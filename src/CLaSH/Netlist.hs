module CLaSH.Netlist
  ( genNetlist
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import qualified Data.Label as Label
import qualified Data.Label.PureM as LabelM
import qualified Data.List as List
import qualified Data.Map as Map

-- GHC API
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified FastString
import qualified Id
import qualified IdInfo
import qualified Literal
import qualified Name
import qualified Var

-- Internal Modules
import CLaSH.Driver.Types (DriverSession)
import CLaSH.Netlist.Constants
import CLaSH.Netlist.Tools
import CLaSH.Netlist.Types
import CLaSH.Util (curLoc,makeCached)
import CLaSH.Util.Core (CoreBinding, varToString, getValArgs, dataconIndex)
import CLaSH.Util.Pretty (pprString)

genNetlist ::
  NetlistState
  -> [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
  -> CoreSyn.CoreBndr
  -> DriverSession [Module]
genNetlist nlState normalized topEntity = do
  let (retVal, nlState') = State.runState (Error.runErrorT (genModules topEntity)) (nlState { _nlNormalized = Map.fromList normalized })
  case retVal of
    Left errMsg   -> error errMsg
    Right netlist -> return netlist

genModules ::
  CoreSyn.CoreBndr
  -> NetlistSession [Module]
genModules topEntity = do
  topMod <- genModule topEntity
  allMods <- LabelM.gets nlMods
  return $ map snd $ Map.toList allMods

genModule ::
  CoreSyn.CoreBndr
  -> NetlistSession Module
genModule modName = do
  modExprMaybe <- fmap (Map.lookup modName) $ LabelM.gets nlNormalized
  case modExprMaybe of
    Nothing      -> Error.throwError $ $(curLoc) ++ "No normalized expr for bndr: " ++ (show modName)
    Just modExpr -> makeCached modName nlMods $ genModule' modName modExpr
      
genModule' ::
  CoreSyn.CoreBndr
  -> CoreSyn.CoreExpr
  -> NetlistSession Module
genModule' modName modExpr = do
  (args,binds,res)       <- splitNormalized modExpr
  (resType:argTypes)     <- mapM mkHType (res:args)
  let (resName:argNames) = map varToString (res:args)
  (decls,clocks)         <- fmap unzip $ mapM mkConcSm binds
  let modName' = varToString modName
  let modInps  = (zip argNames argTypes) ++ (concat clocks)
  let modOutps = [(resName,resType)]
  let modDecls = concat decls
  return $ Module modName' modInps modOutps modDecls

mkConcSm ::
  CoreBinding
  -> NetlistSession ([Decl],[(Ident,HWType)])
mkConcSm (bndr, Cast expr ty) = mkConcSm (bndr, expr)

mkConcSm (bndr, Var v) = genApplication bndr v []

mkConcSm (bndr, app@(App _ _)) = do
  let (Var f, args) = CoreSyn.collectArgs app
  let valArgs       = getValArgs (Var.varType f) args
  genApplication bndr f valArgs

mkConcSm (bndr, expr@(Case (Var scrut) b ty [alt])) = do
  case alt of
    (DataAlt dc, bndrs, (Var selBndr)) -> do
      nonEmptySel <- hasNonEmptyType selBndr
      if nonEmptySel
        then do
          bndrs' <- Monad.filterM hasNonEmptyType bndrs
          case List.elemIndex selBndr bndrs' of
            Just selI -> do
              hwTypeScrut <- mkHType scrut
              hwTypeBndr  <- mkHType bndr
              if hwTypeScrut == hwTypeBndr 
                then do
                  let selName = varToString scrut
                  let selExpr = ExprVar selName
                  return (mkUncondAssign (bndr,hwTypeBndr) selExpr, [])
                else do
                  case hwTypeScrut of
                    ProductType _ _ -> do
                      let fieldSlice = typeFieldRange hwTypeScrut selI
                      let sliceExpr = mkSliceExpr (varToString scrut) fieldSlice
                      return (mkUncondAssign (bndr,hwTypeBndr) sliceExpr,[])
                    other -> do
                      error $ show hwTypeScrut
            Nothing -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case: result is not one of the bndrs:\n" ++ pprString expr
        else
          return ([],[])
    
    _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case:\n" ++ pprString expr

mkConcSm (bndr, expr@(Case _ _ _ _)) = Error.throwError $ $(curLoc) ++ "Not in normal form: Case statement does not have a simple variable as scrutinee:\n" ++ pprString expr
mkConcSm (bndr, expr) = Error.throwError $ $(curLoc) ++ "Not in normal form: let-bound expr is not a Var, Cast, Case or App:\n" ++ pprString expr  

genApplication ::
  CoreSyn.CoreBndr
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genApplication dst f args = do
  nonEmptyDst <- hasNonEmptyType dst
  if nonEmptyDst
    then do
      if (Var.isGlobalId f)
        then do
          case Var.idDetails f of
            IdInfo.DataConWorkId dc -> do
              dstType <- mkHType dst
              args'   <- Monad.filterM hasNonEmptyType args
              case dstType of
                SumType _ _ -> error "genApp dataConWork SumType"
                -- ProductType 
                ProductType _ argTys -> do
                  args'' <- mapM (\arg -> case arg of (Var v) -> varToExpr v ; _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: constructor with non-Var args: " ++ pprString (dst,f,args)) args'
                  if (length argTys) == (length args'')
                    then return (mkUncondAssign (dst,dstType) (ExprConcat args''),[])
                    else Error.throwError $ $(curLoc) ++ "Not in normal form: underapplied constructor: " ++ pprString (dst,f,args) ++ show argTys  
                SPType _ _ -> error "genApp dataConWork SPType"
                BitType -> simpleAssign dstType
                other -> error $ "genApp dataConWork: " ++ show other
                where
                  simpleAssign dstType = do
                    expr <- dataconToExpr dstType dc
                    return (mkUncondAssign (dst,dstType) expr,[])
            IdInfo.DataConWrapId dc -> do
              error "genApp dataConWrap"
            IdInfo.VanillaId -> do
              case (List.lookup (varToString f) builtinBuilders) of
                Just (argCount, builder) ->
                  if length args == argCount
                    then builder dst args
                    else Error.throwError $ $(curLoc) ++ "Incorrect number of arguments to builtin function: " ++ pprString (dst,f,args)
                Nothing -> do
                  normalized <- isNormalizedBndr f
                  if normalized
                    then do
                      modu@(Module modName modInps [modOutps] _)  <- genModule f
                      let clocks = filter ((== ClockType) . snd) modInps
                      let clocksN = filter ((/= ClockType) . snd) modInps
                      if (length clocks + length args) == (length modInps)
                        then do
                          let dstName = (varToString dst)
                          args' <- mapM (\arg -> case arg of (CoreSyn.Var v) -> varToExpr v; other -> Error.throwError $ $(curLoc) ++ "Not in normal form: arg" ++ pprString arg) args
                          let clocksAssign = map (\(c,_) -> (c,ExprVar c)) clocks
                          let inpsAssign = zip (map fst clocksN) args'
                          let outpAssign  = (fst modOutps, ExprVar dstName)
                          return ([InstDecl modName ("comp_inst_" ++ dstName) [] (clocksAssign ++ inpsAssign) [outpAssign]],clocks)
                        else do
                          Error.throwError $ $(curLoc) ++ "Under applied normalized function: " ++ pprString (dst,f,args) ++ show modu 
                    else do
                      dstType <- mkHType dst
                      Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has type: " ++ show dstType
            IdInfo.ClassOpId cls -> do
              error "genApp classOp"
        else do
          normalized <- isNormalizedBndr f
          if normalized
            then do
              error "genApp local normalized"
            else do
              dstType <- mkHType dst
              f' <- varToExpr f
              return (mkUncondAssign (dst,dstType) f',[])      
    else
      return ([],[])

type BuiltinBuilder =
  CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
  
type BuilderTable = [(String, (Int, BuiltinBuilder))]

builtinBuilders :: BuilderTable
builtinBuilders =
  [ ("xorB" , (2, genBinaryOperator Xor))
  , ("andB" , (2, genBinaryOperator And))
  , ("notB" , (1, genUnaryOperator  Neg))
  , ("delay", (3, genDelay))
  ]
  
genDelay :: BuiltinBuilder
genDelay state [Var initS, clock, Var stateP] = do
  stateTy <- mkHType state
  let [stateName,initSName,statePName] = map varToString [state,initS,stateP]
  let stateDecl  = NetDecl stateName stateTy Nothing
  (clockName,clockEdge) <- parseClock clock
  let resetName  = clockName ++ "Reset"
  let resetEvent = Event (ExprVar resetName) AsyncLow
  let resetStmt  = Assign (ExprVar stateName) (ExprVar initSName)
  let clockEvent = Event (ExprVar clockName) clockEdge
  let clockStmt  = Assign (ExprVar stateName) (ExprVar statePName)
  let register   = ProcessDecl [(resetEvent,resetStmt),(clockEvent,clockStmt)]
  return $ ([stateDecl,register],[(clockName,ClockType),(resetName,ClockType)])

parseClock ::
  CoreSyn.CoreExpr
  -> NetlistSession (Ident,Edge)
parseClock clock = do
  case clock of
    (App _ _) -> do
      let (Var clockTyCon, [clockNameCString,_]) = CoreSyn.collectArgs clock
      let (CoreSyn.Var unpackCString, [Lit (Literal.MachStr clockFS)]) = CoreSyn.collectArgs clockNameCString
      let clockName = FastString.unpackFS clockFS
      case (Name.getOccString clockTyCon) of
        "ClockUp"   -> return (clockName,PosEdge)
        "ClockDown" -> return (clockName,NegEdge)
    _ -> Error.throwError $ $(curLoc) ++ "Don't know how to handle clock: " ++ pprString clock