module CLaSH.Netlist
  ( genNetlist
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import qualified Data.Label as Label
import qualified Data.Label.PureM as LabelM
import qualified Data.List as List
import qualified Data.Map as Map

import Debug.Trace

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
import CLaSH.Util.Core (CoreBinding, varToStringUniq, varToString, getValArgs, dataconIndex, getIntegerLiteral, dataconsFor, isVar)
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
  let (resName:argNames) = map varToStringUniq (res:args)
  modCnt <- LabelM.gets nlModCnt
  LabelM.modify nlModCnt (+1)
  let modName' = ((++ (show modCnt)) . (\v -> if null v then (v ++ "Component_") else (v ++ "_")) . mkVHDLBasicId . varToString) modName
  (decls,clocks)         <- fmap unzip $ mapM mkConcSm binds
  let modInps  = (zip argNames argTypes) ++ (List.nub $ concat clocks)
  let modOutps = [(resName,resType)]
  let modDecls = concat decls
  return $ Module modName' modInps modOutps modDecls

mkConcSm ::
  CoreBinding
  -> NetlistSession ([Decl],[(Ident,HWType)])
mkConcSm (bndr, Cast expr ty) = mkConcSm (bndr, expr)

mkConcSm (bndr, Var v) = genApplication bndr v []

mkConcSm (bndr, app@(App _ _)) | isVar (varf) = do
  let (_, args) = CoreSyn.collectArgs app
  let valArgs       = getValArgs (Var.varType f) args
  genApplication bndr f valArgs
  where
    (varf,args) = CoreSyn.collectArgs app
    (Var f)     = varf

mkConcSm (bndr, app@(App _ _)) = do
  Error.throwError $ $(curLoc) ++ "Not in normal form: application of a non-Var:\n" ++ pprString app

mkConcSm (bndr, expr@(Case (Var scrut) b ty [alt])) = do
  let comment = genComment bndr (pprString expr) ([]::[CoreSyn.CoreExpr])
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
                  let selName = varToStringUniq scrut
                  let selExpr = ExprVar selName
                  return (comment:(mkUncondAssign (bndr,hwTypeBndr) selExpr), [])
                else do
                  case hwTypeScrut of
                    ProductType _ _ -> do
                      let fieldSlice = typeFieldRange hwTypeScrut selI
                      let sliceExpr = mkSliceExpr (varToStringUniq scrut) fieldSlice
                      return (comment:(mkUncondAssign (bndr,hwTypeBndr) sliceExpr),[])
                    other -> do
                      error $ show hwTypeScrut
            Nothing -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case: result is not one of the bndrs:\n" ++ pprString expr
        else
          return ([],[])
    
    _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case:\n" ++ pprString expr

mkConcSm (bndr, expr@(Case (Var scrut) _ _ alts)) = do
  let comment = genComment bndr (pprString expr) ([]::[CoreSyn.CoreExpr])
  scrutHWType <- mkHType scrut
  bndrType    <- mkHType bndr
  scrutExpr   <- varToExpr scrut
  (enums, cmp) <- case scrutHWType of
    SumType _ enums -> do
      return (map (ExprLit (Just $ htypeSize scrutHWType) . ExprNum . toInteger) [0..(length enums)-1], scrutExpr)
    BitType -> do
      return (map (ExprLit Nothing . ExprBit) [H,L], scrutExpr)
    BoolType -> do
      return (map (ExprLit Nothing . ExprBit) [L,H], scrutExpr)
    other -> error $ "mkConcSm (bndr, expr@(Case (Var scrut) _ _ alts)) " ++ show scrutHWType
  altcons <- mapM (\(DataAlt dc, _, _) -> fmap (enums!!) $ dataconIndex scrut dc) $ tail alts
  (defaultExpr:otherExprs) <- mapM (varToExpr . (\(_,_,Var v) -> v)) alts
  let caseExpr = ExprCase cmp (zip (map (:[]) altcons) otherExprs) (Just defaultExpr)
  return (comment:(mkUncondAssign (bndr,bndrType) caseExpr),[])

mkConcSm (bndr, expr@(Case _ _ _ _)) = Error.throwError $ $(curLoc) ++ "Not in normal form: Case statement does not have a simple variable as scrutinee:\n" ++ pprString expr
mkConcSm (bndr, expr) = Error.throwError $ $(curLoc) ++ "Not in normal form: let-bound expr is not a Var, Cast, Case or App:\n" ++ pprString expr  

genApplication ::
  CoreSyn.CoreBndr
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genApplication dst f args = do
  nonEmptyDst <- hasNonEmptyType dst
  dstType <- mkHType dst
  if nonEmptyDst
    then do
      if (Var.isGlobalId f)
        then do
          case Var.idDetails f of
            IdInfo.DataConWorkId dc -> do
              args'   <- Monad.filterM hasNonEmptyType args
              dcs   <- dataconsFor dst
              case (dcs,args') of
                ([dc],[arg]) -> do
                  let comment = genComment dst (pprString f) args
                  argExpr <- argToExpr arg
                  return (comment:(mkUncondAssign (dst,dstType) argExpr),[])
                others -> do
                  case dstType of
                    SumType _ _ -> error "genApp dataConWork SumType"
                    ProductType _ argTys -> do
                      argTys' <- mapM mkHType args'
                      let comment = genComment dst (pprString f) args
                      args'' <- mapM (\arg -> case arg of (Var v) -> varToExpr v ; _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: constructor with non-Var args: " ++ pprString (dst,f,args)) args'
                      if [dstType] == argTys'
                        then return (comment:(mkUncondAssign (dst,dstType) (head args'')),[])
                        else do
                          case (compare (length argTys) (length args'')) of
                            EQ -> do
                              let comment = genComment dst (pprString f) args
                              return (comment:(mkUncondAssign (dst,dstType) (ExprConcat args'')),[])
                            LT -> Error.throwError $ $(curLoc) ++ "Not in normal form: overapplied constructor: " ++ pprString (dst,f,args) ++ show argTys  
                            GT -> Error.throwError $ $(curLoc) ++ "Not in normal form: underapplied constructor: " ++ pprString (dst,f,args') ++ show argTys
                    SPType _ _ -> error "genApp dataConWork SPType"
                    BitType -> simpleAssign dstType args'
                    other -> error $ "genApp dataConWork: " ++ show other
                    where
                      simpleAssign dstType [] = do
                        expr <- dataconToExpr dstType dc
                        let comment = genComment dst (pprString f) ([]::[CoreSyn.CoreExpr])
                        return ((comment:mkUncondAssign (dst,dstType) expr),[])
                      simpleAssign dstType [Var v] = do
                        expr <- varToExpr v
                        let comment = genComment dst "" [Var v]
                        return ((comment:mkUncondAssign (dst,dstType) expr),[])
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
                          let dstName = (varToStringUniq dst)
                          args' <- mapM (\arg -> case arg of (CoreSyn.Var v) -> varToExpr v; other -> Error.throwError $ $(curLoc) ++ "Not in normal form: arg" ++ pprString arg) args
                          let clocksAssign = map (\(c,_) -> (c,ExprVar c)) clocks
                          let inpsAssign = zip (map fst clocksN) args'
                          let outpAssign  = (fst modOutps, ExprVar dstName)
                          let comment = genComment dst (pprString f) args
                          return ([comment,InstDecl modName ("comp_inst_" ++ dstName) [] (clocksAssign ++ inpsAssign) [outpAssign]],clocks)
                        else do
                          Error.throwError $ $(curLoc) ++ "Under applied normalized function: " ++ pprString (dst,f,args) ++ show modu 
                    else do
                      Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has type: " ++ show dstType
            IdInfo.ClassOpId cls -> do
              case (List.lookup (varToString f) builtinBuilders) of
                Just (argCount, builder) ->
                  if length args == argCount
                    then builder dst args
                    else Error.throwError $ $(curLoc) ++ "Incorrect number of arguments to builtin function: " ++ pprString (dst,f,args)
                Nothing -> do
                  Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has type: " ++ show dstType
        else do
          normalized <- isNormalizedBndr f
          if normalized
            then do
              -- error "genApp local normalized"
              modu@(Module modName modInps [modOutps] _)  <- genModule f
              let clocks = filter ((== ClockType) . snd) modInps
              let clocksN = filter ((/= ClockType) . snd) modInps
              if (length clocks + length args) == (length modInps)
                then do
                  let dstName = (varToStringUniq dst)
                  args' <- mapM (\arg -> case arg of (CoreSyn.Var v) -> varToExpr v; other -> Error.throwError $ $(curLoc) ++ "Not in normal form: arg" ++ pprString arg) args
                  let clocksAssign = map (\(c,_) -> (c,ExprVar c)) clocks
                  let inpsAssign = zip (map fst clocksN) args'
                  let outpAssign  = (fst modOutps, ExprVar dstName)
                  let comment = genComment dst (pprString f) args
                  return ([comment,InstDecl modName ("comp_inst_" ++ dstName) [] (clocksAssign ++ inpsAssign) [outpAssign]],clocks)
                else do
                  Error.throwError $ $(curLoc) ++ "Under applied normalized function: " ++ pprString (dst,f,args) ++ show modu
            else do
              f' <- varToExpr f
              let comment = genComment dst (pprString f) ([] :: [CoreSyn.CoreExpr])
              return (comment:(mkUncondAssign (dst,dstType) f'),[])      
    else
      return ([],[])

type BuiltinBuilder =
  CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
  
type BuilderTable = [(String, (Int, BuiltinBuilder))]

builtinBuilders :: BuilderTable
builtinBuilders =
  [ ("xorB" , (2, genBinaryOperator "xorB" Xor))
  , ("andB" , (2, genBinaryOperator "andB" And))
  , ("orB"  , (2, genBinaryOperator "orB" Or ))
  , ("notB" , (1, genUnaryOperator  "notB" LNeg))
  , ("delay", (3, genDelay))
  , ("+"    , (2, genBinaryOperatorSLV "(+)" Plus))
  , ("-"    , (2, genBinaryOperatorSLV "(-)" Minus))
  , ("fromInteger", (1, genFromInteger))
  , ("+>>"  , (2, genShiftIntoL))
  , ("vlast", (1, genVLast))
  , ("singleton", (1, genSingleton))
  ]
  
genDelay :: BuiltinBuilder
genDelay state args@[Var initS, clock, Var stateP] = do
  stateTy <- mkHType state
  let [stateName,initSName,statePName] = map varToStringUniq [state,initS,stateP]
  let stateDecl  = NetDecl stateName stateTy Nothing
  (clockName,clockEdge) <- parseClock clock
  let resetName  = clockName ++ "Reset"
  let resetEvent = Event (ExprVar resetName) AsyncLow
  let resetStmt  = Assign (ExprVar stateName) (ExprVar initSName)
  let clockEvent = Event (ExprVar clockName) clockEdge
  let clockStmt  = Assign (ExprVar stateName) (ExprVar statePName)
  let register   = ProcessDecl [(resetEvent,resetStmt),(clockEvent,clockStmt)]
  let comment    = genComment state "delay" args
  return $ ([stateDecl,comment,register],[(clockName,ClockType),(resetName,ClockType)])

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
    
genFromInteger :: BuiltinBuilder
genFromInteger dst [arg] = do
  lit <- getIntegerLiteral nlTfpSyn arg
  dstType <- mkHType dst
  let litExpr = mkUncondAssign (dst,dstType) (ExprLit (Just $ htypeSize dstType) $ ExprNum lit)
  let comment = genComment dst "fromInteger" [arg]
  return (comment:litExpr,[])

genShiftIntoL :: BuiltinBuilder
genShiftIntoL dst [Var elArg,Var vecArg] = do
  dstType@(VecType len etype) <- mkHType vecArg
  let [elName,vecName] = map varToStringUniq [elArg,vecArg]
  let assignExpr = mkUncondAssign (dst,dstType) (ExprConcat [ExprVar elName, ExprSlice vecName (ExprLit Nothing $ ExprNum ((toInteger len) - 1)) (ExprLit Nothing $ ExprNum 1)])
  let comment = genComment dst "(+>>)" [Var elArg, Var vecArg]
  return (comment:assignExpr,[]) 

genVLast :: BuiltinBuilder
genVLast dst [Var vecArg] = do
  dstType <- mkHType dst
  let vecName = varToStringUniq vecArg
  let selExpr = mkUncondAssign (dst,dstType) (ExprIndex vecName (ExprLit Nothing $ ExprNum 0))
  let comment = genComment dst "vlast" [Var vecArg]
  return (comment:selExpr,[])

genSingleton :: BuiltinBuilder
genSingleton dst [Var eArg] = do
  dstType <- mkHType dst
  let eName = varToStringUniq eArg
  let assignExpr = mkUncondAssign (dst,dstType) (ExprConcat [ExprVar eName, ExprVar "\"\""])
  let comment = genComment dst "singleton" [Var eArg]
  return (comment:assignExpr,[])

  