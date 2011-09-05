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
import qualified Id
import qualified IdInfo
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
  return $ Module (varToString modName) (zip argNames argTypes) [(resName,resType)] (concat decls)

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
                  return ([mkUncondAssign (bndr,hwTypeBndr) selExpr], [])
                else do
                  case hwTypeScrut of
                    ProductType _ _ -> do
                      dcI <- dataconIndex (Id.idType scrut) dc
                      let fieldSlice = typeFieldRange hwTypeScrut dcI
                      let sliceExpr = mkSliceExpr (varToString scrut) fieldSlice
                      return ([mkUncondAssign (bndr,hwTypeBndr) sliceExpr],[])
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
                ProductType _ argTys -> do
                  args'' <- mapM (\arg -> case arg of (Var v) -> varToExpr v ; _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: constructor with non-Var args: " ++ pprString (dst,f,args)) args'
                  if (length argTys) == (length args)
                    then return ([mkUncondAssign (dst,dstType) (ExprConcat args'')],[])
                    else Error.throwError $ $(curLoc) ++ "Not in normal form: underapplied constructor: " ++ pprString (dst,f,args)  
                SPType _ _ -> error "genApp dataConWork SPType"
                other -> error $ "genApp dataConWork: " ++ show other
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
                      modDec <- genModule f
                      error $ show modDec
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
              return ([mkUncondAssign (dst,dstType) f'],[])      
    else
      return ([],[])
