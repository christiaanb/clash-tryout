{-# LANGUAGE RelaxedLayout #-}
module CLaSH.Normalize.Tools where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Label.PureM as Label
import Language.KURE

import Debug.Trace

-- GHC API
import qualified CoreSubst
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified IdInfo
import qualified MkCore
import qualified Module
import qualified MonadUtils
import qualified Name
import qualified OccName
import qualified Outputable
import qualified SrcLoc
import qualified TcType
import qualified TyCon
import qualified Type
import qualified UniqSupply
import qualified Var
import qualified VarEnv

-- Internal Modules
import CLaSH.Netlist.Constants
import qualified CLaSH.Netlist.Tools as NetlistTools
import CLaSH.Normalize.Traverse
import CLaSH.Normalize.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.GHC
import CLaSH.Util.Pretty

isNormalizable
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession Bool
isNormalizable resultNonRep bndr = do
  let {
    ; bndrTy = Id.idType bndr
    ; (argTys, resTy) = Type.splitFunTys bndrTy
    ; checkTys = if resultNonRep then argTys else resTy:argTys
    } 
  fmap and $ mapM isRepr checkTys

isNormalizableE
  :: Bool
  -> CoreSyn.CoreExpr
  -> NormalizeSession Bool
isNormalizableE resultNonRep bndr = do
  let {
    ; bndrTy = CoreUtils.exprType bndr
    ; (argTys, resTy) = Type.splitFunTys bndrTy
    ; checkTys = if resultNonRep then argTys else resTy:argTys
    } 
  fmap and $ mapM isRepr checkTys

isRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> (liftErrorState nsNetlistState $ NetlistTools.isReprType ty) `Error.catchError` (\_ -> error "DIE!")

assertRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> liftErrorState nsNetlistState $ NetlistTools.assertReprType ty

mkUnique = do
  us <- Label.gets nsUniqSupply
  let (us',us'') = UniqSupply.splitUniqSupply us
  Label.puts nsUniqSupply us'
  return $ UniqSupply.uniqFromSupply us''
    
mkInternalVar
  :: String
  -> Type.Type
  -> NormalizeSession Var.Var
mkInternalVar name ty = do
  uniq <- mkUnique
  let occName = OccName.mkVarOcc (name ++ show uniq)
  let name'   = Name.mkInternalName uniq occName SrcLoc.noSrcSpan
  return $ Var.mkLocalVar IdInfo.VanillaId name' ty IdInfo.vanillaIdInfo

mkExternalName
  :: String
  -> String
  -> Type.Type
  -> NormalizeSession Var.Var
mkExternalName modName funName ty = do
  uniq <- mkUnique
  let extMod  = Module.mkModule (Module.stringToPackageId "clash-0.1") (Module.mkModuleName modName)
  let occName = OccName.mkVarOcc (funName)
  let name'   = Name.mkExternalName uniq extMod occName SrcLoc.noSrcSpan
  let var'    = Var.mkGlobalVar IdInfo.VanillaId name' ty IdInfo.vanillaIdInfo
  return var'

mkDelay
  :: [CoreSyn.CoreExpr]
  -> NormalizeSession Var.Var
mkDelay [initS,clockDomain] = do
  let [stateTy,clockTy] = map CoreUtils.exprType [initS,clockDomain]
  let delayTy           = Type.mkFunTys [stateTy,clockTy,stateTy] stateTy
  delay                 <- mkExternalName "CLaSH.Builtin" "delay" delayTy
  return delay

mkBinderFor 
  :: CoreSyn.CoreExpr 
  -> String 
  -> NormalizeSession Var.Var
mkBinderFor (CoreSyn.Type ty) name = mkTypeVar name (TcType.typeKind ty)
mkBinderFor expr name = mkInternalVar name (CoreUtils.exprType expr)

mkTypeVar 
  :: String 
  -> Type.Kind 
  -> NormalizeSession Var.Var
mkTypeVar name kind = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc (name ++ show uniq)
  let name' = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkTyVar name' kind

cloneVar 
  :: Var.Var 
  -> NormalizeSession Var.Var
cloneVar v = do
  uniq <- mkUnique
  return $ Var.lazySetIdInfo (Var.setVarUnique v uniq) IdInfo.vanillaIdInfo

changed
  :: CoreSyn.CoreExpr
  -> RewriteM NormalizeSession [CoreContext] CoreSyn.CoreExpr
changed expr = do
  liftQ $ Label.modify nsTransformCounter (+1) 
  markM $ return expr

substitute 
  :: CoreSyn.CoreBndr 
  -> CoreSyn.CoreExpr
  -> TransformationStep
substitute find repl context expr = do
  let subst = CoreSubst.extendSubst CoreSubst.emptySubst find repl
  return $ CoreSubst.substExpr (Outputable.text "substitute") subst expr

substituteAndClone 
  :: CoreSyn.CoreBndr 
  -> CoreSyn.CoreExpr
  -> TransformationStep
substituteAndClone find repl context expr = do
    rwRes <- liftQ $ runRewrite ((extractR . topdownR . tryR . promoteR . transformationStep) substituteAndClone') context expr
    expr' <- case rwRes of
      (Right (rwExpr,_,_)) -> return rwExpr
      Left errMsg          -> error $ $(curLoc) ++ "substituteAndClone failed: " ++ errMsg
    return expr'
  where
    substituteAndClone' context expr@(CoreSyn.Var var) | find == var = do
      repl' <- regenUniques context repl
      return repl'
    
    substituteAndClone' context expr = fail "substituteAndClone'"

transformationStep 
  :: TransformationStep 
  -> Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
transformationStep step = rewrite $ \e -> do
  c <- readEnvM
  step c e

regenUniques :: TransformationStep
regenUniques ctx expr = do
  liftQ $ Label.puts nsBndrSubst VarEnv.emptyVarEnv
  res <- liftQ $ runRewrite regenUniques' [] expr
  expr' <- case res of
    Right (expr',_,_) -> return expr'
    Left  errMsg      -> liftQ $ Error.throwError ($(curLoc) ++ "uniqueRegen failed, this should not happen: " ++ errMsg)
  return expr'

regenUniques' :: Rewrite NormalizeSession [CoreContext] CoreSyn.CoreExpr
regenUniques' = (extractR . topdownR . tryR . promoteR . transformationStep) regenUniques''

regenUniques'' :: TransformationStep
regenUniques'' ctx (Var bndr) = do
  subst <- liftQ $ Label.gets nsBndrSubst
  let bndr' = VarEnv.lookupWithDefaultVarEnv subst bndr bndr
  return (Var bndr')

regenUniques'' ctx (Lam bndr res) | Var.isTyVar bndr = fail "regenUniques''"
regenUniques'' ctx (Lam bndr res) = do
  bndr' <- substBndr bndr
  return (Lam bndr' res)

regenUniques'' ctx (Let (NonRec bndr bound) res) = do
  bndr' <- substBndr bndr
  return (Let (NonRec bndr' bound) res)

regenUniques'' ctx (Let (Rec binds) res) = do
  bndrs' <- substBndrs $ map fst binds
  let binds' = zip bndrs' $ map snd binds
  return (Let (Rec binds') res)

regenUniques'' ctx (Case scrut bndr ty alts) = do
  bndr' <- substBndr bndr
  alts' <- mapM doAlt alts
  return (Case scrut bndr' ty alts')
  where
    doAlt (con, bndrs, expr) = do
      bndrs' <- substBndrs bndrs
      return (con, bndrs', expr)

regenUniques'' ctx expr = fail "regenUniques''"

substBndr bndr = liftQ $ do
  subst <- Label.gets nsBndrSubst
  (subst',bndr') <- regenUnique subst bndr
  Label.puts nsBndrSubst subst'
  return bndr'

substBndrs bndrs = liftQ $ do
  subst <- Label.gets nsBndrSubst
  (subst',bndr') <- MonadUtils.mapAccumLM regenUnique subst bndrs
  Label.puts nsBndrSubst subst'
  return bndr'

regenUnique :: VarEnv.VarEnv CoreSyn.CoreBndr -> CoreSyn.CoreBndr -> NormalizeSession (VarEnv.VarEnv CoreSyn.CoreBndr, CoreSyn.CoreBndr)
regenUnique subst bndr = do
  bndr' <- cloneVar bndr
  let subst' = VarEnv.extendVarEnv subst bndr bndr'
  return (subst',bndr')

isLambdaBodyCtx (LambdaBody _) = True
isLambdaBodyCtx _              = False

isLocalVar :: CoreSyn.CoreExpr -> NormalizeSession Bool
isLocalVar (CoreSyn.Var name) = do
  bndrs <- fmap (Map.keys) $ Label.gets nsBindings
  let isDC = Id.isDataConWorkId name
  return $ not isDC && name `notElem` bndrs
isLocalVar _ = return False

-- Create a "selector" case that selects the ith field from dc_ith
-- datacon
mkSelCase :: CoreSyn.CoreExpr -> Int -> Int -> NormalizeSession CoreSyn.CoreExpr
mkSelCase scrut dcI i = do
  case Type.splitTyConApp_maybe scrutTy of
    -- The scrutinee should have a type constructor. We keep the type
    -- arguments around so we can instantiate the field types below
    Just (tycon, tyargs) -> case TyCon.tyConDataCons_maybe tycon of
      -- The scrutinee type should have a single dataconstructor,
      -- otherwise we can't construct a valid selector case.
      Just dcs | dcI < 0 || dcI >= length dcs -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but datacon index is invalid." ++ errorMsg
               | otherwise -> do
        let datacon = (dcs!!dcI)
        let fieldTys = DataCon.dataConInstOrigArgTys datacon tyargs
        if i < 0 || i >= length fieldTys
          then Error.throwError $ $(curLoc) ++ "Creating extractor case, but field index is invalid." ++ errorMsg
          else do
            -- Create a list of wild binders for the fields we don't want
            let wildbndrs = map MkCore.mkWildValBinder fieldTys
            -- Create a single binder for the field we want
            selBndr <- mkInternalVar "sel" (fieldTys!!i)
            -- Create a wild binder for the scrutinee
            let scrutBndr = MkCore.mkWildValBinder scrutTy
            -- Create the case expression
            let binders = take i wildbndrs ++ [selBndr] ++ drop (i+1) wildbndrs
            return $ Case scrut scrutBndr scrutTy [(DataAlt datacon, binders, Var selBndr)]
      Nothing -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but scrutinee has no datacons?" ++ errorMsg
    Nothing -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but scrutinee has no tycon?" ++ errorMsg
  where
    scrutTy = CoreUtils.exprType scrut
    errorMsg = " Extracting element " ++ (show i) ++ " from datacon " ++ (show dcI) ++ " from '" ++ pprString scrut ++ "'" ++ " Type: " ++ (pprString scrutTy)

inlineBind :: String -> (CoreBinding -> NormalizeSession Bool) -> TransformationStep
inlineBind callerId condition context (Let (NonRec bndr val) res) = inlineBind' callerId condition [(bndr,val)] res context
inlineBind callerId condition context (Let (Rec binds) res)       = inlineBind' callerId condition binds        res context
inlineBind callerId condition context expr                        = fail "inlineBind"

inlineBind' :: String -> (CoreBinding -> NormalizeSession Bool) -> [CoreBinding] -> CoreSyn.CoreExpr -> [CoreContext] -> RewriteM NormalizeSession [CoreContext] CoreSyn.CoreExpr
inlineBind' callerId condition binds res context = do
    (replace,others) <- liftQ $ partitionM condition binds
    case (replace,others) of
      ([],_)    -> fail callerId
      otherwise -> do
        newExpr <- doSubstitute replace (Let (Rec others) res)
        changed newExpr
  where
    doSubstitute :: [CoreBinding] -> CoreSyn.CoreExpr -> RewriteM NormalizeSession [CoreContext] CoreSyn.CoreExpr
    doSubstitute [] expr = return expr
    doSubstitute ((bndr,val):reps) expr = do
      -- Perform this substition in the expression
      expr' <- substituteAndClone bndr val context expr
      -- And in the substitution values we will be using next
      reps' <- mapM (subsBind bndr val) reps
      doSubstitute reps' expr'
    
    bndrs = map fst binds
    
    subsBind :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> CoreBinding -> RewriteM NormalizeSession [CoreContext] CoreBinding
    subsBind bndr expr (b,v) = do
      v' <- substituteAndClone bndr expr ((LetBinding bndrs):context) v
      return (b,v')

getGlobalExpr
  :: CoreSyn.CoreBndr
  -> NormalizeSession (Maybe CoreSyn.CoreExpr)
getGlobalExpr = getGlobalAndExtExpr

getGlobalAndExtExpr
  :: CoreSyn.CoreBndr
  -> NormalizeSession (Maybe CoreSyn.CoreExpr)
getGlobalAndExtExpr bndr = do
  case (nameToString $ Var.varName bndr) `elem` builtinIds of
    True -> return Nothing
    False -> do
      bindings <- fmap (Map.lookup bndr) $ Label.gets nsBindings
      case bindings of
        Just a  -> return $ Just a
        Nothing -> if (not $ Var.isLocalVar bndr) 
                    then do
                      exprMaybe <- Error.liftIO $ loadExtExpr (Var.varName bndr) 
                      case exprMaybe of
                        (Just expr) -> do
                          addGlobalBind bndr expr
                          return (Just expr)
                        Nothing     -> return Nothing
                    else return Nothing

getExtExpr
  :: Name.Name
  -> NormalizeSession (Maybe CoreSyn.CoreExpr)
getExtExpr name = do
  exprMaybe <- Error.liftIO $ loadExtExpr name 
  case exprMaybe of
    (Just expr) -> do
      return (Just expr)
    Nothing     -> return Nothing

splitNormalizedNonRep
  :: CoreSyn.CoreExpr
  -> ([CoreSyn.CoreBndr], [CoreBinding], CoreSyn.CoreExpr)
splitNormalizedNonRep expr = (args, binds, resExpr)
  where
    (args, letExpr) = CoreSyn.collectBinders expr
    (binds,resExpr) = flattenLets letExpr

addGlobalBind :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> NormalizeSession ()
addGlobalBind bndr expr = Label.modify nsBindings (Map.insert bndr expr)

mkFunction :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> NormalizeSession CoreSyn.CoreBndr
mkFunction bndr body = do
  let bodyTy = CoreUtils.exprType body
  bodyId <- cloneVar bndr
  let newId = Var.setVarType bodyId bodyTy
  addGlobalBind newId body
  return newId

mkReferenceTo :: Var.Var -> CoreSyn.CoreExpr
mkReferenceTo var | Var.isTyVar var = (CoreSyn.Type $ Type.mkTyVarTy var)
                  | otherwise       = (CoreSyn.Var var)

isArrowBinder ::
	CoreSyn.CoreBndr
	-> Bool
isArrowBinder bndr = res
  where
  	ty = Id.idType bndr
  	res = case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> Name.getOccString (TyCon.tyConName tycon) == "Component"
  		Nothing -> False

isArrowExpression ::
	CoreSyn.CoreExpr
	-> Bool
isArrowExpression expr = res
  where
	  ty = CoreUtils.exprType expr
	  res =	case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> (Name.getOccString (TyCon.tyConName tycon)) == "Component"
  		Nothing -> False
