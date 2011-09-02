{-# LANGUAGE FlexibleContexts #-}
module CLaSH.Util.Core.Transform
  ( changed
  , cloneVar
  , inlineBind
  , mkInternalVar
  , mkExternalVar
  , mkTypeVar
  , mkUnique
  , regenUniques
  , substitute
  , substituteAndClone
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Label.PureM as Label
import Language.KURE (RewriteM, markM, runRewrite, extractR, bottomupR, tryR,
  promoteR, Rewrite, topdownR, liftQ)

-- GHC API
import qualified CoreSubst
import CoreSyn (Expr(..),Bind(..))
import qualified CoreSyn
import qualified IdInfo
import qualified Module
import qualified MonadUtils
import qualified Name
import qualified OccName
import qualified Outputable
import qualified SrcLoc
import qualified Type
import qualified Unique
import qualified UniqSupply
import qualified Var
import qualified VarEnv

-- Internal Modules
import CLaSH.Util (curLoc, partitionM)
import CLaSH.Util.Core.Traverse
import CLaSH.Util.Core.Types

changed ::
  (Monad m)
  => String
  -> CoreSyn.CoreExpr
  -> RewriteM (TransformSession m) [CoreContext] CoreSyn.CoreExpr
changed tId expr = do
  liftQ $ Label.modify tsTransformCounter (+1) 
  markM $ return expr

inlineBind :: 
  (Monad m) 
  => String 
  -> (CoreBinding -> (TransformSession m) Bool) 
  -> TransformStep m
inlineBind callerId condition context (Let (NonRec bndr val) res) = inlineBind' callerId condition [(bndr,val)] res context
inlineBind callerId condition context (Let (Rec binds) res)       = inlineBind' callerId condition binds        res context
inlineBind callerId condition context expr                        = fail "inlineBind"

inlineBind' :: 
  (Monad m) 
  => String 
  -> (CoreBinding -> (TransformSession m) Bool) 
  -> [CoreBinding] 
  -> CoreSyn.CoreExpr 
  -> [CoreContext] 
  -> RewriteM (TransformSession m) [CoreContext] CoreSyn.CoreExpr
inlineBind' callerId condition binds res context = do
    (replace,others) <- liftQ $ partitionM condition binds
    case (replace,others) of
      ([],_)    -> fail callerId
      otherwise -> do
        newExpr <- doSubstitute replace (Let (Rec others) res)
        changed callerId newExpr
  where
    doSubstitute :: 
      (Monad m)
      => [CoreBinding]
      -> CoreSyn.CoreExpr
      -> RewriteM (TransformSession m) [CoreContext] CoreSyn.CoreExpr
    doSubstitute [] expr = return expr
    doSubstitute ((bndr,val):reps) expr = do
      -- Perform this substition in the expression
      expr' <- substituteAndClone bndr val context expr
      -- And in the substitution values we will be using next
      reps' <- mapM (subsBind bndr val) reps
      doSubstitute reps' expr'
    
    bndrs = map fst binds
    
    subsBind ::
      (Monad m)
      => CoreSyn.CoreBndr
      -> CoreSyn.CoreExpr
      -> CoreBinding
      -> RewriteM (TransformSession m) [CoreContext] CoreBinding
    subsBind bndr expr (b,v) = do
      v' <- substituteAndClone bndr expr ((LetBinding bndrs):context) v
      return (b,v')

substitute ::
  (Monad m)
  => CoreSyn.CoreBndr 
  -> CoreSyn.CoreExpr
  -> TransformStep m
substitute find repl context expr = do
  let subst = CoreSubst.extendSubst CoreSubst.emptySubst find repl
  return $ CoreSubst.substExpr (Outputable.text "substitute") subst expr
      
substituteAndClone ::
  (Monad m)
  => CoreSyn.CoreBndr 
  -> CoreSyn.CoreExpr
  -> TransformStep m
substituteAndClone find repl context expr = do
    rwRes <- liftQ $ runRewrite ((extractR . bottomupR . tryR . promoteR . transformationStep) substituteAndClone') context expr
    expr' <- case rwRes of
      (Right (rwExpr,_,_)) -> return rwExpr
      Left errMsg          -> liftQ $ Error.throwError $ $(curLoc) ++ "substituteAndClone failed: " ++ errMsg
    return expr'
  where
    substituteAndClone' context expr@(CoreSyn.Var var) | find == var = do
      repl' <- regenUniques context repl
      return repl'
    
    substituteAndClone' context expr = fail "substituteAndClone'"

regenUniques :: 
  (Monad m)
  => TransformStep m
regenUniques ctx expr = do
  liftQ $ Label.puts tsBndrSubst VarEnv.emptyVarEnv
  res <- liftQ $ runRewrite regenUniquesStrat [] expr
  expr' <- case res of
    Right (expr',_,_) -> return expr'
    Left  errMsg      -> liftQ $ Error.throwError ($(curLoc) ++ "uniqueRegen failed, this should not happen: " ++ errMsg)
  return expr'

regenUniquesStrat :: 
  (Monad m)
  => Rewrite (TransformSession m) [CoreContext] CoreSyn.CoreExpr
regenUniquesStrat = (extractR . topdownR . tryR . promoteR . transformationStep) regenUniques'

regenUniques' :: 
  (Monad m)
  => TransformStep m
regenUniques' ctx (Var bndr) = do
  subst <- liftQ $ Label.gets tsBndrSubst
  let bndr' = VarEnv.lookupWithDefaultVarEnv subst bndr bndr
  return (Var bndr')

regenUniques' ctx (Lam bndr res) | Var.isTyVar bndr = fail "regenUniques''"
regenUniques' ctx (Lam bndr res) = do
  bndr' <- substBndr bndr
  return (Lam bndr' res)

regenUniques' ctx (Let (NonRec bndr bound) res) = do
  bndr' <- substBndr bndr
  return (Let (NonRec bndr' bound) res)

regenUniques' ctx (Let (Rec binds) res) = do
  bndrs' <- substBndrs $ map fst binds
  let binds' = zip bndrs' $ map snd binds
  return (Let (Rec binds') res)

regenUniques' ctx (Case scrut bndr ty alts) = do
  bndr' <- substBndr bndr
  alts' <- mapM doAlt alts
  return (Case scrut bndr' ty alts')
  where
    doAlt (con, bndrs, expr) = do
      bndrs' <- substBndrs bndrs
      return (con, bndrs', expr)

regenUniques' ctx expr = fail "regenUniques''"

substBndr ::
  (Monad m)
  => CoreSyn.CoreBndr
  -> RewriteM (TransformSession m) [CoreContext] CoreSyn.CoreBndr
substBndr bndr = liftQ $ do
  subst <- Label.gets tsBndrSubst
  (subst',bndr') <- regenUnique subst bndr
  Label.puts tsBndrSubst subst'
  return bndr'

substBndrs ::
  (Monad m)
  => [CoreSyn.CoreBndr]
  -> RewriteM (TransformSession m) [CoreContext] [CoreSyn.CoreBndr]
substBndrs bndrs = liftQ $ do
  subst <- Label.gets tsBndrSubst
  (subst',bndr') <- MonadUtils.mapAccumLM regenUnique subst bndrs
  Label.puts tsBndrSubst subst'
  return bndr'

regenUnique :: 
  (Monad m)
  => VarEnv.VarEnv CoreSyn.CoreBndr 
  -> CoreSyn.CoreBndr 
  -> (TransformSession m) (VarEnv.VarEnv CoreSyn.CoreBndr, CoreSyn.CoreBndr)
regenUnique subst bndr = do
  bndr' <- cloneVar bndr
  let subst' = VarEnv.extendVarEnv subst bndr bndr'
  return (subst',bndr')

cloneVar ::
  (Monad m)
  => Var.Var 
  -> (TransformSession m) Var.Var
cloneVar v = do
  uniq <- mkUnique
  return $ Var.lazySetIdInfo (Var.setVarUnique v uniq) IdInfo.vanillaIdInfo

mkUnique ::
  (Monad m)
  => (TransformSession m) Unique.Unique
mkUnique = do
  us <- Label.gets tsUniqSupply
  let (us',us'') = UniqSupply.splitUniqSupply us
  Label.puts tsUniqSupply us'
  return $ UniqSupply.uniqFromSupply us''

mkInternalVar ::
  (Monad m)
  => String
  -> Type.Type
  -> (TransformSession m) Var.Var
mkInternalVar name ty = do
  uniq <- mkUnique
  let occName = OccName.mkVarOcc (name ++ show uniq)
  let name'   = Name.mkInternalName uniq occName SrcLoc.noSrcSpan
  return $ Var.mkLocalVar IdInfo.VanillaId name' ty IdInfo.vanillaIdInfo

mkExternalVar ::
  (Monad m)
  => String
  -> String
  -> Type.Type
  -> (TransformSession m) Var.Var
mkExternalVar modName funName ty = do
  uniq <- mkUnique
  let extMod  = Module.mkModule (Module.stringToPackageId "clash-0.1") (Module.mkModuleName modName)
  let occName = OccName.mkVarOcc funName
  let name'   = Name.mkExternalName uniq extMod occName SrcLoc.noSrcSpan
  let var'    = Var.mkGlobalVar IdInfo.VanillaId name' ty IdInfo.vanillaIdInfo
  return var'

mkTypeVar ::
  (Monad m)
  => String 
  -> Type.Kind 
  -> (TransformSession m) Var.Var
mkTypeVar name kind = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc (name ++ show uniq)
  let name' = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkTyVar name' kind
