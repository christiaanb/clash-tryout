module CLaSH.Util.CoreHW.Transform
  ( substituteType
  , substituteVar
  , regenUniques
  , cloneVar
  , flattenLets
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Label.PureM    as Label
import Language.KURE                    (RewriteM, runRewrite, extractR, bottomupR, tryR, promoteR, liftQ)

-- GHC API
import qualified CoreSubst
import qualified IdInfo
import qualified Type
import qualified Var
import qualified VarEnv

-- Internal Modules
import CLaSH.Util               (MonadUnique(..), firstM, curLoc, mapAccumLM)
import CLaSH.Util.CoreHW.Syntax (Var, TyVar, Term(..), Type, AltCon(..))
import CLaSH.Util.CoreHW.TermSubst (emptySubst,extendTvSubst,substTerm)
import CLaSH.Util.CoreHW.Tools (tyHasFreeTyVars)
import CLaSH.Util.CoreHW.Traverse (transformationStep)
import CLaSH.Util.CoreHW.Types  (TransformSession, TransformStep, CoreContext, CoreBinding)
import CLaSH.Util.Pretty

substituteType ::
  (Monad m)
  => TyVar
  -> Type
  -> TransformStep m
substituteType find repl context expr = do
    let subst = extendTvSubst emptySubst find repl
    return $ substTerm subst expr

substituteVar ::
  (Monad m)
  => Var
  -> Var
  -> TransformStep m
substituteVar find repl context expr = do
    rwRes <- liftQ $ runRewrite ((extractR . bottomupR . tryR . promoteR . transformationStep) substituteVar') context expr
    expr' <- case rwRes of
      (Right (rwExpr,_,_)) -> return rwExpr
      Left errMsg          -> liftQ $ Error.throwError $ $(curLoc) ++ "substituteVar failed: " ++ errMsg
    return expr'
  where
    substituteVar' context expr@(Var var)   | find == var = return (Var repl)
    substituteVar' context expr@(App e var) | find == var = return (App e repl)
    substituteVar' context expr = fail "substituteVar'"

regenUniques ::
  (Functor m, Monad m)
  => Term
  -> TransformSession m Term
regenUniques = regenUniques' VarEnv.emptyVarEnv

regenUniques' ::
  (Functor m, Monad m)
  => VarEnv.VarEnv Var
  -> Term
  -> TransformSession m Term
regenUniques' subst (Var bndr) = do
  let bndr' = VarEnv.lookupWithDefaultVarEnv subst bndr bndr
  return (Var bndr')

regenUniques' _ l@(Literal _) = return l

regenUniques' subst (TyLambda tyBndr res) = do
  res' <- regenUniques' subst res
  return (TyLambda tyBndr res')

regenUniques' subst (Lambda bndr res) = do
  (subst',bndr') <- regenUnique subst bndr
  res'  <- regenUniques' subst' res
  return (Lambda bndr' res')

regenUniques' subst (Data dc as xs) = do
  let xs' = map (\x -> VarEnv.lookupWithDefaultVarEnv subst x x) xs
  return (Data dc as xs')

regenUniques' subst (TyApp e t) = do
  e' <- regenUniques' subst e
  return (TyApp e' t)

regenUniques' subst (App e var) = do
  let var' = VarEnv.lookupWithDefaultVarEnv subst var var
  e' <- regenUniques' subst e
  return (App e' var')

regenUniques' subst (Case scrut ty alts) = do
  scrut' <- regenUniques' subst scrut
  alts'  <- mapM (doAlt subst) alts
  return (Case scrut' ty alts')
  where
    doAlt s (DataAlt dc as xs, e) = do
      (s',xs') <- mapAccumLM regenUnique s xs
      e'       <- regenUniques' s' e
      return (DataAlt dc as xs', e')
    doAlt s (alt, e) = fmap ((,) alt) $ regenUniques' s e

regenUniques' subst (LetRec binds res) = do
  let (bndrs,exprs) = unzip binds
  (subst',bndrs')   <- mapAccumLM regenUnique subst bndrs
  exprs'            <- mapM (regenUniques' subst') exprs
  res'              <- regenUniques' subst' res
  return (LetRec (zip bndrs' exprs') res')

regenUnique ::
  Monad m
  => VarEnv.VarEnv Var
  -> Var
  -> TransformSession m (VarEnv.VarEnv Var, Var)
regenUnique subst bndr = do
  bndr' <- cloneVar bndr
  let subst' = VarEnv.extendVarEnv subst bndr bndr'
  return (subst', bndr')

cloneVar ::
  Monad m
  => Var
  -> TransformSession m Var
cloneVar v = do
  uniq <- getUniqueM
  return $ Var.setVarUnique v uniq

flattenLets ::
  Term
  -> ([CoreBinding], Term)
flattenLets (LetRec binds expr) = (bindings ++ binds, expr')
  where
    (bindings,expr') = flattenLets expr
flattenLets expr = ([],expr)
