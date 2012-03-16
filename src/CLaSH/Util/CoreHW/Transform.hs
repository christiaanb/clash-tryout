{-# LANGUAGE TypeOperators #-}
module CLaSH.Util.CoreHW.Transform
  ( substituteType
  , inlineBinders
  , liftBinders
  , substituteExpr
  , regenUniques
  , cloneVar
  , flattenLets
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class        (lift)
import Data.Label                       ((:->))
import qualified Data.Label.PureM    as Label
import qualified Data.Map            as Map
import Language.KURE                    (RewriteM, runRewrite, extractR, bottomupR, tryR, promoteR, liftQ)

-- GHC API
import qualified CoreSubst
import qualified IdInfo
import qualified Type
import qualified Var
import qualified VarEnv
import qualified VarSet

-- Internal Modules
import CLaSH.Util                  (MonadUnique(..), firstM, curLoc, mapAccumLM, partitionM, secondM)
import CLaSH.Util.CoreHW.FreeVars  (termSomeFreeVars)
import CLaSH.Util.CoreHW.Syntax    (Var, TyVar, Term(..), Type, AltCon(..))
import CLaSH.Util.CoreHW.TermSubst (emptySubst,extendTvSubst,substTerm)
import CLaSH.Util.CoreHW.Tools     (tyHasFreeTyVars, varStringUniq, mkLams, mkApps, getTypeFail)
import CLaSH.Util.CoreHW.Traverse  (transformationStep, changed, startContext)
import CLaSH.Util.CoreHW.Types     (TransformSession, TransformStep, CoreContext, CoreBinding)
import CLaSH.Util.Pretty

substituteType ::
  (Monad m)
  => TyVar
  -> Type
  -> TransformStep m
substituteType find repl context expr = do
    let subst = extendTvSubst emptySubst find repl
    return $ substTerm subst expr

inlineBinders ::
  (Functor m, Monad m)
  => String
  -> (CoreBinding -> TransformSession m Bool)
  -> TransformStep m
inlineBinders caller condition context expr@(LetRec binds res) = do
  (replace,others) <- liftQ $ partitionM condition binds
  case replace of
    [] -> fail "inlineBinders"
    _  -> do
      let newExpr = case others of [] -> res ; _ -> LetRec others res
      newExpr' <- liftQ $ substituteBinders replace newExpr
      changed caller expr newExpr'
  where

inlineBinders _ _ _ _ = fail "inlineBinders"

liftBinders ::
  (Functor m, Monad m, State.MonadState s m)
  => String
  -> (CoreBinding -> TransformSession m Bool)
  -> (s :-> Map.Map Var Term)
  -> TransformStep m
liftBinders caller condition globalEnv context expr@(LetRec binds res) = do
  (replace,others) <- liftQ $ partitionM condition binds
  case replace of
    [] -> fail "liftBinders"
    _ -> do
      let newExpr = case others of [] -> res ; _ -> LetRec others res
      replace' <- liftQ $ mapM (liftBinding globalEnv) replace
      newExpr' <- liftQ $ substituteBinders replace' newExpr
      changed caller expr newExpr'

liftBinders _ _ _ _ _ = fail "liftBinders"

substituteBinders ::
  (Functor m, Monad m)
  => [CoreBinding]
  -> Term
  -> TransformSession m Term
substituteBinders [] e = return e
substituteBinders ((bndr,val):rest) e = do
  e'    <- substituteExpr bndr val e
  rest' <- mapM (secondM (substituteExpr bndr val)) rest
  substituteBinders rest' e'

liftBinding ::
  (Functor m, Monad m, State.MonadState s m)
  => (s :-> Map.Map Var Term)
  -> CoreBinding
  -> TransformSession m CoreBinding
liftBinding globalEnv (bndr,expr) = do
  -- Get all the local FVs, excluding 'bndr' from the expression
  localFVs    <- localFreeVars globalEnv [bndr] expr
  -- Abstract expression over its local FVs
  let newBody = mkLams localFVs expr
  -- Make a new global ID
  let bodyTy  = getTypeFail newBody
  newBodyId   <- fmap (flip Var.setVarType $ bodyTy) $ cloneVar bndr
  -- Make a new expression, consisting of the to be lifted function applied to it's free variables
  let newExpr = mkApps (Var newBodyId) (map (\x -> case Var.isTyVar x of True -> Right (Type.mkTyVarTy x); False -> Left (Var x)) localFVs)
  -- Replace all occurrences of 'bndr' by the newly applied expression
  newBody'    <- substituteExpr bndr newExpr newBody
  -- Add the new global binding
  (lift . lift) $ Label.modify globalEnv (Map.insert newBodyId newBody')
  return (bndr, newExpr)

localFreeVars ::
  (Functor m, Monad m, State.MonadState s m)
  => (s :-> Map.Map Var Term)
  -> [Var]
  -> Term
  -> TransformSession m [Var]
localFreeVars globalEnv exclude expr = do
    bndrs               <- fmap (Map.keys) $ (lift . lift) $ Label.gets globalEnv
    let interesting var = Var.isLocalVar var && (var `notElem` (bndrs ++ exclude))
    let freeVars        = VarSet.varSetElems $ termSomeFreeVars interesting expr
    return freeVars

substituteExpr ::
  (Functor m, Monad m)
  => Var
  -> Term
  -> Term
  -> TransformSession m Term
substituteExpr find repl expr = do
    rwRes <- runRewrite ((extractR . bottomupR . tryR . promoteR . transformationStep) substituteExpr') startContext expr
    expr' <- case rwRes of
      (Right (rwExpr,_,_)) -> return rwExpr
      Left errMsg          -> Error.throwError $ $(curLoc) ++ "substituteExpr failed: " ++ errMsg
    return expr'
  where
    substituteExpr' context expr@(Var var) | find == var = do
      repl' <- liftQ $ regenUniques repl
      return repl'
    substituteExpr' context expr = fail "substituteVar'"

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

regenUniques' _ p@(Prim _) = return p

regenUniques' subst (TyLambda tyBndr res) = do
  res' <- regenUniques' subst res
  return (TyLambda tyBndr res')

regenUniques' subst (Lambda bndr res) = do
  (subst',bndr') <- regenUnique subst bndr
  res'  <- regenUniques' subst' res
  return (Lambda bndr' res')

regenUniques' subst d@(Data _) = return d

regenUniques' subst (TyApp e t) = do
  e' <- regenUniques' subst e
  return (TyApp e' t)

regenUniques' subst (App e1 e2) = do
  e1' <- regenUniques' subst e1
  e2' <- regenUniques' subst e2
  return (App e1' e2')

regenUniques' subst (Case scrut ty alts) = do
  scrut' <- regenUniques' subst scrut
  alts'  <- mapM (doAlt subst) alts
  return (Case scrut' ty alts')
  where
    doAlt s (DataAlt dc xs, e) = do
      (s',xs') <- mapAccumLM regenUnique s xs
      e'       <- regenUniques' s' e
      return (DataAlt dc xs', e')
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
