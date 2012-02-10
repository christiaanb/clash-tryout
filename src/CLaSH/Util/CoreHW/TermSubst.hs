{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP           #-}
module CLaSH.Util.CoreHW.TermSubst
  ( emptySubst
  , extendTvSubst
  , substTerm
  )
where

-- External Modules
import Data.List (mapAccumL)

-- GHC API
import qualified CoreSubst
import Id        (maybeModifyIdInfo, idInfo, idName)
import qualified Type
import Var       (isTyVar, isLocalId, setVarType, varType)
#if __GLASGOW_HASKELL__ < 702
import Var       (isTyCoVar)
#endif
import VarEnv    (VarEnv, emptyVarEnv, extendVarEnv, lookupVarEnv, lookupInScope, extendInScopeSet, uniqAway, isEmptyVarEnv, delVarEnv)
import VarSet    (VarSet, emptyVarSet, isEmptyVarSet)

-- Internal Modules
import CLaSH.Util               (curLoc)
import CLaSH.Util.CoreHW.Syntax (Term(..), Var, Type, TyVar, AltCon(..))
import CLaSH.Util.CoreHW.Types  (CoreBinding)
import CLaSH.Util.Pretty

data TermSubst  = TermSubst CoreSubst.InScopeSet IdSubstEnv TvSubstEnv
type IdSubstEnv = VarEnv Var
type TvSubstEnv = VarEnv Type

emptyInScopeSet = CoreSubst.substInScope $ CoreSubst.emptySubst

emptySubst      = TermSubst emptyInScopeSet emptyVarEnv emptyVarEnv

#if __GLASGOW_HASKELL__ < 702
extendTvSubst (TermSubst inScope ids tvs) var ty | isTyCoVar var = TermSubst inScope ids (extendVarEnv tvs var ty)
#else
extendTvSubst (TermSubst inScope ids tvs) var ty | isTyVar var = TermSubst inScope ids (extendVarEnv tvs var ty)
#endif
                                                 | otherwise   = error $ $(curLoc) ++ "extendTvSubst called for non tyvar: " ++ show var

substTerm :: TermSubst -> Term -> Term
substTerm subst expr
  = go expr
  where
    go (Var v)              = Var (lookupIdSubst subst v)
    go (Literal lit)        = Literal lit
    go (Prim x)             = Prim x
    go (Data dc)            = Data dc
    go (App fun arg)        = App (go fun) (go arg)
    go (TyApp fun ty)       = TyApp (go fun) (substTy subst ty)
    go (Lambda bndr body)   = Lambda bndr' (substTerm subst' body)
                            where
                              (subst', bndr') = substBndr subst bndr
    go (TyLambda bndr body) = TyLambda bndr' (substTerm subst' body)
                                 where
                                   (subst', bndr') = substBndr subst bndr
    go (LetRec binds body)  = LetRec binds' (substTerm subst' body)
                            where
                              (subst', binds') = substBinds subst binds
    go (Case scrut ty alts) = Case (go scrut) (substTy subst ty) (map (goAlt subst) alts)
    goAlt subst (DataAlt dc xs, rhs) = (DataAlt dc xs', substTerm subst' rhs)
                                     where
                                       (subst',xs') = substBndrs subst xs
    goAlt subst (con, rhs)           = (con, substTerm subst rhs)

substBinds :: TermSubst -> [CoreBinding] -> (TermSubst, [CoreBinding])
substBinds subst pairs = (subst', bndrs' `zip` rhss')
  where
    (bndrs,rhss)     = unzip pairs
    (subst', bndrs') = substRecBndrs subst bndrs
    rhss'            = map (substTerm subst') rhss

substRecBndrs :: TermSubst -> [Var] -> (TermSubst,[Var])
substRecBndrs subst bndrs
  = (newSubst, newBndrs)
  where
    (newSubst, newBndrs) = mapAccumL (substIdBndr newSubst) subst bndrs

lookupIdSubst :: TermSubst -> Var -> Var
lookupIdSubst (TermSubst inScope ids _) v
  | not (isLocalId v)                  = v
  | Just e  <- lookupVarEnv ids v      = e
  | Just v' <- lookupInScope inScope v = v'
  | otherwise                          = v

substTy :: TermSubst -> Type -> Type
substTy subst ty = Type.substTy (getTvSubst subst) ty

getTvSubst :: TermSubst -> Type.TvSubst
getTvSubst (TermSubst inScope _ tenv) = Type.TvSubst inScope tenv

substBndr :: TermSubst -> Var -> (TermSubst, Var)
substBndr subst bndr
  | isTyVar bndr = substTyVarBndr subst bndr
  | otherwise    = substIdBndr subst subst bndr

substBndrs :: TermSubst -> [Var] -> (TermSubst, [Var])
substBndrs = mapAccumL substBndr

substTyVarBndr :: TermSubst -> TyVar -> (TermSubst, TyVar)
substTyVarBndr (TermSubst inScope idEnv tvEnv) tv
  = case Type.substTyVarBndr (Type.TvSubst inScope tvEnv) tv of
    (Type.TvSubst inScope' tvEnv', tv') ->
      (TermSubst inScope' idEnv tvEnv', tv')

substIdBndr :: TermSubst -> TermSubst -> Var -> (TermSubst, Var)
substIdBndr recSubst subst@(TermSubst inScope env tvs) oldId
  = (TermSubst (inScope `extendInScopeSet` id2) newEnv tvs, id2)
  where
    id1                = uniqAway inScope oldId
    id2 | noTypeChange = id1
        | otherwise    = setVarType id1 (substTy subst oldTy)
    oldTy              = varType oldId
    noTypeChange       = isEmptyVarEnv tvs || isEmptyVarSet (Type.tyVarsOfType oldTy)
    newEnv | noChange  = delVarEnv env oldId
           | otherwise = extendVarEnv env oldId id2
    noChange           = id1 == oldId
