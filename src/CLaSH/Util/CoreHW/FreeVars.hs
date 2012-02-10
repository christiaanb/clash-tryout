{-# LANGUAGE CPP #-}
module CLaSH.Util.CoreHW.FreeVars
  ( module CLaSH.Util.CoreHW.FreeVars
  , module VarSet
  )
where

-- GHC API
import CoreFVs (idFreeVars)
import Type    (tyVarsOfType)
#if __GLASGOW_HASKELL__ >= 702
import Var     (isTyVar)
#else
import Var     (isTyCoVar)
#endif
import VarSet

-- Internal Modules
import CLaSH.Util.CoreHW.Syntax

type FreeVars = VarSet

termSomeFreeVars ::
  (Var -> Bool)
  -> Term
  -> FreeVars
termSomeFreeVars f = filterVarSet f . termFreeVars

(varFreeVars, termFreeVars, altsFreeVars) = mkFreeVars

{-# INLINE mkFreeVars #-}
mkFreeVars ::
  ( Var             -> FreeVars
  , Term            -> FreeVars
  , [(AltCon,Term)] -> FreeVars
  )
mkFreeVars = (unitVarSet, term, alternatives)
  where
    term (Var x)          = unitVarSet x
    term (TyApp e ty)     = typ ty `unionVarSet` term e
    term (App e1 e2)      = term e1 `unionVarSet` term e2
    term (Case e ty alts) = typ ty `unionVarSet` term e `unionVarSet`  (alternatives alts)
    term (LetRec xes e)   = (unionVarSets (map term es) `unionVarSet` term e `unionVarSet` unionVarSets (map idFreeVars xs)) `delVarSetList` xs
      where
        (xs,es) = unzip xes

    term (TyLambda x e)  = term e `delVarSet` x
    term (Lambda x e)    = nonRecBinderFreeVars x (term e)
    term (Data _)        = emptyVarSet
    term (Literal _)     = emptyVarSet
    term (Prim _)        = emptyVarSet

    alternatives = unionVarSets . map alternative
    alternative (altcon, e) = altConFreeVars altcon $ term e

    typ = tyVarsOfType

nonRecBinderFreeVars ::
  Var
  -> FreeVars
  -> FreeVars
#if __GLASGOW_HASKELL__ >= 702
nonRecBinderFreeVars x fvs | isTyVar x = fvs `delVarSet` x
#else
nonRecBinderFreeVars x fvs | isTyCoVar x = fvs `delVarSet` x
#endif
                           | otherwise = (fvs `delVarSet` x) `unionVarSet` idFreeVars x

nonRecBindersFreeVars ::
  [Var]
  -> FreeVars
  -> FreeVars
nonRecBindersFreeVars xs = flip (foldr nonRecBinderFreeVars) xs

altConFreeVars ::
  AltCon
  -> FreeVars
  -> FreeVars
altConFreeVars (DataAlt _ xs) = nonRecBindersFreeVars xs
altConFreeVars (LiteralAlt _) = id
altConFreeVars DefaultAlt     = id
