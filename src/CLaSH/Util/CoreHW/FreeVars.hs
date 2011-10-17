module CLaSH.Util.CoreHW.FreeVars
  ( module CLaSH.Util.CoreHW.FreeVars
  , module VarSet
  )
where

-- GHC API
import CoreFVs (idFreeVars)
import Type    (tyVarsOfType)
import Var     (isTyVar)
import VarSet

-- Internal Modules
import CLaSH.Util.CoreHW.Syntax

type FreeVars = VarSet

(varFreeVars, termFreeVars, altsFreeVars, valueFreeVars) = mkFreeVars

{-# INLINE mkFreeVars #-}
mkFreeVars ::
  ( Var             -> FreeVars
  , Term            -> FreeVars
  , [(AltCon,Term)] -> FreeVars
  , Value           -> FreeVars
  )
mkFreeVars = (unitVarSet, term, alternatives, value)
  where
    term (Var x)          = unitVarSet x
    term (Value v)        = value v
    term (TyApp e ty)     = typ ty `unionVarSet` term e
    term (App e x)        = term e `extendVarSet` x
    term (Case e ty alts) = typ ty `unionVarSet` term e `unionVarSet` (alternatives alts)
    term (LetRec xes e)   = (unionVarSets (map term es) `unionVarSet` term e `unionVarSet` unionVarSets (map idFreeVars xs)) `delVarSetList` xs
      where
        (xs,es) = unzip xes

    value (TyLambda x e)  = term e `delVarSet` x
    value (Lambda x e)    = nonRecBinderFreeVars x (term e)
    value (Data _ tys xs) = unionVarSets (map typ tys) `unionVarSet` mkVarSet xs
    value (Literal _)     = emptyVarSet

    alternatives = unionVarSets . map alternative
    alternative (altcon, e) = altConFreeVars altcon $ term e

    typ = tyVarsOfType

nonRecBinderFreeVars ::
  Var
  -> FreeVars
  -> FreeVars
nonRecBinderFreeVars x fvs | isTyVar x = fvs `delVarSet` x
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
altConFreeVars (DataAlt _ as xs) = (`delVarSetList` as) . nonRecBindersFreeVars xs
altConFreeVars (LiteralAlt _)    = id
altConFreeVars DefaultAlt        = id
