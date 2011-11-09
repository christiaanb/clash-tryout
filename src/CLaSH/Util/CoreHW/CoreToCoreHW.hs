{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
module CLaSH.Util.CoreHW.CoreToCoreHW
  ( coreExprToTerm
  )
where

-- External Modules
import Control.Monad (join, liftM, liftM2)

-- GHC API
import CoreFVs    (exprSomeFreeVars)
import CoreSyn    (CoreExpr, Expr(..), Unfolding(..), Bind(..), AltCon(..))
import CoreUnfold (exprIsConApp_maybe)
import Coercion   (isCoVar)
import DataCon    (DataCon,dataConName,dataConTyCon)
import FastString (mkFastString)
import Id         (mkSysLocalM,isDataConWorkId_maybe)
import TyCon      (isNewTyCon)
import Var        (Var,isTyVar)
import VarSet     (isEmptyVarSet)

-- Internal Modules
import CLaSH.Util
import qualified CLaSH.Util.CoreHW.Constants as S
import qualified CLaSH.Util.CoreHW.Syntax as S
import qualified CLaSH.Util.CoreHW.Tools  as S
import CLaSH.Util.Pretty

conAppToTerm ::
  DataCon
  -> [CoreExpr]
  -> S.Term
conAppToTerm dc es
  | isNewTyCon (dataConTyCon dc)
  = error ("newtype not supported: " ++ pprString dc ++ " " ++ pprString es)
  | otherwise
  = let valEs' = map coreExprToTerm valEs
    in foldl S.App (foldl S.TyApp (S.Data dc) tys') valEs'
  where
    (tys', valEs) = takeWhileJust fromType_maybe es

    fromType_maybe (Type ty) = Just ty
    fromType_maybe _         = Nothing

coreExprToTerm ::
  CoreExpr
  -> S.Term
coreExprToTerm = term
  where
    term e | Just (dc, univTys, es) <- exprIsConApp_maybe (const NoUnfolding) e
           = conAppToTerm dc (map Type univTys ++ es)
    term (Var x)                 = case (isDataConWorkId_maybe x) of
                                    Just dc | isNewTyCon (dataConTyCon dc) -> error $ "newtype not supported: " ++ pprString dc
                                            | otherwise                    -> S.Data dc
                                    Nothing -> case (S.varString x `elem` S.builtinIds) of
                                      True -> S.Prim x
                                      False -> S.Var x

    term (Lit l)                 = S.Literal l
    term (App eFun (Type tyArg)) = S.TyApp (term eFun) tyArg
    term (App eFun eArg)         = S.App (term eFun) (term eArg)
    term (Lam x e) | isTyVar x   = S.TyLambda x (term e)
                   | otherwise   = S.Lambda x (term e)
    term (Let (NonRec x e1) e2)  = S.LetRec [(x, term e1)] (term e2)
    term (Let (Rec xes) e)       = S.LetRec (map (second term) xes) (term e)
    term (Case e b ty alts)      = S.Case (term e) ty (map (alt b) alts)
    term (Cast e co)             = error $ "cast not supported: " ++ pprString (e,co)
    term (Note _ e)              = term e
    term (Type ty)               = error $ "Type at non-argument position not supported: " ++ pprString ty
    term (Coercion co)           = error $ "coercion not supported" ++ pprString co

    alt _ (DEFAULT   , [], e)    = (S.DefaultAlt, term e)
    alt _ (LitAlt l  , [], e)    = (S.LiteralAlt l, term e)
    alt b (DataAlt dc, xs, e)    = case (isEmptyVarSet $ exprSomeFreeVars (`elem` [b]) e) of
          True  -> case (as,cs) of
            ([],[]) -> (S.DataAlt dc zs, term e)
            _       -> error $ "Patterns binding coercions or type variables are not supported: " ++ pprString (dc,xs,e)
          False -> error $ "Exprs binding scrutinee are not supported: " ++ pprString (dc,xs,e)
      where
        (as,ys) = span isTyVar xs
        (cs,zs) = span isCoVar ys

    alt b lt                     = error $ "coreExprToTerm: " ++ pprString lt
