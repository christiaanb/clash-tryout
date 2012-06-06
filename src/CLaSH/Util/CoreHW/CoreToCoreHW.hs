{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP           #-}
module CLaSH.Util.CoreHW.CoreToCoreHW
  ( coreExprToTerm
  )
where

-- External Modules
import Control.Monad (join, liftM, liftM2)

-- GHC API
import CoreFVs    (exprSomeFreeVars)
import CoreSyn    (CoreExpr, Expr(..), Unfolding(..), Bind(..), AltCon(..),rhssOfAlts)
import CoreUnfold (exprIsConApp_maybe)
#if __GLASGOW_HASKELL__ >= 702
import Coercion   (isCoVar,coercionType)
#endif
import DataCon    (DataCon,dataConName,dataConTyCon)
import FastString (mkFastString)
import Id         (mkSysLocalM,isDataConWorkId_maybe,isDictId,isDFunId,isClassOpId_maybe)
import TyCon      (isNewTyCon)
import Var        (Var,isTyVar)
#if __GLASGOW_HASKELL__ < 702
import Var        (isTyCoVar)
#endif
import VarSet     (isEmptyVarSet)

-- Internal Modules
import CLaSH.Util
import qualified CLaSH.Util.CoreHW.Constants as S
import qualified CLaSH.Util.CoreHW.Syntax as S
import qualified CLaSH.Util.CoreHW.Tools  as S
import CLaSH.Util.Pretty

coreExprToTerm ::
  [Var]
  -> CoreExpr
  -> S.Term
coreExprToTerm unlocs expr = term expr
  where
    term (Var x)                 = case (isDataConWorkId_maybe x) of
                                    Just dc | isNewTyCon (dataConTyCon dc) -> error $ "Newtype not supported: " ++ pprString dc
                                            | otherwise                    -> if (S.varString x `elem` S.builtinDataCons) then S.Prim (S.PrimCon dc) else S.Data dc
                                    Nothing -> let xString = S.varString x in case (xString `elem` S.builtinIds) of
                                      True  -> case (xString `elem` S.builtinDicts) of
                                        True -> S.Prim $ S.PrimDict x
                                        False -> case (xString `elem` S.builtinDFuns) of
                                          True -> S.Prim $ S.PrimDFun x
                                          False -> S.Prim $ S.PrimFun x
                                      False -> unlocatableToPrim unlocs x

    term (Lit l)                 = S.Literal l
    term (App eFun (Type tyArg)) = S.TyApp (term eFun) tyArg
    term (App eFun eArg)         = S.App (term eFun) (term eArg)
#if __GLASGOW_HASKELL__ >= 702
    term (Lam x e) | isTyVar x   = S.TyLambda x (term e)
#else
    term (Lam x e) | isTyCoVar x = S.TyLambda x (term e)
#endif
                   | otherwise   = S.Lambda x (term e)
    term (Let (NonRec x e1) e2)  = S.LetRec [(x, term e1)] (term e2)
    term (Let (Rec xes) e)       = S.LetRec (map (second term) xes) (term e)
    term (Case e b ty alts)      = let usesBndr = any ( not
                                                      . isEmptyVarSet
                                                      . exprSomeFreeVars (`elem` [b])
                                                      ) (rhssOfAlts alts)
                                   in if usesBndr
                                      then S.LetRec [(b,term e)] (S.Case (S.Var b) ty (map (alt b) alts))
                                      else S.Case (term e) ty (map (alt b) alts)
    term (Cast e co)             = term e
#if __GLASGOW_HASKELL__ >= 704
    term (Tick _ e)              = term e
#else
    term (Note _ e)              = term e
#endif
    term (Type ty)               = error $ "Type at non-argument position not supported:\n" ++ pprString ty
#if __GLASGOW_HASKELL__ >= 702
    term (Coercion co)           = S.Prim $ S.PrimCo co
#endif

    alt _ (DEFAULT   , [], e)    = (S.DefaultAlt, term e)
    alt _ (LitAlt l  , [], e)    = (S.LiteralAlt l, term e)
    alt b (DataAlt dc, xs, e)    = case (as,cs) of
            ([],[]) -> (S.DataAlt dc zs, term e)
            (_:_,[]) -> error $ "Patterns binding type variables are not supported: \n" ++
                                "DataCon: " ++ pprString dc ++ "\nVariables: " ++ pprString xs ++
                                "\nExpression: \n" ++ pprString expr
            ([],_:_) -> error $ "Patterns binding coercions are not supported: \n" ++
                                "DataCon: " ++ pprString dc ++ "\nVariables: " ++ pprString xs ++
                                "\nExpression: \n" ++ pprString expr
      where
        (as,ys) = span isTyVar xs
#if __GLASGOW_HASKELL__ >= 702
        (cs,zs) = span isCoVar ys
#else
        (cs,zs) = ([],ys)
#endif

    alt b lt                     = error $ "coreExprToTerm: " ++ pprString lt

unlocatableToPrim ::
  [Var]
  -> Var
  -> S.Term
unlocatableToPrim unlocs v = case (v `elem` unlocs) of
  True  | Id.isDictId v -> S.Prim $ S.PrimDict v
        | Id.isDFunId v -> S.Prim $ S.PrimDFun v
        | Id.isClassOpId_maybe v /= Nothing -> S.Var v
        | otherwise     -> S.Prim $ S.PrimFun v
  False -> S.Var v
