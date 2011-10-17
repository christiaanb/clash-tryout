{-# LANGUAGE TupleSections #-}
module CLaSH.Util.CoreHW.CoreToCoreHW
  ( coreExprToTerm
  , runParseM
  )
where

-- External Modules
import Control.Monad (join, liftM, liftM2)

-- GHC API
import CoreSyn    (CoreExpr, Expr(..), Unfolding(..), Bind(..), AltCon(..))
import CoreUnfold (exprIsConApp_maybe)
import Coercion   (isCoVar)
import DataCon    (DataCon,dataConName,dataConTyCon)
import FastString (mkFastString)
import Id         (mkSysLocalM)
import TyCon      (isNewTyCon)
import Var        (Var,isTyVar)

-- Internal Modules
import CLaSH.Util
import qualified CLaSH.Util.CoreHW.Syntax as S
import qualified CLaSH.Util.CoreHW.Tools  as S
import CLaSH.Util.Pretty

data Description = Opaque String | ArgumentOf Description

descriptionString  ::
  Description
  -> String
descriptionString = go (0 :: Int)
  where
    go n (Opaque s)     = s ++ (if n > 0 then show n else "")
    go n (ArgumentOf d) = go (n+1) d

desc ::
  S.Term
  -> Description
desc t = case t of
  S.Var x                  -> Opaque (S.varString x)
  S.Value _                -> Opaque "value"
  S.TyApp e1 _             -> argOf (desc e1)
  S.App e1 _               -> argOf (desc e1)
  S.OpApp (S.PrimCall v) _ -> argOf (Opaque (S.varString v))
  S.Case _ _ _             -> Opaque "case"
  S.LetRec _ e             -> desc e

argOf ::
  Description
  -> Description
argOf = ArgumentOf

newtype ParseM a = ParseM { unParseM :: UniqSupply -> (UniqSupply, [(Var, S.Term)], a) }

instance Functor ParseM where
  fmap = liftM

instance Monad ParseM where
  return x    = ParseM $ \s -> (s, [], x)
  mx >>= fmxy = ParseM $ \s -> case unParseM mx s of
    (s1,floats1,x) -> case unParseM (fmxy x) s1 of
      (s2,floats2,y) -> (s2,floats1 ++ floats2,y)

instance MonadUnique ParseM where
  getUniqueSupplyM = ParseM $ \us -> case splitUniqSupply us of (us1,us2) -> (us1, [], us2)

runParseM' ::
  UniqSupply
  -> ParseM a
  -> (UniqSupply,([(Var,S.Term)], a))
runParseM' us act = (us',(floats, x))
  where
    (us', floats, x) = unParseM act us

runParseM ::
  UniqSupply
  -> ParseM S.Term
  -> (UniqSupply, S.Term)
runParseM us = (second $ uncurry S.LetRec) . runParseM' us

freshFloatId ::
  String
  -> S.Term
  -> ParseM (Maybe (Var, S.Term), Var)
freshFloatId _ (S.Var x) = return (Nothing, x)
freshFloatId n e        = fmap (\x -> (Just (x, e), x)) $ mkSysLocalM (mkFastString n) (S.termType e)

floatIt ::
  [(Var,S.Term)]
  -> ParseM ()
floatIt floats = ParseM $ \s -> (s, floats, ())

nameIt ::
  Description
  -> S.Term
  -> ParseM Var
nameIt d e = freshFloatId (descriptionString d) e >>= \(mbFloat, x) -> floatIt (maybeToList mbFloat) >> return x

bindFloats ::
  ParseM S.Term
  -> ParseM S.Term
bindFloats = bindFloatsWith . fmap ((,) [])

bindFloatsWith ::
  ParseM ([(Var, S.Term)], S.Term)
  -> ParseM S.Term
bindFloatsWith act = ParseM $ \s -> case unParseM act s of
  (s, floats, (xes, e)) -> (s, [], S.LetRec (xes ++ floats) e)

appE ::
  S.Term
  -> S.Term
  -> ParseM S.Term
appE e1 e2 = fmap (e1 `S.App`) $ nameIt (argOf (desc e1)) e2

conAppToTerm ::
  DataCon
  -> [CoreExpr]
  -> ParseM S.Term
conAppToTerm dc es
  | isNewTyCon (dataConTyCon dc)
  = error ("newtype not supported: " ++ pprString dc ++ " " ++ pprString es)
  | otherwise
  = do
    valEs' <- mapM coreExprToTerm valEs
    (_,xs) <- mapAccumLM (\d valE -> fmap ((,) (argOf d)) $ nameIt (argOf d) valE)
                         (Opaque (S.nameString (dataConName dc))) valEs'
    return $ S.Value (S.Data dc tys' xs)
  where
    (tys', valEs) = takeWhileJust fromType_maybe es

    fromType_maybe (Type ty) = Just ty
    fromType_maybe _         = Nothing

coreExprToTerm ::
  CoreExpr -> ParseM S.Term
coreExprToTerm = term
  where
    term e | Just (dc, univTys, es) <- exprIsConApp_maybe (const NoUnfolding) e
           = conAppToTerm dc (map Type univTys ++ es)
    term (Var x)                 = return $ S.Var x
    term (Lit l)                 = return $ S.Value (S.Literal l)
    term (App eFun (Type tyArg)) = fmap (flip S.TyApp tyArg) (term eFun)
    term (App eFun eArg)         = join $ liftM2 appE (term eFun) (term eArg)
    term (Lam x e) | isTyVar x   = fmap (S.Value . S.TyLambda x) (bindFloats (term e))
                   | otherwise   = fmap (S.Value . S.Lambda x)   (bindFloats (term e))
    term (Let (NonRec x e1) e2)  = bindFloatsWith (liftM2 (,) (fmap (:[]) $ secondM term (x,e1)) (term e2))
    term (Let (Rec xes) e)       = bindFloatsWith (liftM2 (,) (mapM (secondM term) xes) (term e))
    term (Case e _ ty alts)      = liftM2 (\e' alts' -> S.Case e' ty alts') (term e) (mapM alt alts)
    term (Cast e co)             = error $ "cast not supported: " ++ pprString (e,co)
    term (Note _ e)              = term e
    term (Type ty)               = error $ "non-argument type: " ++ pprString ty
    term (Coercion co)           = error $ "coercion not supported" ++ pprString co

    alt (DEFAULT , [], e)   = fmap ((,) S.DefaultAlt)         $ bindFloats (term e)
    alt (LitAlt l, [], e)   = fmap ((,) (S.LiteralAlt l))     $ bindFloats (term e)
    alt (DataAlt dc, xs, e) = fmap ((,) (S.DataAlt dc as zs)) $ bindFloats (term e)
      where
        (as,ys) = span isTyVar xs
        (_ ,zs) = case span isCoVar ys of
          ([],zs') -> ([],zs')
          _        -> error $ "coercions tyvars not supported: " ++ pprString (dc,xs,e)
    alt lt                  = error $ "coreExprToTerm: " ++ pprString lt
