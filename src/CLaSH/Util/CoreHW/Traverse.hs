{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module CLaSH.Util.CoreHW.Traverse
  (startContext
  ,transformationStep
  ,changed
  )
where

-- External Modules
import Control.Monad                 (liftM, liftM2)
import qualified Data.Label.PureM as Label
import Data.Monoid                   (Monoid, mempty, mconcat, mappend)
import Language.KURE hiding          (apply)
import qualified Language.KURE    as KURE

-- Internal Modules
import CLaSH.Util
import qualified CLaSH.Util.CoreHW.Syntax as C
import qualified CLaSH.Util.CoreHW.Types  as C
import CLaSH.Util.Pretty

startContext :: [C.CoreContext]
startContext = []

data CoreGeneric = CTerm C.Term

instance Term C.Term where
  type Generic C.Term = CoreGeneric
  select (CTerm e)    = Just e
  inject              = CTerm

instance Term CoreGeneric where
  type Generic CoreGeneric = CoreGeneric
  inject                   = id
  select                   = Just

apply :: Monad m
  => C.CoreContext
  -> Translate m [C.CoreContext] e1 e2
  -> e1
  -> RewriteM m [C.CoreContext] e2
apply c rw e = mapEnvM (c:) $ KURE.apply rw e

varR :: (Monoid dec, Monad m)
  => Rewrite m dec C.Term
varR = transparently $ rewrite $ \e -> case e of
  (C.Var x) -> return (C.Var x)
  _         -> fail "varR"

varU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec C.Term r
varU = translate $ \e -> case e of
  (C.Var x) -> return $ mempty (C.Var x)
  _         -> fail "varU"

primR :: (Monoid dec, Monad m)
  => Rewrite m dec C.Term
primR = transparently $ rewrite $ \e -> case e of
  (C.Prim x) -> return (C.Prim x)
  _         -> fail "varR"

primU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec C.Term r
primU = translate $ \e -> case e of
  (C.Prim x) -> return $ mempty (C.Prim x)
  _         -> fail "varU"

litR :: (Monoid dec, Monad m)
  => Rewrite m dec C.Term
litR = transparently $ rewrite $ \e -> case e of
  (C.Literal x) -> return (C.Literal x)
  _             -> fail "litR"

litU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec C.Term r
litU = translate $ \e -> case e of
  (C.Literal x) -> return $ mempty
  _             -> fail "litU"

tyLamR :: Monad m
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
tyLamR rr = transparently $ rewrite $ \e -> case e of
  C.TyLambda tv e -> liftM (C.TyLambda tv) (apply (C.TyLambdaBody tv) rr e)
  _               -> fail "tyLamR"

tyLamU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
tyLamU rr = translate $ \e -> case e of
  C.TyLambda tv e -> apply (C.TyLambdaBody tv) rr e
  _               -> fail "tyLamU"

lamR :: Monad m
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
lamR rr = transparently $ rewrite $ \e -> case e of
  C.Lambda tv e -> liftM (C.Lambda tv) (apply (C.LambdaBody tv) rr e)
  _             -> fail "lamR"

lamU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
lamU rr = translate $ \e -> case e of
  C.Lambda tv e -> apply (C.LambdaBody tv) rr e
  _             -> fail "lamU"

dataR :: (Monoid dec, Monad m)
  => Rewrite m dec C.Term
dataR = transparently $ rewrite $ \e -> case e of
  (C.Data d) -> return (C.Data d)
  _          -> fail "dataR"

dataU :: (Monoid dec, Monad m, Monoid r)
  => Translate m dec C.Term r
dataU = translate $ \e -> case e of
  (C.Data d) -> return $ mempty
  _          -> fail "dataU"

appR :: (Monad m)
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
appR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  (C.App e1 e2) -> liftM2 C.App (apply C.AppFirst rr1 e1) (apply C.AppSecond rr2 e2)
  _             -> fail "appR"

appU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
appU rr1 rr2 = translate $ \e -> case e of
  (C.App e1 e2) -> liftM2 mappend (apply C.AppFirst rr1 e1) (apply C.AppSecond rr2 e2)
  _             -> fail "appU"

tyAppR :: (Monad m)
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
tyAppR rr = transparently $ rewrite $ \e -> case e of
  (C.TyApp e t) -> liftM (`C.TyApp` t) (apply C.TyAppFirst rr e)
  _             -> fail "appR"

tyAppU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
tyAppU rr = translate $ \e -> case e of
  (C.TyApp e t) -> (apply C.TyAppFirst rr e)
  _             -> fail "appU"

letR :: (Monad m)
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
letR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  (C.LetRec binds e) -> do let bndrs = map fst binds
                           liftM2 C.LetRec (mapM (secondM (apply (C.LetBinding bndrs) rr1)) binds)
                                           (apply (C.LetBody bndrs) rr2 e)
  _                  -> fail "letR"

letU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
letU rr1 rr2 = translate $ \e -> case e of
  (C.LetRec binds e)  -> do let bndrs = map fst binds
                            liftM2 mappend (liftM mconcat (mapM (apply (C.LetBinding bndrs) rr1 . snd) binds))
                                           (apply (C.LetBody bndrs) rr2 e)
  _                   -> fail "letU"

caseR :: (Monad m)
  => Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
  -> Rewrite m [C.CoreContext] C.Term
caseR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  (C.Case scrut t alts) -> liftM2 (\scrut' alts' -> C.Case scrut' t alts')
                                    (apply C.Other rr1 scrut)
                                    (mapM (secondM (apply C.CaseAlt rr2)) alts)
  _                     -> fail "caseR"

caseU :: (Monad m, Monoid r)
  => Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
  -> Translate m [C.CoreContext] C.Term r
caseU rr1 rr2 = translate $ \e -> case e of
  (C.Case scrut t alts) -> liftM2 mappend (apply C.Other rr1 scrut) (liftM mconcat (mapM (apply C.CaseAlt rr2 . snd) alts))
  _                     -> fail "caseU"

instance (Monad m) => Walker m [C.CoreContext] C.Term where
  allR rr   =  varR
            <+ litR
            <+ primR
            <+ tyLamR (extractR rr)
            <+ lamR   (extractR rr)
            <+ dataR
            <+ appR   (extractR rr) (extractR rr)
            <+ tyAppR (extractR rr)
            <+ letR   (extractR rr) (extractR rr)
            <+ caseR  (extractR rr) (extractR rr)
  crushU rr =  varU
            <+ litU
            <+ primU
            <+ tyLamU (extractU rr)
            <+ lamU   (extractU rr)
            <+ dataU
            <+ appU   (extractU rr) (extractU rr)
            <+ tyAppU (extractU rr)
            <+ letU   (extractU rr) (extractU rr)
            <+ caseU  (extractU rr) (extractU rr)

instance (Monad m) => Walker m [C.CoreContext] CoreGeneric where
  allR rr = transparently $ rewrite $ \e -> case e of
    CTerm s -> liftM CTerm $ KURE.apply (allR rr) s
  crushU rr = translate $ \e -> case e of
    CTerm s -> KURE.apply (crushU rr) s

transformationStep step = rewrite $ \e -> do
  c <- readEnvM
  step c e

changed ::
  (Monad m)
  => String
  -> C.Term
  -> C.Term
  -> RewriteM (C.TransformSession m) [C.CoreContext] C.Term
changed tId prevTerm expr = do
  liftQ $ Label.modify C.tsTransformCounter (+1)
  --trace ("\n" ++ tId ++ "(before):\n" ++ pprString prevTerm ++ "\n\n" ++ tId ++ "(after):\n" ++ pprString expr) $ markM $ return expr
  trace tId $ markM $ return expr
  --markM $ return expr
