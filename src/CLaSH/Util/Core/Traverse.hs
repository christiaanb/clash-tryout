{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP                   #-}
module CLaSH.Util.Core.Traverse
  ( startContext
  , transformationStep
  )
where

-- External Modules
import Control.Monad (liftM, liftM2)
import Data.Monoid (Monoid, mempty, mconcat, mappend)
import Language.KURE hiding (apply)
import qualified Language.KURE as KURE

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Util.Core.Types
-- import CLaSH.Util.Pretty

startContext :: [CoreContext]
startContext = []

data CoreGeneric = CExpr CoreSyn.CoreExpr
                 | CBind CoreSyn.CoreBind

instance Term CoreSyn.CoreExpr where
  type Generic CoreSyn.CoreExpr = CoreGeneric
  select (CExpr e) = Just e
  select _         = Nothing
  inject           = CExpr

instance Term CoreSyn.CoreBind where
  type Generic CoreSyn.CoreBind = CoreGeneric
  select (CBind b) = Just b
  select _         = Nothing
  inject           = CBind

instance Term CoreGeneric where
  type Generic CoreGeneric = CoreGeneric
  inject = id
  select = Just

apply :: Monad m
  => CoreContext
  -> Translate m [CoreContext] e1 e2
  -> e1
  -> RewriteM m [CoreContext] e2
apply c rw e = mapEnvM (c:) $ KURE.apply rw e

varR :: (Monoid dec, Monad m)
  => Rewrite m dec CoreSyn.CoreExpr
varR = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Var x) -> return (CoreSyn.Var x)
  _               -> fail "varR"

varU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec CoreSyn.CoreExpr r
varU = translate $ \e -> case e of
  (CoreSyn.Var x) -> return $ mempty (CoreSyn.Var x)
  _               -> fail "varU"

litR :: (Monoid dec, Monad m)
  => Rewrite m dec CoreSyn.CoreExpr
litR = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Lit x) -> return (CoreSyn.Lit x)
  _               -> fail "litR"

litU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec CoreSyn.CoreExpr r
litU = translate $ \e -> case e of
  (CoreSyn.Lit x) -> return $ mempty
  _               -> fail "litU"

appR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
appR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  (CoreSyn.App e1 e2) -> liftM2 CoreSyn.App (apply AppFirst rr1 e1)
                                            (apply AppSecond rr2 e2)
  _                   -> fail "appR"

appU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
appU rr1 rr2 = translate $ \e -> case e of
  (CoreSyn.App e1 e2) -> liftM2 mappend (apply AppFirst  rr1 e1)
                                        (apply AppSecond rr2 e2)
  _                   -> fail "appU"

lamR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
lamR rr = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Lam b expr) -> liftM (CoreSyn.Lam b) (apply (LambdaBody b) rr expr)
  _                    -> fail "lamR"

lamU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
lamU rr = translate $ \e -> case e of
  (CoreSyn.Lam b x) -> apply (LambdaBody b) rr x
  _                 -> fail "lamU"

letR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreBind
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
letR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Let e1@(CoreSyn.NonRec b bexpr) e2) -> liftM2 CoreSyn.Let (KURE.apply rr1 e1)
                                                                     (apply (LetBody [b]) rr2 e2)
  (CoreSyn.Let e1@(CoreSyn.Rec binds) e2)      -> liftM2 CoreSyn.Let (KURE.apply rr1 e1)
                                                                     (apply (LetBody $ map fst binds) rr2 e2)
  _                                            -> fail "letR"

letU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreBind r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
letU rr1 rr2 = translate $ \e -> case e of
  (CoreSyn.Let e1@(CoreSyn.NonRec b bexpr) e2) -> liftM2 mappend (KURE.apply rr1 e1)
                                                                 (apply (LetBody [b]) rr2 e2)
  (CoreSyn.Let e1@(CoreSyn.Rec binds) e2)      -> liftM2 mappend (KURE.apply rr1 e1)
                                                                 (apply (LetBody $ map fst binds) rr2 e2)
  _                                            -> fail "letU"

nonRecR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreBind
nonRecR rr = transparently $ rewrite $ \e -> case e of
  (CoreSyn.NonRec b e1) -> liftM (CoreSyn.NonRec b) (apply (LetBinding []) rr e1)
  _                     -> fail "nonRecR"

nonRecU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreBind r
nonRecU rr = translate $ \e -> case e of
  (CoreSyn.NonRec b e1) -> apply (LetBinding []) rr e1
  _                     -> fail "nonRecU"

recR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreBind
recR rr = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Rec binds) -> do
    binds' <- mapM (transBind (map fst binds)) binds
    return $ CoreSyn.Rec binds'
  _                   -> fail "recR"
  where
    transBind bndrs (bndr, expr) = do
      expr' <- apply (LetBinding bndrs) rr expr
      return (bndr, expr')

recU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreBind r
recU rr = translate $ \e -> case e of
  (CoreSyn.Rec binds) -> liftM mconcat $ mapM (apply (LetBinding $ map fst binds) rr) (map (\(_,expr)->expr) binds)
  _                   -> fail "recU"

caseR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
caseR rr1 rr2 = transparently $ rewrite $ \e -> case e of
  expr@(CoreSyn.Case scrut b t alts) -> do
    scrut' <- KURE.apply rr1 scrut
    alts' <- mapM (transAlt b) alts
    return $ CoreSyn.Case scrut' b t alts'
  _                                  -> fail $ "caseR"
  where
    transAlt b (con, binders, expr) = do
      expr' <- apply (CaseAlt b) rr2 expr
      return (con, binders, expr')

caseU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
caseU rr1 rr2 = translate $ \e -> case e of
  (CoreSyn.Case scrut b t alts) -> liftM2 mappend (KURE.apply rr1 scrut) (liftM mconcat (mapM (apply (CaseAlt b) rr2) (map (\(_,_,x)->x) alts)))
  _                             -> fail "caseU"

castR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
castR rr = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Cast expr co) -> liftM ((flip CoreSyn.Cast) co) (apply Other rr expr)
  _                      -> fail "castR"

castU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
castU rr = translate $ \e -> case e of
  (CoreSyn.Cast expr co) -> apply (Other) rr expr
  _                      -> fail "castU"

noteR :: (Monad m)
  => Rewrite m [CoreContext] CoreSyn.CoreExpr
  -> Rewrite m [CoreContext] CoreSyn.CoreExpr
noteR rr = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Note note expr) -> liftM (CoreSyn.Note note) (apply Other rr expr)
  _                        -> fail "noteR"

noteU :: (Monad m, Monoid r)
  => Translate m [CoreContext] CoreSyn.CoreExpr r
  -> Translate m [CoreContext] CoreSyn.CoreExpr r
noteU rr = translate $ \e -> case e of
  (CoreSyn.Note note expr) -> apply (Other) rr expr
  _                        -> fail "noteU"

typeR :: (Monoid dec, Monad m)
  => Rewrite m dec CoreSyn.CoreExpr
typeR = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Type x) -> return (CoreSyn.Type x)
  _               -> fail "typeR"

typeU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec CoreSyn.CoreExpr r
typeU = translate $ \e -> case e of
  (CoreSyn.Type x) -> return $ mempty (CoreSyn.Type x)
  _               -> fail "typeU"

#if __GLASGOW_HASKELL__ >= 702
coercionR :: (Monoid dec, Monad m)
  => Rewrite m dec CoreSyn.CoreExpr
coercionR = transparently $ rewrite $ \e -> case e of
  (CoreSyn.Coercion x) -> return (CoreSyn.Coercion x)
  _               -> fail "coercionR"

coercionU :: (Monad m, Monoid dec, Monoid r)
  => Translate m dec CoreSyn.CoreExpr r
coercionU = translate $ \e -> case e of
  (CoreSyn.Coercion x) -> return $ mempty (CoreSyn.Coercion x)
  _               -> fail "coercionU"
#endif

instance (Monad m) => Walker m [CoreContext] CoreSyn.CoreExpr where
  allR rr   =  varR
            <+ litR
            <+ appR  (extractR rr) (extractR rr)
            <+ lamR  (extractR rr)
            <+ letR  (extractR rr) (extractR rr)
            <+ caseR (extractR rr) (extractR rr)
            <+ castR (extractR rr)
            <+ noteR (extractR rr)
            <+ typeR
#if __GLASGOW_HASKELL__ >= 702
            <+ coercionR
#endif
  crushU rr =  varU
            <+ litU
            <+ appU  (extractU rr) (extractU rr)
            <+ lamU  (extractU rr)
            <+ letU  (extractU rr) (extractU rr)
            <+ caseU (extractU rr) (extractU rr)
            <+ castU (extractU rr)
            <+ noteU (extractU rr)
            <+ typeU
#if __GLASGOW_HASKELL__ >= 702
            <+ coercionU
#endif

instance (Monad m) => Walker m [CoreContext] CoreSyn.CoreBind where
  allR rr   =  nonRecR (extractR rr)
            <+ recR    (extractR rr)
            <+ (transparently $ rewrite $ \e -> return e)
  crushU rr =  nonRecU (extractU rr)
            <+ recU    (extractU rr)

instance (Monad m) => Walker m [CoreContext] CoreGeneric where
  allR rr = transparently $ rewrite $ \e -> case e of
    CExpr s -> liftM CExpr $ KURE.apply (allR rr) s
    CBind s -> liftM CBind $ KURE.apply (allR rr) s
  crushU rr = translate $ \e -> case e of
    CExpr s -> KURE.apply (crushU rr) s
    CBind s -> KURE.apply (crushU rr) s

transformationStep step = rewrite $ \e -> do
  c <- readEnvM
  step c e
