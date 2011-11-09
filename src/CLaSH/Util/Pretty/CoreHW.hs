{-# LANGUAGE PatternGuards #-}
module CLaSH.Util.Pretty.CoreHW
  ()
where

-- GHC API
import Var (varType)

-- Internal Modules
import CLaSH.Util hiding (pprBndr)
import CLaSH.Util.CoreHW.Syntax

newtype PrettyFunction = PrettyFunction (Rational -> SDoc)

instance Outputable PrettyFunction where
  pprPrec prec (PrettyFunction f) = f prec

asPrettyFunction :: Outputable a => a -> PrettyFunction
asPrettyFunction x = PrettyFunction (\prec -> pprPrec prec x)

instance Outputable Term where
  pprPrec prec e = case e of
    Var x         -> pprPrec prec x
    Prim x        -> pprPrec prec x
    TyLambda x e  -> pprPrecLam prec [x] e
    Lambda x e    -> pprPrecLam prec [x] e
    Data dc       -> pprPrec prec dc
    Literal l     -> pprPrec prec l
    TyApp e ty    -> pprPrecApp prec e ty
    App e x       -> pprPrecApp prec e x
    Case e _ alts -> pprPrecCase prec e (map (second id) alts)
    LetRec xes e  -> pprPrecLetRec prec (map (second id) xes) e

instance Outputable AltCon where
    pprPrec prec altcon = case altcon of
        DataAlt dc xs -> prettyParen (prec >= appPrec) $ ppr dc <+> hsep (map (pprBndr CaseBind) xs)
        LiteralAlt l  -> ppr l
        DefaultAlt    -> text "_"

appPrec, opPrec, noPrec :: Num a => a
appPrec = 2 -- Argument of a function application
opPrec  = 1 -- Argument of an infix operator
noPrec  = 0 -- Others

prettyParen :: Bool -> SDoc -> SDoc
prettyParen False = id
prettyParen True  = parens

pprPrecApp :: (Outputable a, Outputable b) => Rational -> a -> b -> SDoc
pprPrecApp prec e1 e2 = prettyParen (prec >= appPrec) $ pprPrec opPrec e1 <+> pprPrec appPrec e2

pprPrecCase :: (Outputable a, Outputable b, Outputable c) => Rational -> a -> [(b,c)] -> SDoc
pprPrecCase prec e alts = prettyParen (prec > noPrec) $ hang (text "case" <+> pprPrec noPrec e <+> text "of") 2 $ vcat (map (pprPrecAlt noPrec) alts)

pprPrecAlt :: (Outputable a, Outputable b) => Rational -> (a, b) -> SDoc
pprPrecAlt _ (alt_con, alt_e) = hang (pprPrec noPrec alt_con <+> text "->") 2 (pprPrec noPrec alt_e)

pprPrecLetRec :: (Outputable a, Outputable b) => Rational -> [(Var, a)] -> b -> SDoc
pprPrecLetRec prec xes eBody
  | [] <- xes = pprPrec prec eBody
  | otherwise = prettyParen (prec > noPrec) $ hang (text "letrec") 2 (vcat [pprBndr LetBind x <+> text "=" <+> pprPrec noPrec e | (x,e) <- xes]) $$ text "in" <+> pprPrec noPrec eBody

pprBndr :: BindingSite -> Var -> SDoc
pprBndr bs x = prettyParen needsParens $ ppr x <+> text "::" <+> ppr (varType x)
  where needsParens = case bs of LambdaBind -> True
                                 CaseBind   -> True
                                 LetBind    -> False

pprPrecLam :: Outputable a => Rational -> [Var] -> a -> SDoc
pprPrecLam prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pprBndr LambdaBind y | y <- xs] <+> (text "->") $+$ (pprPrec noPrec e)

pprPrecApps :: (Outputable a, Outputable b) => Rational -> a -> [b] -> SDoc
pprPrecApps prec e1 es2 = prettyParen (not (null es2) && prec >= appPrec) $ pprPrec opPrec e1 <+> hsep (map (pprPrec appPrec) es2)
