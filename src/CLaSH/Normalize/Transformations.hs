{-# LANGUAGE PatternGuards #-}
module CLaSH.Normalize.Transformations
  ( iotaReduce
  , betaReduce
  , caseApp
  , caseLet
  , caseLam
  , caseCon
  , caseCase
  , letApp
  , letLam
  , bindLam
  , bindBox
  , inlineBox
  , etaExpand
  , funcSpec
  , typeSpec
  , funcLift

  , classopresolution

  , retLam
  , retLet
  , retVar
  , inlineVar
  , emptyLet
  , letFlat
  , deadCode
  , scrutSimpl
  , caseSimpl
  , caseRemove
  , appSimpl
  , bindUntranslatable
  , primSpec
  , inlineUntranslatable
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import Control.Monad.Trans (lift)
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Label.PureM as Label
import Language.KURE (RewriteM, liftQ, runRewrite, extractR, bottomupR, tryR, promoteR)

-- GHC API
import qualified BasicTypes
import qualified DataCon
import qualified Class
import qualified Id
import qualified MkCore
import qualified TyCon
import qualified Type
import qualified TysWiredIn
import qualified Var
import qualified VarSet

-- Internal Modules
import {-# SOURCE #-} CLaSH.Normalize (normalizeMaybe)
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util (curLoc, partitionM, secondM, second)
import CLaSH.Util.CoreHW (CoreContext(..), Term(..), Prim(..), AltCon(..), TypedThing(..), Var, CoreBinding, Type, changed, mkInternalVar, isFun, isLam, applyFunTy, substituteType, substituteExpr, termString, termSomeFreeVars, exprUsesBinders, dataConIndex, isLet, collectArgs, isPoly, tyHasFreeTyVars, mkApps, mkLams, isApplicable, transformationStep, startContext, varString, hasFreeTyVars, isVar, varStringUniq, termFreeVars, regenUniques, termType, cloneVar, collectExprArgs, inlineBind, isCon, builtinIds, builtinDicts, builtinDFuns, isPrimCon, isPrimFun, isSimple)
import CLaSH.Util.Pretty (pprString)

iotaReduce :: NormalizeStep
iotaReduce ctx e@(TyApp (TyLambda tv expr) t) = substituteType tv t ctx expr >>= (changed "iota" e)
iotaReduce _ _ = fail "betaTy"

betaReduce :: NormalizeStep
betaReduce ctx e@(App (Lambda bndr expr) arg)   = changed "beta" e $ LetRec [(bndr,arg)] expr
betaReduce _ _ = fail "beta"

caseApp :: NormalizeStep
caseApp ctx e@(App (Case scrut ty alts) arg)   = changed "caseApp" e $ Case scrut ty' alts'
  where
    alts' = map (second (`App` arg)) alts
    ty'   = applyFunTy ty (termType arg)

caseApp ctx e@(TyApp (Case scrut ty alts) ty') = liftQ $ Error.throwError $ $(curLoc) ++ "What's a TyApp doing at a case expression?: " ++ pprString e
caseApp _ _ = fail "caseApp"

caseLet :: NormalizeStep
caseLet ctx e@(Case (LetRec binds res) ty alts) = changed "caseLet" e $ LetRec binds (Case res ty alts)
caseLet _ _ = fail "caseLet"

caseLam :: NormalizeStep
caseLam ctx e@(Case scrut ty alts) = do
  let altsWithLam = List.partition isLam . map snd $ alts
  case altsWithLam of
    ([],_)                 -> fail "caseLam"
    (TyLambda tv e:rest,_) -> liftQ $ Error.throwError $ $(curLoc) ++ "What's a TyLambda doing in a case alternative?: " ++ pprString e
    (Lambda bndr e:rest,_) -> do
      bndr' <- liftQ $ cloneVar bndr
      let ty' = applyFunTy ty (Id.idType bndr)
      let alts' = map (second (`App` (Var bndr'))) alts
      let newExpr = Lambda bndr' (Case scrut ty' alts')
      changed "caseLam" e newExpr

caseLam _ _ = fail "caseLam"

caseCon :: NormalizeStep
caseCon ctx e@(Case scrut ty alts) | (Data dc, args) <- collectExprArgs scrut = do
  let (altcon,res) = case List.find
                            (\(altcon', _) -> case altcon' of
                              DataAlt dc' _ -> DataCon.dataConTag dc == DataCon.dataConTag dc'
                              _             -> False
                            ) alts of
                       Just alt -> alt
                       Nothing  -> head alts
  case altcon of
    DefaultAlt -> changed "caseCon" e res
    DataAlt dc' xs' | DataCon.dataConTag dc == DataCon.dataConTag dc' -> do
      let fvs            = VarSet.varSetElems $ termSomeFreeVars (`elem` xs') res
      let (binds,others) = List.partition ((`elem` fvs) . fst) $ zip xs' args
      case binds of
        [] -> changed "caseCon" e res
        _  -> changed "caseCon" e $ LetRec binds res
    _ -> liftQ $ Error.throwError $ $(curLoc) ++ "Invalid core, datacon not found in alternative and DEFAULT not first? " ++ pprString e

caseCon _ _ = fail "caseCon"

caseCase :: NormalizeStep
caseCase ctx e@(Case (Case scrut ty1 alts1) ty2 alts2) = do
  let newAlts = map (second (\altE -> Case altE ty2 alts2)) alts1
  let newExpr = Case scrut ty2 newAlts
  changed "caseCase" e newExpr

caseCase _ _ = fail "caseCase"

letApp :: NormalizeStep
letApp ctx e@(App (LetRec binds expr) arg)  = changed "letApp" e $ LetRec binds (App expr arg)
letApp ctx e@(TyApp (LetRec binds expr) ty) = changed "letApp" e $ LetRec binds (TyApp expr ty)
letApp _ _ = fail "letApp"

letLam :: NormalizeStep
letLam ctx e@(LetRec binds (Lambda bndr body)) = changed "letLam" e $ Lambda bndr $ LetRec binds body
letLam ctx e@(LetRec binds (TyLambda tv body)) = changed "letLam" e $ TyLambda tv $ LetRec binds body
letLam _ _ = fail "letLam"

bindLam :: NormalizeStep
bindLam = inlineBind "bindLam" (return . isLam . snd)

bindBox :: NormalizeStep
bindBox = inlineBind "bindBox" (return . isBox . snd)

inlineBox :: NormalizeStep
inlineBox ctx e@(Case scrut ty alts)
  | isBox scrut
  , (Var f, args) <- collectArgs scrut
  = do
    bodyMaybe <- liftQ $ getGlobalExpr f
    case bodyMaybe of
      Just body -> do
        scrut' <- liftQ $ regenUniques body
        changed "inlineBox" e $ Case (mkApps scrut' args) ty alts
      Nothing -> fail "inlineBox"

inlineBox _ _ = fail "inlineBox"

etaExpand :: NormalizeStep
etaExpand (AppFirst:cs)  expr = fail "eta"
etaExpand (AppSecond:cs) expr = fail "eta"

etaExpand ctx expr | isFun expr && not (isLam expr) = do
  let argTy = (fst . Maybe.fromMaybe (error "etaExpand splitFunTy") . Type.splitFunTy_maybe . getTypeFail) expr
  newId <- liftQ $ mkInternalVar "p" argTy
  changed "eta" expr (Lambda newId (App expr (Var newId)))

etaExpand ctx expr = fail "eta"

funcSpec :: NormalizeStep
funcSpec ctx e@(App e1 e2)
  | (Var f, args) <- collectArgs e1
  , isBox e2 || isFun e2
  , not . tyHasFreeTyVars . getTypeFail $ e2
  , (eArgs,[]) <- Either.partitionEithers args
  = do
    bodyMaybe <- liftQ $ getGlobalExpr f
    case bodyMaybe of
      Just body -> do
        localFVs <- liftQ $ localFreeVars e2
        argParams <- liftQ $ mapM (mkBinderFor "pFS") eArgs
        let newBody = mkLams (argParams ++ localFVs) $ mkApps body $ map (Left . Var) argParams ++ [Left e2]
        newf <- liftQ $ mkFunction f newBody
        let newExpr = mkApps (Var newf) $ args ++ (map (Left . Var) localFVs)
        changed "funSpec" e newExpr
      Nothing -> fail "funSpec"

funcSpec _ _ = fail "funcSpec"

typeSpec :: NormalizeStep
typeSpec ctx e@(TyApp e1 ty)
  | (Var f, args) <- collectArgs e1
  , not . tyHasFreeTyVars $ ty
  , (eArgs, []) <- Either.partitionEithers args
  = do
    bodyMaybe <- liftQ $ getGlobalExpr f
    case bodyMaybe of
      Just body -> do
        argParams <- liftQ $ mapM (mkBinderFor "pTS") eArgs
        let newBody = mkLams argParams $ mkApps body $ map (Left . Var) argParams ++ [Right ty]
        newf <- liftQ $ mkFunction f newBody
        let newExpr = mkApps (Var newf) args
        changed "typeSpec" e newExpr
      Nothing -> fail "typeSpec"

typeSpec _ _ = fail "typeSpec"

funcLift :: NormalizeStep
funcLift ctx e
  | (Prim f, args) <- collectArgs e
  , any (\a -> either (not . isSimple) (const False) a && either isFun (const False) a && not (tyHasFreeTyVars . either getTypeFail id $ a)) args
  = do
    args' <- mapM doArg args
    changed "funcLift" e (mkApps (Prim f) args')
  where
    doArg (Left arg) | not (isSimple arg) && isFun arg && not (hasFreeTyVars arg) = do
      fvs <- liftQ $ localFreeVars arg
      let body = mkLams fvs arg
      argId <- liftQ $ mkBinderFor "fun" body
      argId' <- liftQ $ mkFunction argId body
      return $ Left $ mkApps (Var argId') (map (Left . Var) fvs)

    doArg arg = return arg

funcLift _ _ = fail "funcLift"

classopresolution c expr@(App (TyApp (Var sel) ty) dict) = do
  case (Id.isClassOpId_maybe sel) of
    Just cls -> do
      let selectorIds = Class.classAllSelIds cls
      let selIdN = List.elemIndex sel selectorIds
      case selIdN of
        Just n -> do
          selCase <- liftQ $ mkSelCase "classopresolution" dict 0 n
          changed "classopresolution" expr selCase
        Nothing -> fail "classopresolution"
    Nothing -> fail "classopresolution"

classopresolution _ _ = fail "classopresolution"

retLam :: NormalizeStep
retLam ctx expr | all isLambdaBodyCtx ctx && not (isLam expr) && not (isLet expr) = do
  localVar <- liftQ $ isLocalVar expr
  untranslatable <- liftQ $ isUntranslatable expr
  case localVar || untranslatable of
    False -> do
      resId <- liftQ $ mkBinderFor "res" expr
      changed "retLam" expr $ LetRec [(resId, expr)] (Var resId)
    True ->
      fail "retLam"

retLam _ _ = fail "retLam"

retLet :: NormalizeStep
retLet ctx expr@(LetRec binds body) | all isLambdaBodyCtx ctx = do
  localVar <- liftQ $ isLocalVar body
  untranslatable <- liftQ $ isUntranslatable body
  case localVar || untranslatable of
    False -> do
      resId <- liftQ $ mkBinderFor "res" body
      changed "retLet" expr $ LetRec ((resId,body):binds) (Var resId)
    True ->
      fail "retLet"

retLet _ _ = fail "retLet"

retVar :: NormalizeStep
retVar [] e@(Lambda x (Var x')) | x == x' = do
  resId <- liftQ $ mkBinderFor "res" (Var x')
  changed "retVar" e $ LetRec [(resId,(Var x'))] (Var resId)

retVar _ _ = fail "retVar"

inlineVar :: NormalizeStep
inlineVar = inlineBind "inlineVar" (return . isVar . snd)

emptyLet :: NormalizeStep
emptyLet ctx e@(LetRec [] res) = changed "emptyLet" e res
emptyLet _ _ = fail "emptyLet"

letFlat :: NormalizeStep
letFlat c topExpr@(LetRec binds expr) = do
    let (binds',updated) = unzip $ map flatBind binds
    case (or updated) of
      True ->
        changed "letFlat" topExpr $ LetRec  (concat binds') expr
      False ->
        fail "letFlat"
  where
    flatBind :: CoreBinding -> ([CoreBinding],Bool)
    flatBind (b, LetRec binds expr) = ((b,expr):binds,True)
    flatBind (b, expr)              = ([(b,expr)],False)

letFlat _ _ = fail "letFlat"

deadCode :: NormalizeStep
deadCode ctx expr@(LetRec binds res) = do
  let binds' = filter doBind binds
  case (length binds /= length binds') of
    True ->
      changed "deadCode" expr (LetRec binds' res)
    False ->
      fail "deadCode"
  where
    boundExprs      = map snd binds
    doBind (bndr,_) = any (exprUsesBinders [bndr]) (res:boundExprs)

deadCode _ _ = fail "deadCode"

scrutSimpl :: NormalizeStep
scrutSimpl c expr@(Case scrut ty alts) = do
  localVar       <- liftQ $ isLocalVar scrut
  untranslatable <- liftQ $ isUntranslatable scrut
  case localVar || untranslatable of
    False -> do
      scrutId <- liftQ $ mkBinderFor "scrut" scrut
      changed "scrutSimpl" expr $ LetRec [(scrutId,scrut)] (Case (Var scrutId) ty alts)
    True ->
      fail "scrutSimpl"

scrutSimpl _ _ = fail "scrutSimpl"

caseSimpl :: NormalizeStep
caseSimpl ctx (Case scrut ty [(cont, Var x)]) = fail "caseSimpl"

caseSimpl ctx e@(Case scrut ty alts) = do
    (bindingss, alts') <- liftQ $ fmap unzip $ mapM doAlt alts
    let bindings = concat bindingss
    let newExpr  = LetRec bindings (Case scrut ty alts')
    case bindings of
      [] -> fail "caseSimpl"
      _  -> changed "caseSimpl" e newExpr
  where
    doAlt :: (AltCon, Term) -> NormalizeSession ([CoreBinding], (AltCon, Term))
    doAlt alt@(DefaultAlt, expr) = do
      localVar <- isLocalVar expr
      untranslatable <- isUntranslatable expr
      case localVar || untranslatable of
        False -> do
          caseValId <- mkBinderFor "caseAlt" expr
          return ([(caseValId,expr)], (DefaultAlt, Var caseValId))
        True -> return ([], alt)

    doAlt alt@(LiteralAlt l, expr) = do
      localVar <- isLocalVar expr
      untranslatable <- isUntranslatable expr
      case localVar || untranslatable of
        False -> do
          caseValId <- mkBinderFor "caseAlt" expr
          return ([(caseValId,expr)], (LiteralAlt l, Var caseValId))
        True -> return ([], alt)

    doAlt alt@(DataAlt dc bndrs, expr) = do
        untranslatable <- isUntranslatable expr
        localVar <- isLocalVar expr
        case localVar || untranslatable of
          False -> do
            bndrsRes <- Monad.zipWithM doBndr bndrs [0..]
            let (newBndrs, bindings) = unzip bndrsRes
            (exprBinding, expr') <- doExpr expr
            let newAlt = (DataAlt dc newBndrs, expr')
            return (concat bindings ++ exprBinding, newAlt)
          True -> return ([], alt)
      where
        wildBndrs = map (MkCore.mkWildValBinder . Id.idType) bndrs
        freeVars  = termSomeFreeVars (`elem` bndrs) expr

        doBndr :: Var -> Int -> NormalizeSession (Var, [CoreBinding])
        doBndr b i = do
          let used = VarSet.elemVarSet b freeVars
          case used of
            True -> do
              dcI <- dataConIndex (getTypeFail scrut) dc
              caseExpr <- mkSelCase "caseSimpl" scrut dcI i
              return (wildBndrs!!i, [(b,caseExpr)])
            False -> return (b, [])

        doExpr :: Term -> NormalizeSession ([CoreBinding], Term)
        doExpr altE = do
          caseValId <- mkBinderFor "caseAlt" altE
          return ([(caseValId,altE)],Var caseValId)

caseSimpl _ _ = fail "caseSimpl"

caseRemove :: NormalizeStep
caseRemove ctx e@(Case scrut ty [(DefaultAlt, expr)])                     = changed "caseRemove" e expr
caseRemove ctx e@(Case scrut ty [(DataAlt dc bndrs,expr)]) | not usesVars = changed "caseRemove" e expr
  where
    usesVars = exprUsesBinders bndrs expr
caseRemove _ _ = fail "caseRemove"

appSimpl :: NormalizeStep
appSimpl ctx e@(App appf arg)
  | (f, _) <- collectArgs appf
  , isVar f || isCon f || isPrimCon f || isPrimFun f = do
    localVar <- liftQ $ isLocalVar arg
    untranslatable <- liftQ $ isUntranslatable arg
    case localVar || untranslatable of
      True  -> fail "appSimpl"
      False -> do
        argId <- liftQ $ mkBinderFor "arg" arg
        changed "appSimpl" e (LetRec [(argId,arg)] (App appf (Var argId)))

appSimpl _ _ = fail "appSimpl"

bindUntranslatable :: NormalizeStep
bindUntranslatable = inlineBind ("bindUntranslatable") (isUntranslatable . fst)

primSpec :: NormalizeStep
primSpec ctx e@(App e1 e2)
  | (Var f, args)  <- collectArgs e1
  , (Prim prim, _) <- collectArgs e2
  = do
    case prim of
      PrimFun _ -> fail "primSpec"
      PrimCon _ -> fail "primSpel"
      _ -> do
        bodyMaybe <- liftQ $ getGlobalExpr f
        case bodyMaybe of
          Just body -> do
            let newBody = mkApps body [Left (Prim prim)]
            newf <- liftQ $ mkFunction f newBody
            let newExpr = mkApps (Var newf) args
            changed "primSpec" e newExpr
          Nothing -> fail "primSpec"

primSpec _ _ = fail "primSpec"

inlineUntranslatable :: NormalizeStep
inlineUntranslatable ctx e@(App e1 e2)
  | (Prim _, _)   <- collectArgs e1
  , (Var f, args) <- collectArgs e2
  , not (isApplicable e2)
  = do
   untranslatable <- liftQ $ isUntranslatable f
   bodyMaybe      <- liftQ $ getGlobalExpr f
   case (untranslatable,bodyMaybe) of
     (True,Just body) -> do
       let newBody = mkApps body args
       let newExpr = App e1 newBody
       changed ("inlineUntranslatable: " ++ pprString (f,e2)) e newExpr
     _ -> fail "inlineUntranslatable"

inlineUntranslatable _ _ = fail "inlineUntranslatable"
