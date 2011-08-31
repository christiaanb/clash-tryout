module CLaSH.Normalize.Transformations
  ( betaReduce
  , letRemoveUnused
  , letRemove
  , letRemoveSimple
  , castPropagation
  , castSimplification
  , inlineTopLevel
  , etaExpand
  , appProp
  , letRec
  , letFlat
  , retValSimpl
  , appSimpl
  , funExtract
  , scrutSimpl
  , scrutBndrRemove
  , caseSimpl
  , caseRemove
  , knownCase
  , inlinenonrep
  , funSpec
  , inlineNonRepResult
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import Control.Monad.Trans
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Label.PureM as Label
import Language.KURE

-- GHC API
import qualified BasicTypes
import qualified Coercion
import qualified CoreFVs
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified MkCore
import qualified Name
import qualified TcType
import qualified Type
import qualified TysWiredIn
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Driver.Tools
import {-# SOURCE #-} CLaSH.Normalize (normalizeMaybe)
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Core.Transform
import CLaSH.Util.Core.Types
import CLaSH.Util.Pretty

----------------------------------------------------------------
-- Cleanup transformations
----------------------------------------------------------------

--------------------------------
-- β-reduction
--------------------------------
betaReduce :: NormalizeStep
betaReduce ctx (App (Lam bndr expr) arg) | Var.isTyVar bndr = substitute         bndr arg ctx expr >>= (changed "beta")
                                         | otherwise        = substituteAndClone bndr arg ctx expr >>= (changed "beta")

betaReduce ctx expr                                         = fail "beta"

-- ==============================
-- = Unused Let Binding Removal =
-- ==============================
letRemoveUnused :: NormalizeStep
letRemoveUnused ctx expr@(Let (Rec binds) res) = do
    let binds' = filter doBind binds
    if (length binds /= length binds')
      then
        changed "letRemoveUnused" (Let (Rec binds') res)
      else
        fail "letRemoveUnused"
  where
    boundExprs      = map snd binds
    doBind (bndr,_) = any (exprUsesBinders [bndr]) (res:boundExprs)

letRemoveUnused ctx expr = fail "letRemoveUnused"
    
--------------------------------
-- empty let removal
--------------------------------
letRemove :: NormalizeStep
letRemove ctx (Let (Rec []) res) = changed "letRemove" res

letRemove ctx expr               = fail "letRemove"

-- ==============================
-- = Simple Let Binding Removal =
-- ==============================
letRemoveSimple :: NormalizeStep
letRemoveSimple = inlineBind "letRemoveSimple" (\(b,e) -> isLocalVar e)

-- ====================
-- = Cast Propagation =
-- ====================
castPropagation :: NormalizeStep
castPropagation ctx (Cast (Let binds expr) ty)       = changed "castPropagation" $ Let binds (Cast expr ty)
castPropagation ctx (Cast (Case scrut b ty alts) co) = changed "castPropagation" $ Case scrut b (Coercion.applyCo ty co) alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, Cast expr co)) alts
castPropagation ctx expr = fail "castPropagation"

-- =======================
-- = Cast Simplification =
-- =======================
castSimplification :: NormalizeStep
castSimplification ctx expr@(Cast val ty) = do
  localVar <- liftQ $ isLocalVar val
  repr <- liftQ $ isRepr val
  if (not localVar) && repr
    then do
      castValId <- liftQ $ mkBinderFor val "castVal"
      changed "castSimplification" $ Let (Rec [(castValId,val)]) (Cast (Var castValId) ty)
    else
      fail "castSimplification"
      
castSimplification ctx expr = fail "castSimplification"

-- ==============================
-- = Top level binding inlining =
-- ==============================
inlineTopLevel :: NormalizeStep
inlineTopLevel ctx@((LetBinding _):_) expr | not (isFun expr) =
  case (CoreSyn.collectArgs expr) of
    (Var f, args) -> do
      bodyMaybe <- liftQ $ needsInline f
      case bodyMaybe of
        Just body -> do
          bodyUniqued <- regenUniques ctx body
          changed "inlineTopLevel" (CoreSyn.mkApps bodyUniqued args)
        Nothing -> fail "inlineTopLevel"
    _ -> fail "inlineTopLevel"

inlineTopLevel ctx expr = fail "inlineTopLevel"

needsInline :: CoreSyn.CoreBndr -> NormalizeSession (Maybe CoreSyn.CoreExpr)
needsInline bndr = do
  bodyMaybe <- (lift . lift) $ getGlobalExpr nsBindings bndr
  case bodyMaybe of
    Nothing -> return Nothing
    Just body -> case CoreSyn.collectArgs body of
      (Var f, args) -> return $ Just body
      _ -> do
        normMaybe <- normalizeMaybe False bndr
        case normMaybe of
          Nothing -> return Nothing
          Just (_,normExpr) -> case splitNormalizedNonRep normExpr of
            (args, [bind], Var res) -> return $ Just normExpr
            _ -> return Nothing

----------------------------------------------------------------
-- Program structure transformations
----------------------------------------------------------------

--------------------------------
-- η expansion
--------------------------------
etaExpand :: NormalizeStep
etaExpand (AppFirst:cs)  expr = fail "eta"

etaExpand (AppSecond:cs) expr = fail "eta"

etaExpand ctx expr | isFun expr && not (isLam expr) = do
  let argTy = (fst . Type.splitFunTy . CoreUtils.exprType) expr
  newId <- liftQ $ mkInternalVar "param" argTy
  changed "eta" (Lam newId (App expr (Var newId)))

etaExpand ctx expr = fail "eta"

--------------------------------
-- Application propagation
--------------------------------
appProp :: NormalizeStep
appProp ctx (App (Let binds expr) arg)        = changed "appProp" $ Let binds (App expr arg)

appProp ctx (App (Case scrut b ty alts) arg)  = changed "appProp" $ Case scrut b ty' alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, App expr arg)) alts
    ty'   = CoreUtils.applyTypeToArg ty arg
    
appProp ctx expr                              = fail "appProp"

--------------------------------
-- Let recursification
-------------------------------- 
letRec :: NormalizeStep
letRec ctx (Let (NonRec bndr val) res) = changed "letRec" $ Let (Rec [(bndr,val)]) res

letRec ctx expr                        = fail "letRec"

--------------------------------
-- let flattening
--------------------------------
letFlat :: NormalizeStep
letFlat c topExpr@(Let (Rec binds) expr) = do
    let (binds',updated) = unzip $ map flatBind binds
    if (or updated) 
      then do
        changed "letFlat" $ Let (Rec $ concat binds') expr
      else
        fail "letFlat"
  where
    flatBind :: CoreBinding -> ([CoreBinding],Bool)
    flatBind (b, Let (Rec binds) expr) = ((b,expr):binds,True)
    flatBind (b, expr)                 = ([(b,expr)],False)

letFlat c expr = fail "letFlat"

--------------------------------
-- Return value simplification
--------------------------------
retValSimpl :: NormalizeStep
retValSimpl ctx expr | all isLambdaBodyCtx ctx && not (isLam expr) && not (isLet expr) = do
  localVar <- liftQ $ isLocalVar expr
  repr <- liftQ $ isRepr expr
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor expr "res"
      changed "retValSimpl" $ Let (Rec [(resId, expr)]) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr@(Let (Rec binds) body) | all isLambdaBodyCtx ctx = do
  localVar <- liftQ $ isLocalVar body
  repr <- liftQ $ isRepr body
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor body "res"
      changed "retValSimpl" $ Let (Rec $ (resId,body):binds) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr = fail "retValSimpl"

--------------------------------
-- Representable arguments simplification
--------------------------------
appSimpl :: NormalizeStep
appSimpl ctx expr@(App f arg) = do
  repr <- liftQ $ isRepr arg
  localVar <- liftQ $ isLocalVar arg
  if repr && not localVar
    then do
      argId <- liftQ $ mkBinderFor arg "arg"
      changed "appSimpl" $ Let (Rec [(argId,arg)]) (App f (Var argId))
    else
      fail "appSimpl"

appSimpl ctx expr = fail "appSimpl"

-- =======================
-- = Function Extraction =
-- =======================
funExtract :: NormalizeStep
funExtract ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr nsBindings f
    case bodyMaybe of
      Nothing -> do
        args' <- liftQ $ mapM doArg args
        if or (map fst args') 
          then
            changed "funExtract" $ MkCore.mkCoreApps fexpr (map snd args')
          else
            fail "funExtract"
      Just _ -> fail "funExtract"
  where
    (fexpr, args) = CoreSyn.collectArgs expr
    Var f         = fexpr
    
    doArg arg | not (viewVarOrApp arg) && isApplicable arg && not (hasFreeTyVars arg) = do
      let freeVars = VarSet.varSetElems $ CoreFVs.exprFreeVars arg
      let body     = MkCore.mkCoreLams freeVars arg
      funId <- mkBinderFor body "fun"
      (lift . lift) $ addGlobalBind nsBindings funId body
      return $ (True, MkCore.mkCoreApps (Var funId) (map Var freeVars))
    doArg arg = return (False, arg)

funExtract ctx expr = fail "funExtract"


----------------------------------------------------------------
-- Case normalization transformations
----------------------------------------------------------------

-- ============================
-- = Scrutinee simplification =
-- ============================
scrutSimpl :: NormalizeStep
scrutSimpl c expr@(Case scrut b ty alts) = do
  repr <- liftQ $ isRepr scrut
  localVar <- liftQ $ isLocalVar scrut
  if repr && not localVar
    then do
      scrutId <- liftQ $ mkBinderFor scrut "scrut"
      changed "scrutSimpl" $ Let (Rec [(scrutId,scrut)]) (Case (Var scrutId) b ty alts)
    else
      fail "scrutSimpl"

scrutSimpl ctx expr = fail "scrutSimpl"

-- ============================
-- = Scrutinee Binder Removal =
-- ============================
scrutBndrRemove :: NormalizeStep
scrutBndrRemove ctx (Case (Var scrut) bndr ty alts) | bndrUsed = do
    alts' <- mapM substBndrAlt alts
    changed "scrutBndrRemove" $ Case (Var scrut) wild ty alts'
  where
    isUsed (_,_,expr) = exprUsesBinders [bndr] expr
    bndrUsed          = or $ map isUsed alts
    substBndrAlt (con,bndrs,expr) = do
      expr' <- substitute bndr (Var scrut) ctx expr
      return (con, bndrs, expr')
    wild = MkCore.mkWildValBinder (Id.idType bndr)

scrutBndrRemove ctx expr = fail "scrutBndrRemove"

--------------------------------
-- Case normalization
--------------------------------
caseSimpl :: NormalizeStep
caseSimpl ctx expr@(Case scrut b ty [(cont, bndrs, Var x)]) = fail "caseSimpl"

caseSimpl ctx topExpr@(Case scrut bndr ty alts) | not bndrUsed = do
    (bindingss, alts') <- liftQ $ fmap unzip $ mapM doAlt alts
    let bindings = concat bindingss
    let newLet   = MkCore.mkCoreLet (Rec bindings) (Case scrut bndr ty alts')
    if null bindings
      then fail "caseSimpl"
      else changed "caseSimpl" newLet
  where
    isUsed (_,_,expr) = exprUsesBinders [bndr] expr
    bndrUsed = or $ map isUsed alts
    
    doAlt :: CoreSyn.CoreAlt -> NormalizeSession ([CoreBinding], CoreSyn.CoreAlt)
    doAlt (LitAlt _, _, _) = Error.throwError $ $(curLoc) ++ "Don't know how to handle LitAlt in case expression: " ++ show topExpr
    
    doAlt alt@(DEFAULT, [], expr) = do
      localVar <- isLocalVar expr
      repr <- isRepr expr
      (exprBindingMaybe, expr') <- if (not localVar) && repr
        then do
          caseValId <- mkBinderFor expr "caseVal"
          return (Just (caseValId,expr), Var caseValId)
        else
          return (Nothing, expr)
      let newAlt = (DEFAULT, [], expr')
      let bindings = Maybe.catMaybes [exprBindingMaybe]
      return (bindings, newAlt)
      
    doAlt (DataAlt dc, bndrs, expr) = do
        bndrsRes <- Monad.zipWithM doBndr bndrs [0..]
        let (newBndrs, bindingsMaybe) = unzip bndrsRes
        let usesBndrs = not $ VarSet.isEmptyVarSet $ CoreFVs.exprSomeFreeVars (`elem` newBndrs) expr
        (exprBindingMaybe, expr') <- doExpr expr usesBndrs
        let newAlt = (DataAlt dc, newBndrs, expr')
        let bindings = Maybe.catMaybes (bindingsMaybe ++ [exprBindingMaybe])
        return (bindings, newAlt)
      where
        wildBndrs = map (MkCore.mkWildValBinder . Id.idType) bndrs
        freeVars  = CoreFVs.exprSomeFreeVars (`elem` bndrs) expr
        doBndr :: CoreSyn.CoreBndr -> Int -> NormalizeSession (CoreSyn.CoreBndr, Maybe CoreBinding)
        doBndr b i = do
          repr <- isRepr b
          let wild = not (VarSet.elemVarSet b freeVars)
          if (not wild) && repr
            then do
              dcI <- dataconIndex (CoreUtils.exprType scrut) dc
              caseExpr <- mkSelCase scrut dcI i
              return (wildBndrs!!i, Just (b,caseExpr))
            else
              return (b,Nothing)
        doExpr :: CoreSyn.CoreExpr -> Bool -> NormalizeSession (Maybe CoreBinding, CoreSyn.CoreExpr)
        doExpr expr usesBndrs = do
          localVar <- isLocalVar expr
          repr <- isRepr expr
          if (not usesBndrs) && (not localVar) && repr
            then do
              caseValId <- mkBinderFor expr "caseVal"
              return (Just (caseValId, expr), Var caseValId)
            else
              return (Nothing, expr)
              
caseSimpl ctx expr = fail "caseSimpl"

-- ================
-- = Case Removal =
-- ================
caseRemove :: NormalizeStep
caseRemove ctx (Case scrut b ty [(con,bndrs,expr)]) | not usesVars = changed "caseRemove" expr
  where
    usesVars = exprUsesBinders (b:bndrs) expr
caseRemove ctx expr = fail "caseRemove"

-- ============================================
-- = Case of Known Constructor Simplification =
-- ============================================
knownCase :: NormalizeStep
knownCase ctx expr@(Case scrut@(App _ _) bndr ty alts) | not bndrUsed = do
    case CoreSyn.collectArgs scrut of
      (Var f, args) -> case Id.isDataConId_maybe f of
        Nothing -> fail "knownCase"
        Just dc -> do
          let (altcon,bndrs,res) = case List.find (\(altcon,bndr,res) -> altcon == (DataAlt dc)) alts of
                Just alt -> alt
                Nothing  -> head alts
          if altcon /= (DataAlt dc) && altcon /= DEFAULT
            then do
              liftQ $ Error.throwError $ $(curLoc) ++ "Invalid core, datacon not found in alternatie and DEFAULT alternative is not first?\n" ++ pprString expr
            else do
              let (tvs, preds, _, _) = DataCon.dataConSig dc
              let count = length tvs + length preds
              let binds = zip bndrs (drop count args)
              changed "knownCase" $ Let (Rec binds) res
  where
    isUsed (_, _, expr) = exprUsesBinders [bndr] expr
    bndrUsed            = or $ map isUsed alts

knownCase ctx expr = fail "knownCase"

-- =================================================
-- = Unrepresentable value removal transformations =
-- =================================================

-- ======================================
-- = Non-representable binding inlining =
-- ======================================
inlinenonrep :: NormalizeStep
inlinenonrep = inlineBind "inlinenonrep" (fmap not . isRepr . snd)

-- ===========================
-- = Function Specialization =
-- ===========================
funSpec :: NormalizeStep
funSpec ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr nsBindings f
    case bodyMaybe of
      Just body -> do
        (args',updated) <- fmap unzip $ liftQ $ mapM doArg args
        case (or updated) of
          True -> do
            let (newArgs',newParams',oldArgs) = unzip3 args'
            let newArgs   = concat newArgs'
            let newParams = concat newParams'
            let newBody   = MkCore.mkCoreLams newParams (MkCore.mkCoreApps body oldArgs)
            newf <- liftQ $ mkFunction f newBody
            let newExpr = MkCore.mkCoreApps (Var newf) newArgs
            changed "funSpec" newExpr
          False ->
            fail "funSpec"
      Nothing -> fail "funSpec"
  where
    (fexpr,args) = CoreSyn.collectArgs expr
    (Var f)      = fexpr
    
    doArg :: CoreSyn.CoreExpr -> NormalizeSession (([CoreSyn.CoreExpr], [CoreSyn.CoreBndr], CoreSyn.CoreExpr), Bool)
    doArg arg = do
      repr <- isRepr arg
      bndrs <- fmap (Map.keys) $ (lift . lift) $ Label.gets nsBindings
      let interesting var = Var.isLocalVar var && (var `notElem` bndrs)
      if (not repr) && (not (isVar arg && interesting (exprToVar arg))) && (not (hasFreeTyVars arg))
        then do
          let freeVars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting arg
          return ((map Var freeVars, freeVars, arg),True)
        else do
          paramId <- mkBinderFor arg "param"
          return (([arg],[paramId], mkReferenceTo paramId),False)

funSpec ctx expr = fail "funSpec"

-- =====================================
-- = Non-representable result inlining =
-- =====================================
inlineNonRepResult :: NormalizeStep
inlineNonRepResult ctx expr | not (isApplicable expr) && not (hasFreeTyVars expr) = do
  case CoreSyn.collectArgs expr of
    (Var f, args) | not (Id.isDictId f) -> do
      repr <- liftQ $ isRepr expr
      if not repr
        then do
          bodyMaybe <- liftQ $ normalizeMaybe True f
          case bodyMaybe of
            Just body -> do
              let (bndrs,binds,res) = splitNormalizedNonRep $ snd body
              if hasFreeTyVars res
                then
                  fail "inlineNonRepResult"
                else do
                  globalBndrs <- fmap (Map.keys) $ liftQ $ (lift . lift) $ Label.gets nsBindings
                  let interesting var = Var.isLocalVar var && (var `notElem` globalBndrs)
                  let freeVars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting res
                  let freeVarTypes = map Id.idType freeVars
                  let cntFreeVars = length freeVars
                  let fvsDatacon = TysWiredIn.tupleCon BasicTypes.Boxed cntFreeVars
                  let fvsDataconId = DataCon.dataConWorkId fvsDatacon
                  let newRes = if (cntFreeVars == 1) then res else CoreSyn.mkApps (Var fvsDataconId) (map Type freeVarTypes ++ map Var freeVars)
                  let newBody = CoreSyn.mkLams bndrs (Let (Rec binds) newRes)
                  f' <- liftQ $ mkFunction f newBody
                  let newApp = CoreSyn.mkApps (Var f') args
                  resBndr <- liftQ $ mkBinderFor newApp "res"
                  selCases <- liftQ $ if (cntFreeVars == 1) then
                      return [(Var resBndr)]
                    else
                      mapM (mkSelCase (Var resBndr) 0) [0..cntFreeVars-1]
                  let binds = (resBndr,newApp):(zip freeVars selCases)
                  let letExpr = Let (Rec binds) res
                  letExprUniqued <- regenUniques ctx letExpr
                  changed "inlineNonRepResult" letExprUniqued
            Nothing -> fail "inlineNonRepResult"
        else
          fail "inlineNonRepResult"
    _ -> fail "inlineNonRepResult"

inlineNonRepResult c expr = fail "inlineNonRepResult"
