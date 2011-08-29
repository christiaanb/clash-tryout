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
  , inlineArrowBndr
  , arrowArrDesugar
  , arrowReturnADesugar
  , arrowFirstDesugar
  , arrowHooksDesugar
  , arrowComponentDesugar
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Label.PureM as Label
import Language.KURE

import Debug.Trace

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
import {-# SOURCE #-} CLaSH.Normalize (normalizeMaybe,normalizeBndr,desugarArrowExpr)
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Pretty

----------------------------------------------------------------
-- Cleanup transformations
----------------------------------------------------------------

--------------------------------
-- β-reduction
--------------------------------
betaReduce :: TransformationStep
betaReduce ctx (App (Lam bndr expr) arg) | Var.isTyVar bndr = substitute bndr arg ctx expr >>= changed
                                         | otherwise        = substituteAndClone bndr arg ctx expr >>= changed

betaReduce ctx expr                                         = fail "beta"

-- ==============================
-- = Unused Let Binding Removal =
-- ==============================
letRemoveUnused :: TransformationStep
letRemoveUnused ctx expr@(Let (Rec binds) res) = do
    let binds' = filter doBind binds
    if (length binds /= length binds')
      then
        changed (Let (Rec binds') res)
      else
        fail "letRemoveUnused"
  where
    boundExprs      = map snd binds
    doBind (bndr,_) = any (exprUsesBinders [bndr]) (res:boundExprs)

letRemoveUnused ctx expr = fail "letRemoveUnused"
    
--------------------------------
-- empty let removal
--------------------------------
letRemove :: TransformationStep
letRemove ctx (Let (Rec []) res) = changed res

letRemove ctx expr               = fail "letRemove"

-- ==============================
-- = Simple Let Binding Removal =
-- ==============================
letRemoveSimple :: TransformationStep
letRemoveSimple = inlineBind "letRemoveSimple" (\(b,e) -> isLocalVar e)

-- ====================
-- = Cast Propagation =
-- ====================
castPropagation :: TransformationStep
castPropagation ctx (Cast (Let binds expr) ty)       = changed $ Let binds (Cast expr ty)
castPropagation ctx (Cast (Case scrut b ty alts) co) = changed $ Case scrut b (Coercion.applyCo ty co) alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, Cast expr co)) alts
castPropagation ctx expr = fail "castPropagation"

-- =======================
-- = Cast Simplification =
-- =======================
castSimplification :: TransformationStep
castSimplification ctx expr@(Cast val ty) = do
  localVar <- liftQ $ isLocalVar val
  repr <- liftQ $ isRepr val
  if (not localVar) && repr
    then do
      castValId <- liftQ $ mkBinderFor val "castVal"
      changed $ Let (Rec [(castValId,val)]) (Cast (Var castValId) ty)
    else
      fail "castSimplification"
      
castSimplification ctx expr = fail "castSimplification"

-- ==============================
-- = Top level binding inlining =
-- ==============================
inlineTopLevel :: TransformationStep
inlineTopLevel ctx@((LetBinding _):_) expr | not (isFun expr) =
  case (CoreSyn.collectArgs expr) of
    (Var f, args) -> do
      bodyMaybe <- liftQ $ needsInline f
      case bodyMaybe of
        Just body -> do
          bodyUniqued <- regenUniques ctx body
          changed (CoreSyn.mkApps bodyUniqued args)
        Nothing -> fail "inlineTopLevel"
    _ -> fail "inlineTopLevel"

inlineTopLevel ctx expr = fail "inlineTopLevel"

needsInline :: CoreSyn.CoreBndr -> NormalizeSession (Maybe CoreSyn.CoreExpr)
needsInline bndr = do
  bodyMaybe <- getGlobalExpr bndr
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
etaExpand :: TransformationStep
etaExpand (AppFirst:cs)  expr = fail "eta"

etaExpand (AppSecond:cs) expr = fail "eta"

etaExpand ctx expr | isFun expr && not (isLam expr) = do
  let argTy = (fst . Type.splitFunTy . CoreUtils.exprType) expr
  newId <- liftQ $ mkInternalVar "param" argTy
  changed (Lam newId (App expr (Var newId)))

etaExpand ctx expr = fail "eta"

--------------------------------
-- Application propagation
--------------------------------
appProp :: TransformationStep
appProp ctx (App (Let binds expr) arg)        = changed $ Let binds (App expr arg)

appProp ctx (App (Case scrut b ty alts) arg)  = changed $ Case scrut b ty' alts'
  where
    alts' = map (\(con,bndrs,expr) -> (con,bndrs, App expr arg)) alts
    ty'   = CoreUtils.applyTypeToArg ty arg
    
appProp ctx expr                              = fail "appProp"

--------------------------------
-- Let recursification
-------------------------------- 
letRec :: TransformationStep
letRec ctx (Let (NonRec bndr val) res) = changed $ Let (Rec [(bndr,val)]) res

letRec ctx expr                        = fail "letRec"

--------------------------------
-- let flattening
--------------------------------
letFlat :: TransformationStep
letFlat c topExpr@(Let (Rec binds) expr) = do
    let (binds',updated) = unzip $ map flatBind binds
    if (or updated) 
      then do
        changed $ Let (Rec $ concat binds') expr
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
retValSimpl :: TransformationStep
retValSimpl ctx expr | all isLambdaBodyCtx ctx && not (isLam expr) && not (isLet expr) = do
  localVar <- liftQ $ isLocalVar expr
  repr <- liftQ $ isRepr expr
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor expr "res"
      changed $ Let (Rec [(resId, expr)]) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr@(Let (Rec binds) body) | all isLambdaBodyCtx ctx = do
  localVar <- liftQ $ isLocalVar body
  repr <- liftQ $ isRepr body
  if not localVar && repr
    then do
      resId <- liftQ $ mkBinderFor body "res"
      changed $ Let (Rec $ (resId,body):binds) (Var resId)
    else
      fail "retValSimpl"

retValSimpl ctx expr = fail "retValSimpl"

--------------------------------
-- Representable arguments simplification
--------------------------------
appSimpl :: TransformationStep
appSimpl ctx expr@(App f arg) = do
  repr <- liftQ $ isRepr arg
  localVar <- liftQ $ isLocalVar arg
  if repr && not localVar
    then do
      argId <- liftQ $ mkBinderFor arg "arg"
      changed $ Let (Rec [(argId,arg)]) (App f (Var argId))
    else
      fail "appSimpl"

appSimpl ctx expr = fail "appSimpl"

-- =======================
-- = Function Extraction =
-- =======================
funExtract :: TransformationStep
funExtract ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ getGlobalExpr f
    case bodyMaybe of
      Nothing -> do
        args' <- liftQ $ mapM doArg args
        if or (map fst args') 
          then
            changed $ MkCore.mkCoreApps fexpr (map snd args')
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
      addGlobalBind funId body
      return $ (True, MkCore.mkCoreApps (Var funId) (map Var freeVars))
    doArg arg = return (False, arg)

funExtract ctx expr = fail "funExtract"


----------------------------------------------------------------
-- Case normalization transformations
----------------------------------------------------------------

-- ============================
-- = Scrutinee simplification =
-- ============================
scrutSimpl :: TransformationStep
scrutSimpl c expr@(Case scrut b ty alts) = do
  repr <- liftQ $ isRepr scrut
  localVar <- liftQ $ isLocalVar scrut
  if repr && not localVar
    then do
      scrutId <- liftQ $ mkBinderFor scrut "scrut"
      changed $ Let (Rec [(scrutId,scrut)]) (Case (Var scrutId) b ty alts)
    else
      fail "scrutSimpl"

scrutSimpl ctx expr = fail "scrutSimpl"

-- ============================
-- = Scrutinee Binder Removal =
-- ============================
scrutBndrRemove :: TransformationStep
scrutBndrRemove ctx (Case (Var scrut) bndr ty alts) | bndrUsed = do
    alts' <- mapM substBndrAlt alts
    changed $ Case (Var scrut) wild ty alts'
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
caseSimpl :: TransformationStep
caseSimpl ctx expr@(Case scrut b ty [(cont, bndrs, Var x)]) = fail "caseSimpl"

caseSimpl ctx topExpr@(Case scrut bndr ty alts) | not bndrUsed = do
    (bindingss, alts') <- liftQ $ fmap unzip $ mapM doAlt alts
    let bindings = concat bindingss
    let newLet   = MkCore.mkCoreLet (Rec bindings) (Case scrut bndr ty alts')
    if null bindings
      then fail "caseSimpl"
      else changed newLet
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
caseRemove :: TransformationStep
caseRemove ctx (Case scrut b ty [(con,bndrs,expr)]) | not usesVars = changed expr
  where
    usesVars = exprUsesBinders (b:bndrs) expr
caseRemove ctx expr = fail "caseRemove"

-- ============================================
-- = Case of Known Constructor Simplification =
-- ============================================
knownCase :: TransformationStep
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
              changed $ Let (Rec binds) res
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
inlinenonrep :: TransformationStep
inlinenonrep = inlineBind "inlinenonrep" (fmap not . isRepr . snd)

-- ===========================
-- = Function Specialization =
-- ===========================
funSpec :: TransformationStep
funSpec ctx expr@(App _ _) | isVar fexpr = do
    bodyMaybe <- liftQ $ getGlobalExpr f
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
            changed newExpr
          False ->
            fail "funSpec"
      Nothing -> fail "funSpec"
  where
    (fexpr,args) = CoreSyn.collectArgs expr
    (Var f)      = fexpr
    
    doArg :: CoreSyn.CoreExpr -> NormalizeSession (([CoreSyn.CoreExpr], [CoreSyn.CoreBndr], CoreSyn.CoreExpr), Bool)
    doArg arg = do
      repr <- isRepr arg
      bndrs <- fmap (Map.keys) $ Label.gets nsBindings
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
inlineNonRepResult :: TransformationStep
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
                  globalBndrs <- fmap (Map.keys) $ liftQ $ Label.gets nsBindings
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
                  changed letExprUniqued
            Nothing -> fail "inlineNonRepResult"
        else
          fail "inlineNonRepResult"
    _ -> fail "inlineNonRepResult"

inlineNonRepResult c expr = fail "inlineNonRepResult"

-- ====================
-- = Arrow desugaring =
-- ====================

inlineArrowBndr :: TransformationStep
inlineArrowBndr c expr@(Let (NonRec bndr val) res) | isArrowExpression expr =
  inlineBind "inlineArrow" (\(b,e) -> return $ b == bndr) c expr
    
inlineArrowBndr c expr = fail "inlineArrowHooks"

arrowArrDesugar :: TransformationStep
arrowArrDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString f) == "arr" && (not $ isApplicable expr) = do
    let [liftedFun] = getValArgs (Var.varType f) alreadyMappedArgs
    let [argTy]   = (fst . Type.splitFunTys . CoreUtils.exprType) liftedFun
    paramId <- liftQ $ mkInternalVar "param" argTy
    let liftedFunApp  = App liftedFun (Var paramId)
    let desugaredExpr = Lam paramId liftedFunApp
    changed desugaredExpr
  where
    (fexpr, alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var f)                    = fexpr
  
arrowArrDesugar ctx expr = fail "arrowArrDesugar"

arrowReturnADesugar :: TransformationStep
arrowReturnADesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString f) == "returnA" && (not $ isApplicable expr) = do
    case ((Type.splitTyConApp_maybe . CoreUtils.exprType) expr) of
      Nothing -> liftQ $ Error.throwError $ $(curLoc) ++ "returnA?\n" ++ pprString expr ++ "\n" ++ pprString (CoreUtils.exprType expr)
      Just arrType -> do
        -- Create 2 new Vars of which the 2nd is of the value type of the arrow
        let argTy = (head . snd) arrType
        paramId <- liftQ $ mkInternalVar "param" argTy
        -- Return the extracted expression 
        let packinps = Var paramId
        changed $ Lam paramId packinps
  where
    (fexpr,alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var f)                   = fexpr
    
arrowReturnADesugar ctx expr = fail "arrowReturnADesugar"

desugarSubExpression f = do
  if isArrowExpression f
    then do
      case f of
        (Var bndr) -> do
          realFExpr <- liftQ $ normalizeBndr False bndr
          let realFExprType = CoreUtils.exprType realFExpr
          return (Var $ Var.setVarType bndr realFExprType)
        otherwise -> liftQ $ desugarArrowExpr "first" f 
    else
      return f

arrowHooksDesugar :: TransformationStep
arrowHooksDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString hooks) == ">>>" && (not $ isApplicable expr) = do
    let [f,g] = getValArgs (Var.varType hooks) alreadyMappedArgs
    realF <- desugarSubExpression f
    realG <- desugarSubExpression g
    let [fSplit,gSplit] = map (Type.splitFunTys . CoreUtils.exprType) [realF,realG]
    [([fInpTy], fResTy),([gInpTy], gResTy)] <- case [fSplit,gSplit] of {
        ; [([fInpTy], fResTy),([gInpTy], gResTy)] -> return [([fInpTy], fResTy),([gInpTy], gResTy)]
        ; x -> liftQ $ Error.throwError $ $(curLoc) ++ "Unexpected Arrow Type:\n" ++ pprString expr
        }
    betaId <- liftQ $ mkInternalVar "betaHooks" fInpTy
    gammaId <- liftQ $ mkInternalVar "gammaHooks" gInpTy
    deltaId <- liftQ $ mkInternalVar "deltaHooks" gResTy
    let letexprs = Rec [ (gammaId, (App realF (Var betaId)))
                       , (deltaId, (App realG (Var gammaId)))
                       ]
    let letExpression = MkCore.mkCoreLets [letexprs] (Var deltaId)       
    changed (Lam betaId letExpression)
  where
    (fexpr,alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var hooks)               = fexpr

arrowHooksDesugar ctx expr = fail "arrowHooksDesugar"

arrowFirstDesugar :: TransformationStep
arrowFirstDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString first) == "first" && (not $ isApplicable expr) = do
    let deltaTy = (last . snd . (Maybe.fromMaybe $ (error "arrowFirstExtract (delta)(1)")) . Type.splitTyConApp_maybe . head . snd . (Maybe.fromMaybe $ (error "arrowFirstExtract (delta)(0)")) . Type.splitTyConApp_maybe . CoreUtils.exprType) expr
    -- let gammaTy = (head . snd . (Maybe.fromMaybe $ (error "arrowFirstExtract (gamma)(1)")) . Type.splitTyConApp_maybe . last . snd . (Maybe.fromMaybe $ (error "arrowFirstExtract (delta)(0)")) . Type.splitTyConApp_maybe . CoreUtils.exprType) expr
    -- Retreive the packed functions     
    let [f] = getValArgs (Var.varType first) alreadyMappedArgs
    realF <- desugarSubExpression f
    let ([betaTy], gammaTy) = (Type.splitFunTys . CoreUtils.exprType) realF
    let inputTy = TysWiredIn.mkBoxedTupleTy [betaTy,deltaTy]
    inputId <- liftQ $ mkInternalVar "inputFirst" inputTy
    -- Unpack input into input for function f and delta
    betaScrutId <- liftQ $ mkInternalVar "betaScrutFirst" betaTy
    deltaScrutId <- liftQ $ mkInternalVar "deltaScrutFirst" deltaTy
    betaId <- liftQ $ mkInternalVar "betaFirst" betaTy
    deltaId <- liftQ $ mkInternalVar "deltaFirst" deltaTy
    let unpackBeta = MkCore.mkSmallTupleSelector [betaScrutId,deltaScrutId] betaScrutId (MkCore.mkWildValBinder inputTy) (Var inputId)
    let unpackDelta = MkCore.mkSmallTupleSelector [betaScrutId,deltaScrutId] deltaScrutId (MkCore.mkWildValBinder inputTy) (Var inputId)
    -- Retreive the output of f
    gammaId <- liftQ $ mkInternalVar "gammaFirst" gammaTy
    -- Pack the result of f and delta
    let resPack = MkCore.mkCoreTup [Var gammaId, Var deltaId]
    gammaDeltaTPId <- liftQ $ mkInternalVar "gammaDeltaFirst" (CoreUtils.exprType resPack)
    let letexprs = Rec [ (betaId, unpackBeta)
                       , (deltaId, unpackDelta)
                       , (gammaId, App realF (Var betaId))
                       , (gammaDeltaTPId, resPack)
                       ]
    let letExpression = MkCore.mkCoreLets [letexprs] (Var gammaDeltaTPId)   
    changed (Lam inputId letExpression) 
  where
    (fexpr,alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var first)               = fexpr

arrowFirstDesugar ctx expr = fail "arrowFirstDesugar"

arrowComponentDesugar :: TransformationStep
arrowComponentDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString component) == "component" && (not $ isApplicable expr) = do
    let [f,initS,clockDom]          = getValArgs (Var.varType component) alreadyMappedArgs
    let ([fStateTy,fInpTy], fResTy) = (Type.splitFunTys . CoreUtils.exprType) f
    let (_,[_,fOutpTy])             = Type.splitAppTys fResTy
    inputId                         <- liftQ $ mkInternalVar "componentInput"   fInpTy
    outputId                        <- liftQ $ mkInternalVar "componentOutput"  fOutpTy
    outputScrutId                   <- liftQ $ mkInternalVar "componentOutputS" fOutpTy
    resId                           <- liftQ $ mkInternalVar "componentResult"  fResTy
    stateId                         <- liftQ $ mkInternalVar "componentState"   fStateTy
    statePrimeId                    <- liftQ $ mkInternalVar "componentStateP"  fStateTy
    statePrimeScrutId               <- liftQ $ mkInternalVar "componentStatePS" fStateTy
    let unpackStatePrime            = MkCore.mkSmallTupleSelector [statePrimeScrutId,outputScrutId] statePrimeScrutId (MkCore.mkWildValBinder fResTy) (Var resId)
    let unpackOutput                = MkCore.mkSmallTupleSelector [statePrimeScrutId,outputScrutId] outputScrutId     (MkCore.mkWildValBinder fResTy) (Var resId)
    delayFunc                       <- liftQ $ mkDelay [initS,clockDom]
    let letBndrs                    = Rec [ (resId       , MkCore.mkCoreApps f [Var stateId, Var inputId])
                                          , (statePrimeId, unpackStatePrime)
                                          , (outputId    , unpackOutput)
                                          , (stateId     , MkCore.mkCoreApps (Var delayFunc) [initS,clockDom, Var statePrimeId])
                                          ]
    let letExpression               = MkCore.mkCoreLets [letBndrs] (Var outputId)
    changed (Lam inputId letExpression)
  where
    (fexpr,alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var component)               = fexpr

arrowComponentDesugar ctx expr = fail "arrowComponentDesugar"