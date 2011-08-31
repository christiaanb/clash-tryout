module CLaSH.Desugar.Transformations
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Maybe as Maybe
import Language.KURE
  
-- GHC API
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified MkCore
import qualified Name
import qualified Type
import qualified TysWiredIn
import qualified Var

-- Internal Modules
import {-# SOURCE #-} CLaSH.Desugar (desugarBndr,desugarExpr)
import CLaSH.Desugar.Tools
import CLaSH.Desugar.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Core.Transform
import CLaSH.Util.Pretty

inlineArrowBndr :: DesugarStep
inlineArrowBndr c expr@(Let (NonRec bndr val) res) | isArrowExpression expr =
  inlineBind "inlineArrow" (\(b,e) -> return $ b == bndr) c expr
    
inlineArrowBndr c expr = fail "inlineArrowHooks"

arrDesugar :: DesugarStep
arrDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString f) == "arr" && (not $ isApplicable expr) = do
    let [liftedFun] = getValArgs (Var.varType f) alreadyMappedArgs
    let [argTy]   = (fst . Type.splitFunTys . CoreUtils.exprType) liftedFun
    paramId <- liftQ $ mkInternalVar "param" argTy
    let liftedFunApp  = App liftedFun (Var paramId)
    let desugaredExpr = Lam paramId liftedFunApp
    changed desugaredExpr
  where
    (fexpr, alreadyMappedArgs) = CoreSyn.collectArgs expr
    (Var f)                    = fexpr
  
arrDesugar ctx expr = fail "arrowArrDesugar"

returnADesugar :: DesugarStep
returnADesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString f) == "returnA" && (not $ isApplicable expr) = do
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
    
returnADesugar ctx expr = fail "arrowReturnADesugar"

desugarSubExpression f = do
  if isArrowExpression f
    then do
      case f of
        (Var bndr) -> do
          realFExpr <- liftQ $ desugarBndr bndr
          let realFExprType = CoreUtils.exprType realFExpr
          return (Var $ Var.setVarType bndr realFExprType)
        otherwise -> liftQ $ desugarExpr "first" f 
    else
      return f

hooksDesugar :: DesugarStep
hooksDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString hooks) == ">>>" && (not $ isApplicable expr) = do
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

hooksDesugar ctx expr = fail "arrowHooksDesugar"

firstDesugar :: DesugarStep
firstDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString first) == "first" && (not $ isApplicable expr) = do
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

firstDesugar ctx expr = fail "arrowFirstDesugar"

componentDesugar :: DesugarStep
componentDesugar ctx expr@(App _ _) | isVar fexpr && (Name.getOccString component) == "component" && (not $ isApplicable expr) = do
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

componentDesugar ctx expr = fail "arrowComponentDesugar"
