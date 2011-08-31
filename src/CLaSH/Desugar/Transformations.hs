module CLaSH.Desugar.Transformations
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import Control.Monad.Trans
import qualified Data.Maybe as Maybe
import Language.KURE
  
-- GHC API
import CoreSyn (Expr(..),Bind(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified MkCore
import qualified Name
import qualified TcType
import qualified Type
import qualified TysWiredIn
import qualified Var

-- Internal Modules
import CLaSH.Desugar.Tools
import CLaSH.Desugar.Types
import CLaSH.Driver.Tools
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Core.Transform
import CLaSH.Util.Core.Types
import CLaSH.Util.Pretty

inlineArrowBndr :: DesugarStep
inlineArrowBndr c expr@(Let (NonRec bndr val) res) | isArrowExpression expr =
  inlineBind "inlineArrow" (\(b,e) -> return $ b == bndr) c expr
    
inlineArrowBndr c expr = fail "inlineArrowHooks"

inlineCompLift :: DesugarStep
inlineCompLift ctx expr@(Var liftComp) | (Name.getOccString liftComp) == "^^^" = do
  bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr dsBindings liftComp
  case bodyMaybe of
    Just body -> do
      bodyUniqued <- regenUniques ctx body
      changed "inlineCompLift" bodyUniqued
    Nothing -> fail "inlineCompLift"

inlineCompLift ctx expr = fail "inlineCompLift"

arrDesugar :: DesugarStep
arrDesugar ctx expr@(Var arr) | (Name.getOccString arr) == "arr" = do
  let compTy                      = CoreUtils.exprType expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
  let ([bTV,cTV],_,compTy'')      = TcType.tcSplitSigmaTy compTy'
  let ([fTy],_)                   = TcType.tcSplitFunTys compTy''
  fId                             <- liftQ $ mkInternalVar "tFun" fTy
  arrowDictId                     <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
  let resExpr                     = MkCore.mkCoreLams [arrTV,arrowDictId,bTV,cTV,fId] (Var fId)
  changed "arrDesugar" resExpr
  
arrDesugar ctx expr = fail "arrowArrDesugar"

returnADesugar :: DesugarStep
returnADesugar ctx expr@(Var returnA) | (Name.getOccString returnA) == "returnA" = do
  let compTy                          = CoreUtils.exprType expr
  let ([aTV,bTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
  arrowDictId                         <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
  outId                               <- liftQ $ mkInternalVar "out" (Type.mkTyVarTy bTV)
  let resExpr                         = MkCore.mkCoreLams [aTV,bTV,arrowDictId,outId] (Var outId)
  changed "returnADesugar" resExpr

returnADesugar ctx expr = fail "arrowReturnADesugar"

hooksDesugar :: DesugarStep
hooksDesugar ctx expr@(Var hooks) | (Name.getOccString hooks) == ">>>" = do
  let compTy                        = CoreUtils.exprType expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
  let ([aTV,bTV,cTV],_,_)           = TcType.tcSplitSigmaTy compTy'
  let [aTy,bTy,cTy]                 = map Type.mkTyVarTy [aTV,bTV,cTV]
  let fTy                           = Type.mkFunTy aTy bTy
  let gTy                           = Type.mkFunTy bTy cTy
  [fId,gId]                         <- liftQ $ Monad.zipWithM mkInternalVar ["f","g"] [fTy,gTy]
  [inpId,conId,outpId]              <- liftQ $ Monad.zipWithM mkInternalVar ["inp","con","outp"] [aTy, bTy, cTy]
  let letBndrs = Rec [ (conId, App (Var fId) (Var inpId))
                     , (outpId, App (Var gId) (Var conId))
                     ]
  let resExpr = MkCore.mkCoreLams [arrTV,arrowDictId,aTV,bTV,cTV,fId,gId,inpId] (MkCore.mkCoreLet letBndrs (Var outpId))
  changed "hooksDesugar" resExpr

hooksDesugar ctx expr = fail "arrowHooksDesugar"

firstDesugar :: DesugarStep
firstDesugar ctx expr@(Var first) | (Name.getOccString first) == "first" = do
  let compTy                        = CoreUtils.exprType expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
  let ([bTV,cTV,dTV],_,_)           = TcType.tcSplitSigmaTy compTy'
  let [bTy,cTy,dTy]                 = map Type.mkTyVarTy [bTV,cTV,dTV]
  let fTy                           = Type.mkFunTy bTy cTy
  [bId,bSId]                        <- liftQ $ Monad.zipWithM mkInternalVar ["b","bS"] [bTy,bTy]
  [dId,dSId]                        <- liftQ $ Monad.zipWithM mkInternalVar ["d","dS"] [dTy,dTy]
  cId                               <- liftQ $ mkInternalVar "c" cTy
  fId                               <- liftQ $ mkInternalVar "f" fTy
  let inpTy                         = TysWiredIn.mkBoxedTupleTy [bTy, dTy]
  let outpTy                        = TysWiredIn.mkBoxedTupleTy [cTy, dTy]
  [inpId,outpId]                    <- liftQ $ Monad.zipWithM mkInternalVar ["inp","outp"] [inpTy,outpTy]
  let unpackB                       = MkCore.mkSmallTupleSelector [bSId,dSId] bSId (MkCore.mkWildValBinder inpTy) (Var inpId)
  let unpackD                       = MkCore.mkSmallTupleSelector [bSId,dSId] dSId (MkCore.mkWildValBinder inpTy) (Var inpId)
  let letBndrs = Rec [ (bId, unpackB)
                     , (dId, unpackD)
                     , (cId, App (Var fId) (Var bId))
                     , (outpId, MkCore.mkCoreTup [Var cId, Var dId])
                     ]
  let resExpr = MkCore.mkCoreLams [arrTV,arrowDictId,bTV,cTV,dTV,fId,inpId] (MkCore.mkCoreLet letBndrs (Var outpId))
  changed "firstDesugar" resExpr

firstDesugar ctx expr = fail "arrowFirstDesugar"

componentDesugar :: DesugarStep
componentDesugar ctx expr@(Var component) | (Name.getOccString component) == "component" = do
  let compTy                      = CoreUtils.exprType expr
  let ([sTV,iTV,oTV],_,compTy')   = TcType.tcSplitSigmaTy compTy
  let [iTy,oTy]                   = TcType.mkTyVarTys [iTV,oTV]
  let ([fTy,sTy,clockTy],_)       = TcType.tcSplitFunTys compTy'
  let (_,resTy)                   = TcType.tcSplitFunTys fTy
  [fId,initSId,clockId]           <- liftQ $ Monad.zipWithM mkInternalVar ["tFun","initS","clock"]        [fTy,sTy,clockTy]
  [inputId,outputId,outputSId]    <- liftQ $ Monad.zipWithM mkInternalVar ["input","output","outputS"]    [iTy,oTy,oTy]
  resId                           <- liftQ $ mkInternalVar "result" resTy
  [stateInId,stateOutId,stateSId] <- liftQ $ Monad.zipWithM mkInternalVar ["stateIn","stateOut","stateS"] [sTy,sTy,sTy]
  let unpackStateOut              = MkCore.mkSmallTupleSelector [stateSId,outputSId] stateSId  (MkCore.mkWildValBinder resTy) (Var resId)
  let unpackOutput                = MkCore.mkSmallTupleSelector [stateSId,outputSId] outputSId (MkCore.mkWildValBinder resTy) (Var resId)
  delayFunc                       <- liftQ $ mkDelay sTV clockTy
  let letBndrs                    = Rec [ (resId, MkCore.mkCoreApps (Var fId) [Var stateInId, Var inputId])
                                        , (stateOutId, unpackStateOut)
                                        , (outputId, unpackOutput)
                                        , (stateInId, MkCore.mkCoreApps (Var delayFunc) [Type sTy, Var initSId, Var clockId, Var stateOutId] )
                                        ]
  let resExpr = MkCore.mkCoreLams [sTV,iTV,oTV,fId,initSId,clockId,inputId] (MkCore.mkCoreLet letBndrs (Var outputId))
  changed "componentDesugar" resExpr

componentDesugar ctx expr = fail "arrowComponentDesugar"
