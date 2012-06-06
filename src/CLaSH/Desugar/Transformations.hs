{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP           #-}
module CLaSH.Desugar.Transformations
  ( inlineArrowBndr
  , componentCastRemoval
  , arrDesugar
  , returnADesugar
  , hooksDesugar
  , firstDesugar
  , componentDesugar
  , loopDesugar
  , usedComponentDesugar
  , blockRamDesugar
  )
where

-- External Modules
import qualified Control.Monad as Monad
import Control.Monad.Trans (lift)
import Language.KURE (liftQ)

-- GHC API
import CoreSyn (Expr(..),Bind(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified MkCore
import qualified Name
import qualified TcType
import qualified Type
import qualified TysWiredIn

-- Internal Modules
import {-# SOURCE #-} CLaSH.Desugar
import CLaSH.Desugar.Tools
import CLaSH.Desugar.Types
import CLaSH.Driver.Tools (getGlobalExpr)
import CLaSH.Util.Core (mkInternalVar,TypedThing(..))
import CLaSH.Util.Core.Transform (changed, regenUniques, inlineBind)
import CLaSH.Util.Pretty (pprString)

builtinArrowFuns :: [String]
builtinArrowFuns = ["arr","returnA",">>>","first","component","loop","blockRam"]

inlineArrowBndr :: DesugarStep
inlineArrowBndr c expr@(Let (NonRec bndr val) res) | isArrowExpression expr =
  inlineBind "inlineArrow" (\(b,e) -> return $ b == bndr) c expr

inlineArrowBndr c expr = fail "inlineArrowHooks"

componentCastRemoval :: DesugarStep
componentCastRemoval ctx (Cast e co) | isArrowExpression e =
  changed "componentCastRemoval" e

componentCastRemoval _ _ = fail "componentCastRemoval"

arrDesugar :: DesugarStep
arrDesugar ctx expr@(Var arr) | (Name.getOccString arr) == "arr" = do
  let compTy                        = getTypeFail expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
  let ([bTV,cTV],[],compTy'')       = TcType.tcSplitSigmaTy compTy'
  let ([fTy],_)                     = TcType.tcSplitFunTys  compTy''
  fId                               <- liftQ $ mkInternalVar "tFun" fTy
#if __GLASGOW_HASKELL__ >= 704
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" arrowDict
#else
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
#endif
  let resExpr                       = MkCore.mkCoreLams [arrTV,arrowDictId,bTV,cTV,fId] (Var fId)
  changed "arrDesugar" resExpr

arrDesugar ctx expr = fail "arrowArrDesugar"

returnADesugar :: DesugarStep
returnADesugar ctx expr@(Var returnA) | (Name.getOccString returnA) == "returnA" = do
  let compTy                          = getTypeFail expr
  let ([aTV,bTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
#if __GLASGOW_HASKELL__ >= 704
  arrowDictId                         <- liftQ $ mkInternalVar "arrowDict" arrowDict
#else
  arrowDictId                         <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
#endif
  outId                               <- liftQ $ mkInternalVar "out" (Type.mkTyVarTy bTV)
  let resExpr                         = MkCore.mkCoreLams [aTV,bTV,arrowDictId,outId] (Var outId)
  changed "returnADesugar" resExpr

returnADesugar ctx expr = fail "arrowReturnADesugar"

hooksDesugar :: DesugarStep
hooksDesugar ctx expr@(Var hooks) | (Name.getOccString hooks) == ">>>" = do
  let compTy                        = getTypeFail expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
#if __GLASGOW_HASKELL__ >= 704
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" arrowDict
#else
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
#endif
  let ([aTV,bTV,cTV],[],_)          = TcType.tcSplitSigmaTy compTy'
  let [aTy,bTy,cTy]                 = map Type.mkTyVarTy [aTV,bTV,cTV]
  let fTy                           = Type.mkFunTy aTy bTy
  let gTy                           = Type.mkFunTy bTy cTy
  [fId,gId]                         <- liftQ $ Monad.zipWithM mkInternalVar ["f","g"] [fTy,gTy]
  [inpId,conId,outpId]              <- liftQ $ Monad.zipWithM mkInternalVar ["inp","con","outp"] [aTy, bTy, cTy]
  let letBndrs                      = Rec [ (conId, App (Var fId) (Var inpId))
                                          , (outpId, App (Var gId) (Var conId))
                                          ]
  let resExpr                      = MkCore.mkCoreLams
                                      [arrTV,arrowDictId,aTV,bTV,cTV,fId,gId,inpId]
                                      (MkCore.mkCoreLet letBndrs (Var outpId))
  changed "hooksDesugar" resExpr

hooksDesugar ctx expr = fail "arrowHooksDesugar"

firstDesugar :: DesugarStep
firstDesugar ctx expr@(Var first) | (Name.getOccString first) == "first" = do
  let compTy                        = getTypeFail expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
#if __GLASGOW_HASKELL__ >= 704
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" arrowDict
#else
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
#endif
  let ([bTV,cTV,dTV],[],_)          = TcType.tcSplitSigmaTy compTy'
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
  let letBndrs                      = Rec [ (bId, unpackB)
                                          , (dId, unpackD)
                                          , (cId, App (Var fId) (Var bId))
                                          , (outpId, MkCore.mkCoreTup [Var cId, Var dId])
                                          ]
  let resExpr                       = MkCore.mkCoreLams
                                        [arrTV,arrowDictId,bTV,cTV,dTV,fId,inpId]
                                        (MkCore.mkCoreLet letBndrs (Var outpId))
  changed "firstDesugar" resExpr

firstDesugar ctx expr = fail "arrowFirstDesugar"

componentDesugar :: DesugarStep
componentDesugar ctx expr@(Var component) | (Name.getOccString component) == "component" = do
  let compTy                      = getTypeFail expr
  let ([sTV,iTV,oTV],[],compTy')  = TcType.tcSplitSigmaTy compTy
  let [iTy,oTy]                   = TcType.mkTyVarTys [iTV,oTV]
  let ([fTy,sTy,clockTy],_)       = TcType.tcSplitFunTys compTy'
  let (_,resTy)                   = TcType.tcSplitFunTys fTy
  [fId,initSId,clockId]           <- liftQ $ Monad.zipWithM mkInternalVar ["tFun","initS","clock"]        [fTy,sTy,clockTy]
  [inputId,outputId,outputSId]    <- liftQ $ Monad.zipWithM mkInternalVar ["input","output","outputS"]    [iTy,oTy,oTy]
  resId                           <- liftQ $ mkInternalVar "result" resTy
  [stateInId,stateOutId,stateSId] <- liftQ $ Monad.zipWithM mkInternalVar ["stateCur","stateNext","stateS"] [sTy,sTy,sTy]
  let unpackStateOut              = MkCore.mkSmallTupleSelector [stateSId,outputSId] stateSId  (MkCore.mkWildValBinder resTy) (Var resId)
  let unpackOutput                = MkCore.mkSmallTupleSelector [stateSId,outputSId] outputSId (MkCore.mkWildValBinder resTy) (Var resId)
  delayFunc                       <- liftQ $ mkDelay sTV clockTy
  let letBndrs                    = Rec [ (resId, MkCore.mkCoreApps (Var fId) [Var stateInId, Var inputId])
                                        , (stateOutId, unpackStateOut)
                                        , (outputId, unpackOutput)
                                        , (stateInId, MkCore.mkCoreApps (Var delayFunc) [Type sTy, Var initSId, Var clockId, Var stateOutId] )
                                        ]
  let resExpr                     = MkCore.mkCoreLams
                                      [sTV,iTV,oTV,fId,initSId,clockId,inputId]
                                      (MkCore.mkCoreLet letBndrs (Var outputId))
  changed "componentDesugar" resExpr

componentDesugar ctx expr = fail "arrowComponentDesugar"

loopDesugar :: DesugarStep
loopDesugar ctx expr@(Var loop) | Name.getOccString loop == "loop" = do
  let compTy                        = getTypeFail expr
  let ([arrTV],[arrowDict],compTy') = TcType.tcSplitSigmaTy compTy
#if __GLASGOW_HASKELL__ >= 704
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" arrowDict
#else
  arrowDictId                       <- liftQ $ mkInternalVar "arrowDict" (Type.mkPredTy arrowDict)
#endif
  let ([bTV,dTV,cTV],_,compTy'')    = TcType.tcSplitSigmaTy compTy'
  let [bTy,dTy,cTy]                 = map Type.mkTyVarTy [bTV,dTV,cTV]
  let finpTy                        = TysWiredIn.mkBoxedTupleTy [bTy, dTy]
  let foutpTy                       = TysWiredIn.mkBoxedTupleTy [cTy, dTy]
  let fTy                           = Type.mkFunTy finpTy foutpTy
  [fId,finpId,foutId]               <- liftQ $ Monad.zipWithM mkInternalVar ["f","finp","foutp"]    [fTy,finpTy,foutpTy]
  [bId,cId,cSId,dId,dSId]           <- liftQ $ Monad.zipWithM mkInternalVar ["b","c","cS","d","dS"] [bTy,cTy,cTy,dTy,dTy]
  let unpackC                       = MkCore.mkSmallTupleSelector [cSId,dSId] cSId (MkCore.mkWildValBinder foutpTy) (Var foutId)
  let unpackD                       = MkCore.mkSmallTupleSelector [cSId,dSId] dSId (MkCore.mkWildValBinder foutpTy) (Var foutId)
  let letBndrs                      = Rec [ (finpId, MkCore.mkCoreTup [Var bId, Var dId])
                                          , (foutId, MkCore.mkCoreApp (Var fId) (Var finpId))
                                          , (cId   , unpackC)
                                          , (dId   , unpackD)
                                          ]
  let resExpr                       = MkCore.mkCoreLams
                                        [arrTV,arrowDictId,bTV,dTV,cTV,fId,bId]
                                        (MkCore.mkCoreLet letBndrs (Var cId))
  changed "loopDesugar" resExpr

loopDesugar ctx expr = fail "arrowLoopDesugar"

usedComponentDesugar :: DesugarStep
usedComponentDesugar ctx expr
  | (Var f, args) <- CoreSyn.collectArgs expr
  , isArrowExpression expr
  , (Name.getOccString f) `notElem` builtinArrowFuns
  = do
    bodyMaybe <- liftQ $ (lift . lift) $ getGlobalExpr dsBindings f
    case bodyMaybe of
      Nothing -> fail "usedComponentDesugar"
      Just body -> do
        (newBndr,e) <- liftQ $ desugar' f
        let newExpr = MkCore.mkCoreApps (Var newBndr) args
        changed ("usedComponentDesugar") newExpr

usedComponentDesugar _ _ = fail "usedComponentDesugar"

blockRamDesugar :: DesugarStep
blockRamDesugar ctx expr@(App _ _)
  | isArrowExpression expr
  , (Var blockRam, args) <- CoreSyn.collectArgs expr
  , (Name.getOccString blockRam) == "blockRam"
  = do
    let forallTy                                   = getTypeFail blockRam
    let ([sizeTV,dataTV],[posDict],funTy)          = TcType.tcSplitSigmaTy forallTy
#if __GLASGOW_HASKELL__ >= 704
    posDictId                                      <- liftQ $ mkInternalVar "posDict" posDict
#else
    posDictId                                      <- liftQ $ mkInternalVar "posDict" (Type.mkPredTy posDict)
#endif
    let ([sizeArgTy,clockArgTy],compTy)            = TcType.tcSplitFunTys funTy
    let (compTC, [compInpTy,compOutpTy])           = TcType.tcSplitTyConApp compTy
    [sizeId,clockId,inputId,outputId]              <- liftQ $ Monad.zipWithM mkInternalVar ["bsize","bclk","binp","boutp"] [sizeArgTy,clockArgTy,compInpTy,compOutpTy]
    let (_, [dataInTy,wrTy,rdTy,weTy])             = TcType.tcSplitTyConApp compInpTy
    [dataInSId,wrSId,rdSId,weSId]                  <- liftQ $ Monad.zipWithM mkInternalVar ["dataInS","wrS","rdS","weS"] [dataInTy,wrTy,rdTy,weTy]
    let [dataInWild,wrWild,rdWild,weWild]          = map MkCore.mkWildValBinder [dataInTy,wrTy,rdTy,weTy]
    let selections                                 = zip (zipWith (replaceAt [dataInWild,wrWild,rdWild,weWild]) [0..] [dataInSId,wrSId,rdSId,weSId]) [dataInSId,wrSId,rdSId,weSId]
    let [dataInUnpack,wrUnpack,rdUnpack,weUnpack]  = map (\(sels,i) -> MkCore.mkSmallTupleSelector sels i (MkCore.mkWildValBinder compInpTy) (Var inputId)) selections
    [dataInId,wrId,rdId,weId]                      <- liftQ $ Monad.zipWithM mkInternalVar ["dataIn","wr","rd","we"] [dataInTy,wrTy,rdTy,weTy]
    bramFunc                                       <- liftQ $ mkBlockRam sizeTV dataTV clockArgTy wrTy weTy
    let bramApp                                    = MkCore.mkCoreApps (Var bramFunc) $ map Type [sizeArgTy, dataInTy] ++ map Var [sizeId,clockId,dataInId,wrId,rdId,weId]
    let letBndrs = Rec $ zip [dataInId,wrId,rdId,weId] [dataInUnpack,wrUnpack,rdUnpack,weUnpack] ++ [(outputId,bramApp)]
    let resExpr = MkCore.mkCoreLams
                    [sizeTV,dataTV,posDictId,sizeId,clockId,inputId]
                    (MkCore.mkCoreLet letBndrs (Var outputId))
    let newExpr = MkCore.mkCoreApps resExpr args
    newBram <- liftQ $ mkFunction blockRam newExpr

    changed "blockRamDesugar" (Var newBram)
    where
      replaceAt :: [a] -> Int -> a -> [a]
      replaceAt [] _ _     = []
      replaceAt (_:xs) 0 y = y:xs
      replaceAt (x:xs) n y = x:(replaceAt xs (n-1) y)

blockRamDesugar ctx expr = fail "blockRamDesugar"
