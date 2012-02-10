{-# LANGUAGE CPP #-}
module CLaSH.Desugar.Tools
  ( mkDelay
  , mkBlockRam
  , isArrowExpression
  , mkFunction
  )
where

-- External Modules
import Control.Monad.Trans (lift)
import qualified Data.Label.PureM as Label
import qualified Data.Map         as Map

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import qualified Name
import qualified TyCon
import qualified Type
import qualified Var

-- Internal Modules
import CLaSH.Desugar.Types
import CLaSH.Util.Core (mkExternalVar,TypedThing(..),cloneVar)

mkDelay ::
#if __GLASGOW_HASKELL__ >= 702
  Type.TyVar
#else
  Var.TyVar
#endif
  -> Type.Type
  -> DesugarSession Var.Var
mkDelay sTV clockTy = do
  let stateTy           = Type.mkTyVarTy sTV
  let delayTy           = Type.mkForAllTy sTV $ Type.mkFunTys [stateTy,clockTy,stateTy] stateTy
  delay                 <- mkExternalVar "CLaSH.Builtin" "delayBuiltin" delayTy
  return delay

mkBlockRam ::
#if __GLASGOW_HASKELL__ >= 702
  Type.TyVar
  -> Type.TyVar
#else
  Var.TyVar
  -> Var.TyVar
#endif
  -> Type.Type
  -> Type.Type
  -> Type.Type
  -> DesugarSession Var.Var
mkBlockRam sizeTV dataTV clockTy addrTy weTy = do
  let dataTy = Type.mkTyVarTy dataTV
  let sizeTy = Type.mkTyVarTy sizeTV
  let blockRamTy = Type.mkForAllTys [sizeTV,dataTV] $ Type.mkFunTys [sizeTy,clockTy,dataTy,addrTy,addrTy,weTy] dataTy
  bram <- mkExternalVar "CLaSH.Builtin" "blockRamBuiltin" blockRamTy
  return bram

isArrowExpression ::
	CoreSyn.CoreExpr
	-> Bool
isArrowExpression expr = res
  where
	  ty = getTypeFail expr
	  res =	case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> (Name.getOccString (TyCon.tyConName tycon)) == "Component"
  		Nothing -> False

mkFunction ::
  Var.Var
  -> CoreSyn.CoreExpr
  -> DesugarSession Var.Var
mkFunction bndr body = do
  let bodyTy = getTypeFail body
  bodyId <- cloneVar bndr
  let newId = Var.setVarType bodyId bodyTy
  addGlobalBind newId body
  return newId

addGlobalBind ::
  Var.Var
  -> CoreSyn.CoreExpr
  -> DesugarSession ()
addGlobalBind vId body = do
  (lift . lift) $ Label.modify dsBindings (Map.insert vId body)
