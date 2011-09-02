module CLaSH.Desugar.Tools
  ( mkDelay
  , isArrowExpression
  )
where

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import qualified Name
import qualified TyCon
import qualified Type
import qualified Var

-- Internal Modules
import CLaSH.Desugar.Types
import CLaSH.Util.Core (mkExternalVar)

mkDelay ::
  Type.TyVar
  -> Type.Type
  -> DesugarSession Var.Var
mkDelay sTV clockTy = do
  let stateTy           = Type.mkTyVarTy sTV
  let delayTy           = Type.mkForAllTy sTV $ Type.mkFunTys [stateTy,clockTy,stateTy] stateTy
  delay                 <- mkExternalVar "CLaSH.Builtin" "delay" delayTy
  return delay

isArrowExpression ::
	CoreSyn.CoreExpr
	-> Bool
isArrowExpression expr = res
  where
	  ty = CoreUtils.exprType expr
	  res =	case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> (Name.getOccString (TyCon.tyConName tycon)) == "Component"
  		Nothing -> False
