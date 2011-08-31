module CLaSH.Desugar.Tools
where

-- External Modules
import qualified Data.Label.PureM as Label
import Language.KURE

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import qualified Name
import qualified TyCon
import qualified Type
import qualified Var

-- Internal Modules
import CLaSH.Desugar.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Core.Transform
import CLaSH.Util.Core.Traverse

mkDelay ::
  [CoreSyn.CoreExpr]
  -> DesugarSession Var.Var
mkDelay [initS,clockDomain] = do
  let [stateTy,clockTy] = map CoreUtils.exprType [initS,clockDomain]
  let delayTy           = Type.mkFunTys [stateTy,clockTy,stateTy] stateTy
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
