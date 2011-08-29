module CLaSH.Util.Core.Pretty
  ( pprBinding
  )
where

-- External Modules
import Text.PrettyPrint.HughesPJClass (Pretty,prettyShow)
import qualified Text.PrettyPrint.HughesPJClass as Pretty

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import Outputable (OutputableBndr, showSDoc, ppr, ($+$), (<+>), nest, empty, text, vcat)
import qualified Outputable
import qualified Var

-- Internal Modules
import CLaSH.Util.Core.Show

instance (OutputableBndr b, Show b) => Pretty (CoreSyn.Expr b) where
  pPrint = Pretty.text . show

pprBinding
  :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr)
  -> String
pprBinding (b,e) = Outputable.showSDoc $
  (text "Binder:") <+> (text $ show b ++ "[" ++ show (Var.varUnique b) ++ "]")
  $+$ nest indent (
    hang' (text "Type of Binder:") align (Outputable.ppr $ Var.varType b)
    $+$ hang' (text "Expression:") align (text $ Pretty.prettyShow e)
    $+$ hang' (text "Pretty Expression:") align (Outputable.ppr e)
  )
  $+$ (text "\n")

align = 20
indent = 5
hang' d1 n d2 = vcat [d1, nest n d2]
