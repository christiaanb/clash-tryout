module CLaSH.Desugar where

import qualified CoreSyn
import CLaSH.Desugar.Types

desugarBndr
  :: CoreSyn.CoreBndr
  -> DesugarSession CoreSyn.CoreExpr

desugarExpr ::
  String
  -> CoreSyn.CoreExpr
  -> DesugarSession CoreSyn.CoreExpr
