module CLaSH.Desugar where

import CLaSH.Desugar.Types
import qualified CoreSyn

desugar' ::
  CoreSyn.CoreBndr
  -> DesugarSession (CoreSyn.CoreBndr,CoreSyn.CoreExpr)
