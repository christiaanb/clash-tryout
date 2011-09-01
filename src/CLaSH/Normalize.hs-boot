module CLaSH.Normalize where

import qualified CoreSyn
import CLaSH.Normalize.Types

normalizeMaybe
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession (Maybe (CoreSyn.CoreBndr, CoreSyn.CoreExpr))
