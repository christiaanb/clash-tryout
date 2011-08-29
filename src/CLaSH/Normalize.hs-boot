module CLaSH.Normalize where

import qualified CoreSyn
import CLaSH.Normalize.Types

normalizeMaybe
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession (Maybe (CoreSyn.CoreBndr, CoreSyn.CoreExpr))

normalizeBndr
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession CoreSyn.CoreExpr

normalizeExpr
  :: String
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreExpr

desugarArrowExpr
  :: String
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreExpr
