module CLaSH.Normalize where

import CLaSH.Normalize.Types
import CLaSH.Util.CoreHW (Var, Term)

normalizeMaybe
  :: Bool
  -> Var
  -> NormalizeSession (Maybe (Var, Term))
