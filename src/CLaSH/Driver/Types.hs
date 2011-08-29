module CLaSH.Driver.Types where

-- External Modules
import Control.Monad.State (StateT)
import Data.Label ((:->), lens)
import qualified Data.Label
import Data.Map (Map,empty)

-- GHC API
import qualified CoreSyn

data DriverState = DriverState
  { _tsBindings :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  }

-- Derive record field accessors
Data.Label.mkLabels [''DriverState]

emptyDriverState = DriverState empty

type DriverSession = StateT DriverState IO
