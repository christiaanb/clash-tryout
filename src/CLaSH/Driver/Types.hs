module CLaSH.Driver.Types where

-- External Modules
import Control.Monad.State.Strict (StateT)
import Data.Label ((:->), lens)
import qualified Data.Label
import Data.Map (Map,empty)

-- GHC API
import qualified CoreSyn
import qualified UniqSupply

data DriverState = DriverState
  { _drUniqSupply :: UniqSupply.UniqSupply
  }

-- Derive record field accessors
Data.Label.mkLabels [''DriverState]

emptyDriverState uniqSupply = DriverState uniqSupply

type DriverSession = StateT DriverState IO
