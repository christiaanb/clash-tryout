module CLaSH.Netlist.Types
where

import Control.Monad.Error (ErrorT)
import Control.Monad.State (State)
import Data.Label ((:->), lens)
import qualified Data.Label
import Data.Map (Map,fromList)

data HWType = BitType
            | SignedType Int
            | SumType     String [String]
            | ProductType String [HWType]
            | SPType      String [(String,[HWType])]
            | UnitType
            | CompType
            -- | ClockType
            | Invalid String
  deriving (Eq,Ord,Show)

data NetlistState = NetlistState {
  _nlTypes :: Map String HWType
}

empytNetlistState = NetlistState (fromList [("Bit",BitType)])

Data.Label.mkLabels [''NetlistState]

type NetlistSession = ErrorT String (State NetlistState)
