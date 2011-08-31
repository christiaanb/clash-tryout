module CLaSH.Normalize.Types
where

-- External Modules
import Control.Monad.Error (ErrorT)
import Control.Monad.State (StateT)
import Data.Label ((:->), lens)
import qualified Data.Label
import Data.Map (Map,empty)
import Language.KURE

-- GHC API
import qualified CoreSyn
import qualified UniqSupply
import qualified VarEnv

-- Internal Modules
import CLaSH.Netlist.Types
import CLaSH.Util.Core.Types

data NormalizeState = NormalizeState
  { _nsNormalized     :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _nsBindings       :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _nsNetlistState   :: NetlistState
  }
  
emptyNormalizeState bindings = NormalizeState empty bindings empytNetlistState

Data.Label.mkLabels [''NormalizeState]

type NormalizeSession = TransformSession (StateT NormalizeState IO)

type NormalizeStep = [CoreContext] -> CoreSyn.CoreExpr -> RewriteM NormalizeSession [CoreContext] CoreSyn.CoreExpr
