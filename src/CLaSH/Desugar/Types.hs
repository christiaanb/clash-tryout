module CLaSH.Desugar.Types
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

-- Internal Modules
import CLaSH.Util.Core.Transform
import CLaSH.Util.Core.Types

data DesugarState = DesugarState
  { _dsDesugared        :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _dsBindings         :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  }

emptyDesugarState bindings = DesugarState empty bindings

Data.Label.mkLabels [''DesugarState]

type DesugarSession = TransformSession (StateT DesugarState IO)

type DesugarStep = [CoreContext] -> CoreSyn.CoreExpr -> RewriteM DesugarSession [CoreContext] CoreSyn.CoreExpr
