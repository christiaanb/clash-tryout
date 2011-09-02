module CLaSH.Desugar.Types
  ( DesugarState(..)
  , DesugarSession
  , DesugarStep
  , dsDesugared
  , dsBindings
  , emptyDesugarState
  )
where

-- External Modules
import Control.Monad.State.Strict (StateT)
import qualified Data.Label
import Data.Map (Map,empty)
import Language.KURE (RewriteM)

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Util.Core.Types (TransformSession, CoreContext)

data DesugarState = DesugarState
  { _dsDesugared        :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _dsBindings         :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  }

emptyDesugarState ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> DesugarState
emptyDesugarState bindings = DesugarState empty bindings

Data.Label.mkLabels [''DesugarState]

type DesugarSession = TransformSession (StateT DesugarState IO)

type DesugarStep = [CoreContext] -> CoreSyn.CoreExpr -> RewriteM DesugarSession [CoreContext] CoreSyn.CoreExpr
