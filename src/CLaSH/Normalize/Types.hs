module CLaSH.Normalize.Types
  ( NormalizeState(..)
  , NormalizeSession
  , NormalizeStep
  , nsNormalized
  , nsBindings
  , nsNetlistState
  , emptyNormalizeState
  )
where

-- External Modules
import Control.Monad.State.Strict (StateT)
import qualified Data.Label
import Data.Map                   (Map,empty)
import Language.KURE              (RewriteM)

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Netlist.Types (NetlistState, empytNetlistState)
import CLaSH.Util.CoreHW   (Term, Var, CoreContext, TransformSession)

-- | State kept by the normalization phase
data NormalizeState = NormalizeState
  {
  -- | Cached normalized binders
    _nsNormalized     :: Map Var Term
  -- | Cached global binders
  , _nsBindings       :: Map Var Term
  -- | The state of the netlist-generation stage, intended to decide if
  -- types are representable
  , _nsNetlistState   :: NetlistState
  }

-- Make lenses for the normalization stage state
Data.Label.mkLabels [''NormalizeState]

-- | Create an empty state for the normalization session
emptyNormalizeState ::
  Map Var Term -- ^ Cache of global binders
  -> NetlistState -- ^ Current netlist state
  -> NormalizeState
emptyNormalizeState bindings nlState = NormalizeState empty bindings nlState

-- | The normalization session is a transformation session with extra state
-- to cache information on already normalized binders. Needs IO to load
-- external binder information
type NormalizeSession = TransformSession (StateT NormalizeState IO)

type NormalizeStep =
  [CoreContext]
  -> Term
  -> RewriteM NormalizeSession [CoreContext] Term
