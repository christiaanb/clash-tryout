module CLaSH.Normalize.Types
where

-- External Modules
import Control.Monad.Error (ErrorT)
import Control.Monad.State (StateT)
import Control.Monad.Reader (Reader)
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

data NormalizeState = NormalizeState
  { _nsNormalized       :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _nsBindings         :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _nsNetlistState     :: NetlistState
  , _nsTransformCounter :: Int
  , _nsUniqSupply       :: UniqSupply.UniqSupply
  , _nsBndrSubst        :: VarEnv.VarEnv CoreSyn.CoreBndr
  }
  
emptyNormalizeState uniqSupply = NormalizeState empty empty empytNetlistState 0 uniqSupply VarEnv.emptyVarEnv

Data.Label.mkLabels [''NormalizeState]

type NormalizeSession = ErrorT String (StateT NormalizeState IO)

data CoreContext = AppFirst
                 | AppSecond
                 | LetBinding [CoreSyn.CoreBndr]
                 | LetBody  [CoreSyn.CoreBndr]
                 | LambdaBody CoreSyn.CoreBndr
                 | CaseAlt CoreSyn.CoreBndr
                 | Other
  deriving (Eq, Show)

type TransformationStep = [CoreContext] -> CoreSyn.CoreExpr -> RewriteM NormalizeSession [CoreContext] CoreSyn.CoreExpr