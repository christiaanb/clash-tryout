module CLaSH.Util.Core.Types
where

-- External Modules
import Control.Monad.State (StateT)
import Control.Monad.Error (ErrorT)
import qualified Data.Label
import Language.KURE

-- GHC API
import qualified CoreSyn
import qualified UniqSupply
import qualified VarEnv

-- Internal Modules
import CLaSH.Driver.Types

data CoreContext = AppFirst
                 | AppSecond
                 | LetBinding [CoreSyn.CoreBndr]
                 | LetBody  [CoreSyn.CoreBndr]
                 | LambdaBody CoreSyn.CoreBndr
                 | CaseAlt CoreSyn.CoreBndr
                 | Other
  deriving (Eq, Show)

data TransformState = TransformState
  { _tsTransformCounter :: Int
  , _tsBndrSubst        :: VarEnv.VarEnv CoreSyn.CoreBndr
  , _tsUniqSupply       :: UniqSupply.UniqSupply
  }
  
Data.Label.mkLabels [''TransformState]

type TransformSession m = ErrorT String (StateT TransformState m)
type TransformStep m    = [CoreContext] -> CoreSyn.CoreExpr -> RewriteM (TransformSession m) [CoreContext] CoreSyn.CoreExpr

emptyTransformState uniqSupply = TransformState 0 VarEnv.emptyVarEnv uniqSupply
