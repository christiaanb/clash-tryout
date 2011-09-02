{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module CLaSH.Util.Core.Types
  ( CoreBinding
  , TypedThing(..)
  , CoreContext(..)
  , TransformState(..)
  , TransformSession
  , TransformStep
  , tsTransformCounter
  , tsBndrSubst
  , tsUniqSupply
  , emptyTransformState
  )
where

-- External Modules
import Control.Monad.State.Strict (StateT)
import Control.Monad.Error (ErrorT)
import qualified Data.Label
import Language.KURE (RewriteM)

-- GHC API
import qualified CoreSyn
import qualified CoreUtils
import qualified Id
import qualified Outputable
import qualified Type
import qualified UniqSupply
import qualified VarEnv

type CoreBinding = (CoreSyn.CoreBndr, CoreSyn.CoreExpr)

class Outputable.Outputable t => TypedThing t where
  getType :: t -> Maybe Type.Type
  
instance TypedThing CoreSyn.CoreExpr where
  getType (CoreSyn.Type _) = Nothing
  getType expr             = Just $ CoreUtils.exprType expr
  
instance TypedThing CoreSyn.CoreBndr where
  getType = return . Id.idType
  
instance TypedThing Type.Type where
  getType = return

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
