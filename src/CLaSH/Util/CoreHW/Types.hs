{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module CLaSH.Util.CoreHW.Types
  ( CoreContext (..)
  , CoreBinding
  , TransformSession
  , TransformStep
  , tsTransformCounter
  , tsUniqSupply
  , emptyTransformState
  )
where

-- External Modules
import Control.Monad.State.Strict (StateT)
import Control.Monad.Error        (ErrorT)
import qualified Data.Label
import qualified Data.Label.PureM as Label
import Language.KURE              (RewriteM)

-- GHC API
import qualified VarEnv

-- Internal Modules
import CLaSH.Util                 (UniqSupply, MonadUnique(..), splitUniqSupply)
import CLaSH.Util.CoreHW.Syntax   (Var, Term, TyVar)

type CoreBinding = (Var, Term)

data CoreContext = AppFirst
                 | TyAppFirst
                 | LetBinding   [Var]
                 | LetBody      [Var]
                 | LambdaBody   Var
                 | TyLambdaBody TyVar
                 | CaseAlt
                 | Other
  deriving (Show)

data TransformState = TransformState
  { _tsTransformCounter :: Int
  , _tsUniqSupply       :: UniqSupply
  }

Data.Label.mkLabels [''TransformState]

type TransformSession m = ErrorT String (StateT TransformState m)
type TransformStep m    = [CoreContext] -> Term -> RewriteM (TransformSession m) [CoreContext] Term

emptyTransformState uniqSupply = TransformState 0 uniqSupply

instance Monad m => MonadUnique (TransformSession m) where
  getUniqueSupplyM = do
    us <- Label.gets tsUniqSupply
    let (us',us'') = splitUniqSupply us
    Label.puts tsUniqSupply us''
    return us'
