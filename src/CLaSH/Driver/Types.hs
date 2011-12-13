{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module CLaSH.Driver.Types
  ( DriverState(..)
  , DriverSession
  , drUniqSupply
  , emptyDriverState
  )
where

-- External Modules
import Control.Monad.State.Strict (StateT)
import Data.Label ((:->), lens)
import qualified Data.Label
import qualified Data.Label.PureM as Label
import Data.Map (Map,empty)

-- GHC API
import qualified CoreSyn
import qualified UniqSupply

-- Internal Modules
import CLaSH.Util (UniqSupply, MonadUnique(..), splitUniqSupply)

data DriverState = DriverState
  { _drUniqSupply :: UniqSupply.UniqSupply
  }

-- Derive record field accessors
Data.Label.mkLabels [''DriverState]

emptyDriverState uniqSupply = DriverState uniqSupply

type DriverSession = StateT DriverState IO

instance MonadUnique DriverSession where
  getUniqueSupplyM = do
    us <- Label.gets drUniqSupply
    let (us',us'') = splitUniqSupply us
    Label.puts drUniqSupply us''
    return us'
