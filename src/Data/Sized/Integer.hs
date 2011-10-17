{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DatatypeContexts #-}
module Data.Sized.Integer
  ( Signed(..)
  , Unsigned(..)
  , Index(..)
  , HWBits(..)
  ) where

import qualified Data.Bits as B
import Types

data (PositiveT nT)    => Signed nT   = Signed Integer

data (PositiveT nT)    => Unsigned nT = Unsigned Integer

data (PositiveT upper) => Index upper = Index Integer

class (B.Bits a) => HWBits a where
  type ShiftSize a :: *
  shiftL :: a -> Index (ShiftSize a) -> a
  shiftR :: a -> Index (ShiftSize a) -> a
