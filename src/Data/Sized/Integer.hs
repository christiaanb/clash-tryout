{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE DatatypeContexts #-}

module Data.Sized.Integer
  ( Signed(..)
  , Unsigned(..)
  , HWBits(..)
  ) where

import qualified Data.Bits as B
import Types

data (PositiveT nT)    => Signed nT   = Signed Integer

data (PositiveT nT)    => Unsigned nT = Unsigned Integer

class (B.Bits a) => HWBits a where
  type ShiftSize a :: *
  shiftL :: a -> Unsigned (Log2Ceil (ShiftSize a)) -> a
  shiftR :: a -> Unsigned (Log2Ceil (ShiftSize a)) -> a
