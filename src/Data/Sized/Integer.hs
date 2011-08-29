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

newtype (PositiveT nT)    => Signed nT   = Signed Integer

newtype (PositiveT nT)    => Unsigned nT = Unsigned Integer

newtype (PositiveT upper) => Index upper = Index Integer

class (B.Bits a) => HWBits a where
  type ShiftSize a :: *
  shiftL :: a -> Index (ShiftSize a) -> a
  shiftR :: a -> Index (ShiftSize a) -> a
