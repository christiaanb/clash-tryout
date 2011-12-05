{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}

module Data.Sized.Unsigned
    ( Unsigned
    , resizeUnsigned
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import qualified Data.Bits as B
import Types
import Types.Data.Num.Decimal.Literals.TH

import Data.Sized.Integer

instance PositiveT nT => Lift (Unsigned nT) where
  lift (Unsigned i) = sigE [| (Unsigned i) |] (decUnsignedT (fromIntegerT (undefined :: nT)))

decUnsignedT :: Integer -> Q Type
decUnsignedT n = appT (conT (''Unsigned)) (decLiteralT n)

resizeUnsigned :: (PositiveT nT, PositiveT nT') => Unsigned nT -> Unsigned nT'
resizeUnsigned a = fromInteger (toInteger a)

sizeT :: Unsigned nT
      -> nT
sizeT _ = undefined

mask :: forall nT . PositiveT nT
     => nT
     -> Integer
mask _ = B.bit (fromIntegerT (undefined :: nT)) - 1

instance PositiveT nT => Eq (Unsigned nT) where
  (==) = eqUnsigned
  (/=) = neqUnsigned

eqUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
  -> Bool
eqUnsigned (Unsigned x) (Unsigned y) = x == y

neqUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
  -> Bool
neqUnsigned (Unsigned x) (Unsigned y) = x /= y

instance PositiveT nT => Show (Unsigned nT) where
  showsPrec prec n =
      showsPrec prec $ toInteger n

instance PositiveT nT => Read (Unsigned nT) where
    readsPrec prec str =
        [ (fromInteger n, str)
        | (n, str) <- readsPrec prec str ]

instance PositiveT nT => Ord (Unsigned nT) where
    a `compare` b = toInteger a `compare` toInteger b

instance PositiveT nT => Bounded (Unsigned nT) where
    minBound = 0
    maxBound = Unsigned $ (1 `B.shiftL` (fromIntegerT (undefined :: nT))) - 1

instance PositiveT nT => Enum (Unsigned nT) where
    succ x
       | x == maxBound  = error $ "Enum.succ{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `succ' of maxBound"
       | otherwise      = x + 1
    pred x
       | x == minBound  = error $ "Enum.succ{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `pred' of minBound"
       | otherwise      = x - 1

    fromEnum (Unsigned x)
        | x > toInteger (maxBound :: Int) =
            error $ "Enum.fromEnum{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Unsigned greater than maxBound :: Int"
        | x < toInteger (minBound :: Int) =
            error $ "Enum.fromEnum{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Unsigned smaller than minBound :: Int"
        | otherwise =
            fromInteger x
    toEnum x
        | x > fromIntegral (maxBound :: Unsigned nT) =
            error $ "Enum.fromEnum{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Unsigned greater than maxBound :: Unsigned " ++ show (fromIntegerT (undefined :: nT))
        | x < fromIntegral (minBound :: Unsigned nT) =
            error $ "Enum.fromEnum{Unsigned " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Unsigned smaller than minBound :: Unsigned " ++ show (fromIntegerT (undefined :: nT))
        | otherwise =
            fromInteger $ toInteger x

instance PositiveT nT => Num (Unsigned nT) where
  (+)         = plusUnsigned
  (-)         = minUnsigned
  (*)         = timesUnsigned
  negate      = negateUnsigned
  fromInteger = unsignedFromInteger
  abs         = absUnsigned
  signum      = signumUnsigned

plusUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
  -> Unsigned nT
plusUnsigned (Unsigned a) (Unsigned b) = unsignedFromInteger $ (a + b)

minUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
  -> Unsigned nT
minUnsigned (Unsigned a) (Unsigned b) = unsignedFromInteger $ (a - b)

timesUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
  -> Unsigned nT
timesUnsigned (Unsigned a) (Unsigned b) = unsignedFromInteger $ (a * b)

negateUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
negateUnsigned s@(Unsigned n) =
  unsignedFromInteger $ (n `B.xor` mask (sizeT s)) + 1

unsignedFromInteger ::
  forall nT
  . PositiveT nT
  => Integer
  -> Unsigned nT
unsignedFromInteger n
  | n > 0
  = Unsigned $ n B..&. mask (undefined :: nT)
  | n < 0
  = negateUnsigned $ unsignedFromInteger $ negate n
  | otherwise
  = Unsigned 0

absUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
absUnsigned u = u

signumUnsigned ::
  PositiveT nT
  => Unsigned nT
  -> Unsigned nT
signumUnsigned (Unsigned 0) = Unsigned 0
signumUnsigned _            = Unsigned 1

instance PositiveT nT => Real (Unsigned nT) where
    toRational n = toRational $ toInteger n

instance PositiveT nT => Integral (Unsigned nT) where
    a `quot` b =
        fromInteger $ toInteger a `quot` toInteger b
    a `rem` b =
        fromInteger $ toInteger a `rem` toInteger b
    a `div` b =
        fromInteger $ toInteger a `div` toInteger b
    a `mod` b =
        fromInteger $ toInteger a `mod` toInteger b
    a `quotRem` b =
        let (quot, rem) = toInteger a `quotRem` toInteger b
        in (fromInteger quot, fromInteger rem)
    a `divMod` b =
        let (div, mod) = toInteger a `divMod` toInteger b
        in (fromInteger div, fromInteger mod)
    toInteger s@(Unsigned x) = x

instance PositiveT nT => B.Bits (Unsigned nT) where
    (Unsigned a) .&. (Unsigned b) = Unsigned $ a B..&. b
    (Unsigned a) .|. (Unsigned b) = Unsigned $ a B..|. b
    (Unsigned a) `xor` Unsigned b = Unsigned $ a `B.xor` b
    complement (Unsigned x) = Unsigned $ x `B.xor` mask (undefined :: nT)
    s@(Unsigned x) `shiftL` b
      | b < 0 = error $ "Bits.shiftL{Unsigned " ++ show (B.bitSize s) ++ "}: tried to shift by negative amount"
      | otherwise =
        Unsigned $ mask (undefined :: nT) B..&. (x `B.shiftL` b)
    s@(Unsigned x) `shiftR` b
      | b < 0 = error $ "Bits.shiftR{Unsigned " ++ show (B.bitSize s) ++ "}: tried to shift by negative amount"
      | otherwise =
        Unsigned $ (x `B.shiftR` b)
    s@(Unsigned x) `rotateL` b
      | b < 0 =
        error $ "Bits.rotateL{Unsigned " ++ show (B.bitSize s) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Unsigned $ mask (undefined :: nT) B..&.
            ((x `B.shiftL` b) B..|. (x `B.shiftR` (B.bitSize s - b)))
    s@(Unsigned x) `rotateR` b
      | b < 0 =
        error $ "Bits.rotateR{Unsigned " ++ show (B.bitSize s) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Unsigned $ mask (undefined :: nT) B..&.
            ((x `B.shiftR` b) B..|. (x `B.shiftL` (B.bitSize s - b)))
    bitSize _ = fromIntegerT (undefined :: nT)
    isSigned _ = False

instance PositiveT nT => HWBits (Unsigned nT) where
  type ShiftSize (Unsigned nT) = nT
  a `shiftL` (Unsigned b) = a `B.shiftL` (fromIntegral b)
  a `shiftR` (Unsigned b) = a `B.shiftR` (fromIntegral b)
