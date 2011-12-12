{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE FlexibleContexts    #-}

module Data.Sized.Signed
  ( Signed
  , resizeSigned
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import qualified Data.Bits as B
import Types
import Types.Data.Num.Decimal.Literals.TH

import Data.Sized.Integer

instance PositiveT nT => Lift (Signed nT) where
  lift (Signed i) = sigE [| (Signed i) |] (decSignedT (fromIntegerT (undefined :: nT)))

decSignedT :: Integer -> Q Type
decSignedT n = appT (conT (''Signed)) (decLiteralT n)

resizeSigned :: (PositiveT nT, PositiveT nT') => Signed nT -> Signed nT'
resizeSigned a = fromInteger (toInteger a)

sizeT :: Signed nT
      -> nT
sizeT _ = undefined

mask :: forall nT . PositiveT nT
     => nT
     -> Integer
mask _ = B.bit (fromIntegerT (undefined :: nT)) - 1

signBit :: forall nT . PositiveT nT
        => nT
        -> Int
signBit _ = fromIntegerT (undefined :: nT) - 1

isNegative :: forall nT . PositiveT nT
           => Signed nT
           -> Bool
isNegative (Signed x) =
    B.testBit x $ signBit (undefined :: nT)

instance PositiveT nT => Eq (Signed nT) where
  (==) = eqSigned
  (/=) = neqSigned

eqSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
  -> Bool
eqSigned  (Signed x) (Signed y) = x == y

neqSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
  -> Bool
neqSigned (Signed x) (Signed y) = x /= y

instance PositiveT nT => Show (Signed nT) where
    showsPrec prec n =
        showsPrec prec $ toInteger n

instance PositiveT nT => Read (Signed nT) where
    readsPrec prec str =
        [ (fromInteger n, str)
        | (n, str) <- readsPrec prec str ]

instance PositiveT nT => Ord (Signed nT) where
    a `compare` b = toInteger a `compare` toInteger b

instance PositiveT nT => Bounded (Signed nT) where
    minBound = Signed $ negate $ 1 `B.shiftL` (fromIntegerT (undefined :: nT) - 1)
    maxBound = Signed $ (1 `B.shiftL` (fromIntegerT (undefined :: nT) - 1)) - 1

instance PositiveT nT => Enum (Signed nT) where
    succ x
       | x == maxBound  = error $ "Enum.succ{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `succ' of maxBound"
       | otherwise      = x + 1
    pred x
       | x == minBound  = error $ "Enum.succ{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `pred' of minBound"
       | otherwise      = x - 1

    fromEnum (Signed x)
        | x > toInteger (maxBound :: Int) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed greater than maxBound :: Int"
        | x < toInteger (minBound :: Int) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed smaller than minBound :: Int"
        | otherwise =
            fromInteger x
    toEnum x
        | x' > toInteger (maxBound :: Signed nT) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed greater than maxBound :: Signed " ++ show (fromIntegerT (undefined :: nT))
        | x' < toInteger (minBound :: Signed nT) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed smaller than minBound :: Signed " ++ show (fromIntegerT (undefined :: nT))
        | otherwise =
            fromInteger x'
            where x' = toInteger x

instance PositiveT nT => Num (Signed nT) where
  (+)         = plusSigned
  (-)         = minSigned
  (*)         = timesSigned
  negate      = negateSigned
  fromInteger = signedFromInteger
  abs         = absSigned
  signum      = signumSigned

plusSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
  -> Signed nT
plusSigned (Signed a) (Signed b) = signedFromInteger $ (a + b)

minSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
  -> Signed nT
minSigned a b = a + (negateSigned b)

timesSigned ::
  forall nT
  . PositiveT nT
  => Signed nT
  -> Signed nT
  -> Signed nT
timesSigned s1@(Signed a) s2@(Signed b)
  | a * b > toInteger (maxBound :: Signed nT)
  , (isNegative s1) `xnor` (isNegative s2) = signedFromInteger $ (a*b) B..&. (B.bit (fromIntegerT (undefined :: nT) - 1) - 1)
  | a * b < (negate $ 1 `B.shiftL` (fromIntegerT (undefined :: nT) - 1)) = signedFromInteger $ (a * b)
  | otherwise                                                            = signedFromInteger $ (a * b)
  where
    xnor False False = True
    xnor True  True  = True
    xnor _     _     = False

negateSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
negateSigned s@(Signed n) =
  signedFromInteger $ (n `B.xor` mask (sizeT s)) + 1

signedFromInteger ::
  forall nT
  . PositiveT nT
  => Integer
  -> Signed nT
signedFromInteger n
  | n > 0
  = Signed $ n B..&. mask (undefined :: nT)
  | n < 0
  = negateSigned $ signedFromInteger $ negate n
  | otherwise
  = Signed 0

absSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
absSigned s | isNegative s = negateSigned s
            | otherwise    = s

signumSigned ::
  PositiveT nT
  => Signed nT
  -> Signed nT
signumSigned (Signed 0)       = Signed 0
signumSigned s | isNegative s = signedFromInteger (-1)
               | otherwise    = signedFromInteger 1

instance PositiveT nT => Real (Signed nT) where
    toRational n = toRational $ toInteger n

instance PositiveT nT => Integral (Signed nT) where
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
    toInteger s@(Signed x) =
        if isNegative s
           then let Signed x' = negate s in negate x'
           else x

instance PositiveT nT => B.Bits (Signed nT) where
    (Signed a) .&. (Signed b) = Signed $ a B..&. b
    (Signed a) .|. (Signed b) = Signed $ a B..|. b
    (Signed a) `xor` Signed b = Signed $ a `B.xor` b
    complement (Signed x) = Signed $ x `B.xor` mask (undefined :: nT)
    (Signed x) `shiftL` b
      | b < 0 = error $ "Bits.shiftL{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to shift by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) B..&. (x `B.shiftL` b)
    s@(Signed x) `shiftR` b
      | b < 0 = error $ "Bits.shiftR{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to shift by negative amount"
      | isNegative s =
        Signed $ mask (undefined :: nT) B..&.
            ((x `B.shiftR` b) B..|. (mask (undefined :: nT) `B.shiftL` (fromIntegerT (undefined :: nT) - b)))
      | otherwise =
        Signed $ (mask (undefined :: nT)) B..&. (x `B.shiftR` b)
    (Signed a) `rotateL` b
      | b < 0 =
        error $ "Bits.rotateL{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) B..&.
            ((a `B.shiftL` b) B..|. (a `B.shiftR` (fromIntegerT (undefined :: nT) - b)))
    (Signed a) `rotateR` b
      | b < 0 =
        error $ "Bits.rotateR{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) B..&.
            ((a `B.shiftR` b) B..|. (a `B.shiftL` (fromIntegerT (undefined :: nT) - b)))
    bitSize _ = fromIntegerT (undefined :: nT)
    isSigned _ = True

instance PositiveT nT => HWBits (Signed nT) where
  type ShiftSize (Signed nT) = nT
  a `shiftL` (Unsigned b) = a `B.shiftL` (fromIntegral b)
  a `shiftR` (Unsigned b) = a `B.shiftR` (fromIntegral b)
