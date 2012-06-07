{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.Builtin
  ( module Control.Arrow
  , module Control.Monad.Fix
  , module Data.Bits
  , module Data.Sized.Integer
  , module Data.Sized.Vector
  , module Data.Sized.Unsigned
  , module Data.Sized.Signed
  , module Language.Haskell.TH.Lift
  , module Types

  , Bit (..)
  , andB
  , orB
  , xorB
  , notB

  , Clock(..)
  , Component
  , component
  , (^^^)
  , blockRam
  , defaultClock
  , run
  , runWithDefault
  )
where

-- External Modules
import Control.Arrow (Arrow,arr,first,ArrowLoop,loop,(>>>),returnA)
import Control.Category (Category,(.),id)
import Control.Monad.Fix (mfix)
import Data.Bits hiding (shiftL,shiftR)
import qualified Data.Set as Set
import Debug.Trace (trace)
import Language.Haskell.TH.Lift
import Prelude hiding (id,(.))
import qualified Prelude as P
import Types

-- Internal Modules
import Data.Sized.Integer(HWBits(..))
import Data.Sized.Signed
import Data.Sized.Unsigned
import Data.Sized.Vector

data Bit = H | L
  deriving (Eq,Show)

deriveLift ''Bit

H `andB` H = H
_ `andB` _ = L

L `orB` L = L
_ `orB` _ = H

H `xorB` L = H
L `xorB` H = H
_ `xorB` _ = L

notB L = H
notB H = L

data Clock = ClockUp String Int | ClockDown String Int
  deriving (Eq,Show)

instance Ord Clock where
  compare (ClockUp   s1 i1) (ClockUp   s2 i2) = case compare i1 i2 of EQ -> compare s1 s2; x -> x
  compare (ClockUp   s1 i1) (ClockDown s2 i2) = case compare i1 i2 of EQ -> compare s1 s2; x -> x
  compare (ClockDown s1 i1) (ClockUp   s2 i2) = case compare i1 i2 of EQ -> compare s1 s2; x -> x
  compare (ClockDown s1 i1) (ClockDown s2 i2) = case compare i1 i2 of EQ -> compare s1 s2; x -> x

data Component i o = C
  { domain :: Set.Set Clock
  , exec   :: Clock -> i -> (o, Component i o)
  }

instance Category Component where
  (C { domain = cdA, exec = g}) . (C {domain = cdB, exec = f}) =
     C { domain = Set.union cdA cdB
       , exec   = \clk b -> let (c,f') = f clk b
                                (d,g') = g clk c
                            in (d, g'.f')
       }
  id = arr id

instance Arrow Component where
  arr f    = C { domain = Set.empty
               , exec   = \clk b -> (f b, arr f)
               }
  first af = af { exec  = \clk (b,d) -> let (c,f') = (exec af) clk b
                                        in ((c,d), first f')
                }
instance ArrowLoop Component where
   loop af = af { exec = (\clk i -> let ((c,d), f') = (exec af) clk (i, d)
                                    in (c, loop f'))
                }

component :: (s -> i -> (s,o)) -> s -> Clock -> Component i o
component f initS clk = C { domain = Set.singleton clk
                          , exec = \clk' i -> let (s,o)            = f initS i
                                                  s' | clk == clk' = s
                                                     | otherwise   = initS
                                              in (o, component f s' clk)
                          }
{-# INLINE (^^^) #-}
(^^^) :: (s -> i -> (s,o)) -> s -> Component i o
f ^^^ initS = component f initS defaultClock

{-# INLINE defaultClock #-}
defaultClock :: Clock
defaultClock = ClockUp "defaultClock" 1

blockRam ::
  forall nT a
  . PositiveT nT
  => nT
  -> Clock
  -> Component (a,Unsigned (Log2Ceil nT), Unsigned (Log2Ceil nT), Bool) a
blockRam bSize clk = bram ^^^ bInit
  where
    bram :: (Vector nT a,a) -> (a, Unsigned (Log2Ceil nT), Unsigned (Log2Ceil nT), Bool) -> ((Vector nT a,a), a)
    bram (ram,outp) (din,wr,rd,we) = ((ram',outp'),outp)
      where
        ram' | we        = vreplace ram wr din
             | otherwise = ram
        outp'            = ram!rd

    bInit :: (Vector nT a,a)
    bInit = (initErrors,error "blockRam: reading undefined initial value")

    initErrors :: Vector nT a
    initErrors = vmap (\i -> error $ "blockRam: reading undefined unitial value at location: " ++ show i) (viterate (+1) 0)

run :: Component i o -> [(Clock,i)] -> [o]
run (C _ hw) inps = go hw inps
  where
    go f []     = []
    go f ((c,i):is) = let (o,C _ f') = f c i
                      in o:(go f' is)

runWithDefault :: Component i o -> [i] -> [o]
runWithDefault c@(C clks _) =
  case (Set.size clks) of
    0 -> run c . zip (repeat defaultClock)
    1 -> let clk = Set.findMin clks
         in run c . zip (repeat clk)
    n -> let minClk = Set.findMin clks
         in  trace ("== Warning ==\nRunning multi-clock(" ++ show n ++ ") design with one clock: " ++ show minClk) $ run c . zip (repeat minClk)
