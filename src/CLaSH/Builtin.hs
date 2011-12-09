{-# LANGUAGE Arrows #-}
module CLaSH.Builtin
  ( module Control.Arrow
  , module Control.Monad.Fix
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
  , defaultClock
  , run
  , runWithDefault
  )
where

-- External Modules
import Control.Arrow (Arrow,arr,first,ArrowLoop,loop,(>>>),returnA)
import Control.Category (Category,(.),id)
import Control.Monad.Fix (mfix)
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
  deriving (Eq,Ord,Show)

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

run :: Component i o -> [(Clock,i)] -> [o]
run (C _ hw) inps = go hw inps
  where
    go f []     = []
    go f ((c,i):is) = let (o,C _ f') = f c i
                      in o:(go f' is)

runWithDefault :: Component i o -> [i] -> [o]
runWithDefault c@(C clks _) =
  if (Set.size clks) < 2 then
    run c . zip (repeat defaultClock)
  else
    trace "== Warning ==\nRunning multi-clock design with only \"defaultClock\"\n" $ run c . zip (repeat defaultClock)
