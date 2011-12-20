{-# LANGUAGE Arrows #-}
module BRAMtest where

import CLaSH

whenValid :: Unsigned D2 -> Unsigned D64 -> (Unsigned D2, Unsigned D64)
whenValid 0 x = (1,0)
whenValid 1 x = (2,0)
whenValid n x = (n,x)

topEntity = proc inp -> do
  outp    <- (blockRam d128 defaultClock) -< inp
  outp'   <- whenValid ^^^ 0 -< outp
  returnA -< outp'

testInput :: [(Unsigned D64, Unsigned D7, Unsigned D7, Bit)]
testInput = [(1,2,2,H),(8,2,2,H),(9,2,2,H),(3,2,2,H)]

expectedOutput :: [Unsigned D64]
expectedOutput = [0,0,1,8]
