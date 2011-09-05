{-# LANGUAGE Arrows #-}
module Register where

import CLaSH

registerT :: Bit -> Bit -> (Bit,Bit)
registerT q d = (d,q)

topEntity :: Component Bit Bit
topEntity = proc inp -> do
  outp <- registerT ^^^ L -< inp
  returnA -< outp

sysClock :: Clock
sysClock = ClockUp "sysClock" 1

