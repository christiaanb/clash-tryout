{-# LANGUAGE Arrows #-}
module Register where

import CLaSH

registerT :: Bit -> Bit -> (Bit,Bit)
registerT q d = (d,q)

topEntity :: Component Bit Bit
topEntity = register sysClock

register :: Clock -> Component Bit Bit
register clk = proc inp -> do
  outp <- component registerT L clk -< inp
  returnA -< outp

sysClock :: Clock
sysClock = ClockUp "sysClock" 1

