{-# LANGUAGE Arrows #-}
module Register where

import CLaSH

registerT :: Bit -> Bit -> (Bit,Bit)
registerT q d = (d,q)

topEntity :: Component Bit (Maybe Bit)
topEntity = proc inp -> do
  outp <- component registerT L (ClockUp 1) -< inp
  returnA -< (Just outp)
