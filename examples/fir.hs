{-# LANGUAGE Arrows, TemplateHaskell #-}
module FIR where

import CLaSH

type Word = Signed D16

fir hs pxs x = (xT, xT ** hs)
  where
    xT       = x +>> pxs
    as ** bs = vfoldl (+) 0 (vzipWith (*) as bs)

topEntity = (fir hs) ^^^ initFir
  where
    hs      = $(vTH [2,3,-2,(8::Word)])
    initFir = vcopyn d4 0

testInput      = [2,3,-2,(8::Word)]
expectedOutput = [4,12,1,(20::Word)]
