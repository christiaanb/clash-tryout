{-# LANGUAGE Arrows #-}
module ALU where

import CLaSH
import Data.Tuple.HT

dc = L

program =
  [ (H, L, H )
  , (L, L, L )
  , (L, H, dc)
  , (H, L, H )
  , (H, H, dc)
  ]

type Word = Unsigned D4

type RegAddr = Bit
type RegisterBankState = (Word,Word)

registerBank ::
  RegisterBankState
  -> (RegAddr, Bool, Word)
  -> (RegisterBankState, Word)
registerBank s (addr, we, d) = (s', o)
  where
    s' = case we of
      False -> s
      True  ->
        let (r0,r1) = s
            r0'     = case addr of L -> d; H -> r0
            r1'     = case addr of H -> d; L -> r1
        in (r0',r1')
    o = case we of
      False -> case addr of L -> fst s; H -> snd s
      True  -> 0
      
data AluOp = Add | Sub
alu Add = (+)
alu Sub = (-)

delayN s inp = (inp, s)

topEntity = proc (addr,we,op) -> do
  rec (t,z) <- delayN ^^^ (0,0)       -< (t',z')
      t'    <- registerBank ^^^ (0,1) -< (addr,we,z)
      z'    <- arr (uncurry3 alu)     -< (op, t', t)
  returnA -< t'
