{-# LANGUAGE NoMonomorphismRestriction, Arrows #-}
module ALU where

import CLaSH
import Data.Tuple.HT

data Opcode = And | Xor | Or

alu opc a b = case opc of
  And -> andB a $ notB b
  Xor -> xorB a $ notB b
  Or  -> orB  a $ notB b

topEntity :: Component (Opcode, Bit, Bit) Bit    
topEntity = proc inp -> do
  outp <- arr (uncurry3 alu) -< inp
  returnA -< outp
