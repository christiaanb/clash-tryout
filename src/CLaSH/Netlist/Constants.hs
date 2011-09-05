module CLaSH.Netlist.Constants
  ( builtinIds
  , builtinBuilders
  )
where
  
-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Netlist.Types
import CLaSH.Netlist.Tools

builtinIds :: [String]
builtinIds = ["xorB","andB","notB","delay","unpackCString#","I#"]

type BuiltinBuilder =
  CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
  
type BuilderTable = [(String, (Int, BuiltinBuilder))]

builtinBuilders :: BuilderTable
builtinBuilders =
  [ ("xorB", (2, genBinaryOperator Xor))
  , ("andB", (2, genBinaryOperator And))
  , ("notB", (1, genUnaryOperator  Neg))
  ]
