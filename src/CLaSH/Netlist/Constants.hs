module CLaSH.Netlist.Constants
  ( builtinIds
  )
where

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Netlist.Types
import CLaSH.Netlist.Tools

builtinIds :: [String]
builtinIds = ["xorB","andB","notB","orB","delay","unpackCString#","I#",
  "+>>","vlast","Int#", "singleton", "empty",
  "+>","smallInteger","eqUnsigned","neqUnsigned","plusUnsigned",
  "minUnsigned", "timesUnsigned", "negateUnsigned", "unsignedFromInteger",
  "absUnsigned", "signumUnsigned"]
