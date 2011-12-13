module CLaSH.Driver.PrepareBinding
  ( prepareBinding
  )
where

-- External Modules
import Data.Map (Map)

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.CoreHW        (coreToCoreHW)
import CLaSH.Desugar       (desugar)
import CLaSH.Driver.Types
import CLaSH.Util.CoreHW   (Var,Term)

prepareBinding ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> CoreSyn.CoreBndr
  -> DriverSession (Map Var Term)
prepareBinding globalBindings  bndr = do
  globalBindings'           <- desugar       globalBindings  bndr
  coreHWBindings            <- coreToCoreHW  globalBindings' bndr
  return coreHWBindings
