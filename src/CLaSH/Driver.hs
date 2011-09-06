module CLaSH.Driver
  ( generateVHDL
  )
where

-- External Modules
import qualified Control.Monad.State.Strict as State
import qualified Data.Time.Clock as Clock
import qualified Data.Map as Map

-- GHC.API
import qualified CoreSyn
import qualified HscTypes
import qualified UniqSupply

-- Internal Modules
import CLaSH.Driver.Types
import CLaSH.Driver.Tools
import CLaSH.Desugar (desugar)
import CLaSH.Netlist (genNetlist)
import CLaSH.Netlist.GenVHDL (genVHDL)
import CLaSH.Normalize (normalize)
import CLaSH.Util.Pretty (pprString)
import CLaSH.Util.GHC (loadModules)
import CLaSH.Util (curLoc)

generateVHDL :: 
  String 
  -> IO ()
generateVHDL modName = do
  start <- Clock.getCurrentTime
  coreModGuts <- loadModules modName
  vhdl <- runDriverSession $ do
    let allBindings = concatMap (CoreSyn.flattenBinds . HscTypes.mg_binds) coreModGuts
    let topEntities = filter (isTopEntity . fst) allBindings
    case topEntities of
      [topEntity'] -> do
        let topEntity = fst topEntity'
        let globalBindings = Map.fromList allBindings
        globalBindings'           <- desugar    globalBindings  topEntity
        (normalized,netlistState) <- normalize  globalBindings' topEntity
        netlist                   <- genNetlist netlistState normalized topEntity
        let vhdl                  = map ((flip genVHDL) []) netlist
        return vhdl
      []          -> error $ $(curLoc) ++ "No 'topEntity' found"
      otherwise   -> error $ $(curLoc) ++ "Found multiple top entities: " ++
                             show (map fst topEntities)
  putStrLn $ concat vhdl
  return ()

runDriverSession ::
  DriverSession a 
  -> IO a
runDriverSession session = do
  uniqSupply <- State.liftIO $ UniqSupply.mkSplitUniqSupply 'z'
  State.evalStateT session (emptyDriverState uniqSupply)
