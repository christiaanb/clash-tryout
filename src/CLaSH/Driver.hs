module CLaSH.Driver
  ( generateVHDL
  )
where

-- External Modules
import qualified Control.Monad.State as State
import qualified Data.Time.Clock as Clock
import qualified Data.Map as Map
import Data.Label.PureM

-- GHC.API
import qualified CoreSyn
import qualified HscTypes

-- Internal Modules
import CLaSH.Driver.Types
import CLaSH.Driver.Tools
import CLaSH.Normalize (normalize)
import CLaSH.Util.Pretty
import CLaSH.Util.GHC (loadModules)
import CLaSH.Util

generateVHDL :: String -> IO ()
generateVHDL modName = do
  start <- Clock.getCurrentTime
  coreModGuts <- loadModules modName
  vhdl <- runDriverSession $ do
    let allBindings = concatMap (CoreSyn.flattenBinds . HscTypes.mg_binds) coreModGuts
    let topEntities = filter (isTopEntity . fst) allBindings
    case topEntities of
      [topEntity] -> do
        puts tsBindings $ Map.fromList allBindings
        normalized <- normalize (Map.fromList allBindings) (fst topEntity)
        return normalized
      []          -> $(errorCurLoc "No 'topEntity' found")
      otherwise   -> error $ $(curLoc) ++ "Found multiple top entities: " ++
                             show (map fst topEntities)
  putStrLn $ pprString vhdl
  return ()

runDriverSession :: DriverSession a -> IO a
runDriverSession session = do
  State.evalStateT session emptyDriverState
