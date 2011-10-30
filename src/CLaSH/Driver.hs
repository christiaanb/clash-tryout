module CLaSH.Driver
  ( generateVHDL
  )
where

-- External Modules
import qualified Control.Monad.State.Strict as State
import qualified Data.Time.Clock as Clock
import qualified Data.Label.PureM as Label
import qualified Data.Map as Map
import qualified System.Directory as Directory
import qualified System.FilePath as FilePath
import qualified System.IO as IO

-- GHC.API
import qualified CoreSyn
import qualified HscTypes
import qualified UniqSupply

-- Internal Modules
import CLaSH.CoreHW                   (coreToCoreHW)
import CLaSH.Driver.Types
import CLaSH.Driver.Tools
import CLaSH.Desugar                  (desugar)
import CLaSH.Netlist                  (genNetlist)
import CLaSH.Netlist.GenVHDL          (genVHDL)
import CLaSH.Normalize                (normalize)
import CLaSH.Util.CoreHW              (termType)
import CLaSH.Util.Pretty              (pprString)
import CLaSH.Util.GHC                 (loadModules)
import CLaSH.Util                     (curLoc)

generateVHDL ::
  String
  -> IO ()
generateVHDL modName = do
  start <- Clock.getCurrentTime
  coreModGuts <- loadModules modName
  (top,vhdl) <- runDriverSession $ do
    let allBindings = concatMap (CoreSyn.flattenBinds . HscTypes.mg_binds) coreModGuts
    let topEntities = filter (isTopEntity . fst) allBindings
    case topEntities of
      [topEntity'] -> do
        let topEntity = fst topEntity'
        let globalBindings = Map.fromList allBindings
        globalBindings'           <- desugar      globalBindings  topEntity
        coreHWBindings            <- coreToCoreHW globalBindings' topEntity
        (normalized,netlistState) <- normalize    coreHWBindings  topEntity
        netlist                   <- genNetlist   netlistState    normalized topEntity
        let vhdl                  = map ((flip genVHDL) ["work.all"]) netlist
        --let vhdl = normalized
        return (topEntity,vhdl)
      []          -> error $ $(curLoc) ++ "No 'topEntity' found"
      otherwise   -> error $ $(curLoc) ++ "Found multiple top entities: " ++
                             show (map fst topEntities)
  let dir = "./vhdl/" ++ (show top) ++ "/"
  prepareDir dir
  mapM_ (writeVHDL dir) vhdl
  end <- Clock.getCurrentTime
  putStrLn $ "\nTotal compilation tooks: " ++ show (Clock.diffUTCTime end start)
  return ()

runDriverSession ::
  DriverSession a
  -> IO a
runDriverSession session = do
  uniqSupply <- State.liftIO $ UniqSupply.mkSplitUniqSupply 'z'
  State.evalStateT session (emptyDriverState uniqSupply)

-- | Prepares the directory for writing VHDL files. This means creating the
--   dir if it does not exist and removing all existing .vhdl files from it.
prepareDir :: String -> IO ()
prepareDir dir = do
  -- Create the dir if needed
  Directory.createDirectoryIfMissing True dir
  -- Find all .vhdl files in the directory
  files <- Directory.getDirectoryContents dir
  let to_remove = filter ((==".vhdl") . FilePath.takeExtension) files
  -- Prepend the dirname to the filenames
  let abs_to_remove = map (FilePath.combine dir) to_remove
  -- Remove the files
  mapM_ Directory.removeFile abs_to_remove

writeVHDL :: String -> (String, String) -> IO ()
writeVHDL dir (name, vhdl) = do
  -- Find the filename
  let fname = dir ++ name ++ ".vhdl"
  -- Write the file
  handle <- IO.openFile fname IO.WriteMode
  IO.hPutStrLn handle "-- Automatically generated VHDL"
  IO.hPutStr handle vhdl
  IO.hClose handle
