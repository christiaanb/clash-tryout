{-# LANGUAGE RecordWildCards #-}
module CLaSH.Util.GHC.LoadModules
  ( loadModules
  )
where

-- External Modules
import qualified GHC.Paths

-- GHC API
import qualified DynFlags
import qualified GHC
import qualified HscTypes
import qualified Panic

-- Internal Modules
import CLaSH.Util (curLoc)

loadModules :: String -> IO [HscTypes.ModGuts]
loadModules modName =
  GHC.defaultErrorHandler DynFlags.defaultLogAction $
    GHC.runGhc (Just GHC.Paths.libdir) $ do
      dflags <- GHC.getSessionDynFlags
      GHC.setSessionDynFlags $ dflags {GHC.simplPhases = 0}
      target <- GHC.guessTarget modName Nothing
      GHC.setTargets [target]
      ldRes <- GHC.load GHC.LoadAllTargets
      case ldRes of
        GHC.Succeeded -> do
          modGraph <- GHC.getModuleGraph
          let modGraph' = map disableOptimizationsFlags modGraph
          desugardMods <- mapM (\m -> parseModule m >>=
                                GHC.typecheckModule >>=
                                GHC.desugarModule) modGraph'
          return $ map GHC.coreModule desugardMods
        GHC.Failed -> Panic.pgmError $ $(curLoc) ++ "failed to load module: " ++ modName

parseModule :: GHC.GhcMonad m => GHC.ModSummary -> m GHC.ParsedModule
parseModule modSum = do
  (GHC.ParsedModule pmModSum pmParsedSource) <- GHC.parseModule modSum
  return (GHC.ParsedModule (disableOptimizationsFlags pmModSum) pmParsedSource)

disableOptimizationsFlags :: GHC.ModSummary -> GHC.ModSummary
disableOptimizationsFlags ms@(GHC.ModSummary {..}) = ms {GHC.ms_hspp_opts = dflags}
  where
    dflags = ms_hspp_opts {DynFlags.optLevel = 0, GHC.simplPhases = 0}
