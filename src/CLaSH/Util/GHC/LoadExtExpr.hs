module CLaSH.Util.GHC.LoadExtExpr
  ( loadExtExpr
  )
where

import qualified CoreSyn
import qualified DynFlags
import qualified GHC
import qualified GHC.Paths
import qualified HscTypes
import qualified IdInfo
import qualified IfaceSyn
import qualified LoadIface
import qualified Maybes
import qualified MonadUtils
import qualified Outputable
import qualified TcIface
import qualified TcRnMonad
import qualified TcRnTypes
import qualified UniqFM
import qualified Var

loadExtExpr :: GHC.Name -> IO (Maybe CoreSyn.CoreExpr)
loadExtExpr name =
  GHC.defaultErrorHandler DynFlags.defaultLogAction $ do
    GHC.runGhc (Just GHC.Paths.libdir) $ do
      dflags <- GHC.getSessionDynFlags
      GHC.setSessionDynFlags dflags
      nameMod <- GHC.findModule (GHC.moduleName $ GHC.nameModule name) Nothing
      hscEnv <- GHC.getSession
      let localEnv  = TcRnTypes.IfLclEnv nameMod (Outputable.text "loadExtExpr") UniqFM.emptyUFM  UniqFM.emptyUFM
      let globalEnv = TcRnTypes.IfGblEnv Nothing
      MonadUtils.liftIO $ TcRnMonad.initTcRnIf 'r' hscEnv globalEnv localEnv $ do 
        iface <- LoadIface.findAndReadIface (Outputable.text "loadExtExpr") nameMod False
        case iface of
          Maybes.Succeeded (modInfo, modPath) -> do
            let (modPrints,modDefs) = unzip $ HscTypes.mi_decls modInfo
            let nameFun = GHC.getOccName name
            let modDef = filter ((== nameFun) . IfaceSyn.ifName) modDefs
            case modDef of
              [nameModDef] -> loadDecl nameModDef
              _ -> return Nothing
          Maybes.Failed _ -> return Nothing

loadDecl :: IfaceSyn.IfaceDecl -> TcRnTypes.IfL (Maybe CoreSyn.CoreExpr)
loadDecl decl = do
  tyThing <- TcIface.tcIfaceDecl False decl
  case tyThing of
    GHC.AnId _id -> do
      let unfolding = IdInfo.unfoldingInfo $ Var.idInfo _id
      case unfolding of
        (CoreSyn.CoreUnfolding e _ _ _ _ _ _ _ _) -> return $ Just e
        _ -> return Nothing
    _ -> return Nothing
