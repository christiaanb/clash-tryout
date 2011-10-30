module CLaSH.Util.GHC.LoadExtExpr
  ( loadExtExpr
  )
where

import qualified Class
import qualified CoreSyn
import qualified DataCon
import qualified DynFlags
import qualified FastString
import qualified GHC
import qualified GHC.Paths
import qualified HscTypes
import qualified Id
import qualified IdInfo
import qualified IfaceSyn
import qualified LoadIface
import qualified Maybes
import qualified MkCore
import qualified MonadUtils
import qualified Outputable
import qualified TcIface
import qualified TcRnMonad
import qualified TcRnTypes
import qualified TcType
import qualified Type
import qualified UniqFM
import qualified UniqSupply
import qualified Var

loadExtExpr :: GHC.Name -> IO (Maybe CoreSyn.CoreExpr)
loadExtExpr name = do
  uniqSupply <- UniqSupply.mkSplitUniqSupply 'p'
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
              [nameModDef] -> loadDecl uniqSupply nameModDef
              _ -> return Nothing
          Maybes.Failed _ -> return Nothing

loadDecl :: UniqSupply.UniqSupply -> IfaceSyn.IfaceDecl -> TcRnTypes.IfL (Maybe CoreSyn.CoreExpr)
loadDecl uniqSupply decl = do
  tyThing <- TcIface.tcIfaceDecl False decl
  case tyThing of
    GHC.AnId _id -> do
      let unfolding = IdInfo.unfoldingInfo $ Var.idInfo _id
      case unfolding of
        (CoreSyn.CoreUnfolding e _ _ _ _ _ _ _ _) -> return $ Just e
        (CoreSyn.DFunUnfolding arity dc cops) -> return $ coreExprFromDFunUnfolding uniqSupply _id dc cops
        _ -> return Nothing
    _ -> return Nothing

coreExprFromDFunUnfolding ::
  UniqSupply.UniqSupply
  -> Var.Var
  -> DataCon.DataCon
  -> [CoreSyn.CoreExpr]
  -> Maybe CoreSyn.CoreExpr
coreExprFromDFunUnfolding uniqSupply dfunId dfunDc dfunOps = Just dfunExpr
  where
    uniques                     = UniqSupply.uniqsFromSupply uniqSupply
    dfunTy                      = Id.idType dfunId
    (dfTVs,dfThetas,dfunResTys) = TcType.tcSplitSigmaTy dfunTy
    dfThetaVars                 = zipWith3 Id.mkSysLocal (repeat $ FastString.mkFastString "dict") uniques (Type.mkPredTys dfThetas)
    (_,[dfArgTy])               = Type.splitAppTys dfunResTys
    dwrapId                     = DataCon.dataConWrapId dfunDc
    dfunVars                    = map (CoreSyn.Type . Type.mkTyVarTy) dfTVs ++ map CoreSyn.Var dfThetaVars
    dfunOps'                    = zipWith MkCore.mkCoreApps dfunOps $ repeat dfunVars
    dfunDcExpr'                 = MkCore.mkCoreApps (CoreSyn.Var dwrapId) (CoreSyn.Type dfArgTy : dfunOps')
    dfunExpr                    = MkCore.mkCoreLams (dfTVs ++ dfThetaVars) dfunDcExpr'

