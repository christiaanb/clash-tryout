module CLaSH.Netlist.Tools
  ( isReprType
  , assertReprType
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Map as Map
import qualified Data.Label.PureM as Label

import Debug.Trace

-- GHC API
import qualified CoreSubst
import qualified DataCon
import qualified Name
import qualified Outputable
import qualified TyCon
import qualified Type
import qualified Var
import qualified VarSet

-- internal Module
import CLaSH.Netlist.Types
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Pretty

isReprType :: Type.Type -> NetlistSession Bool
isReprType ty = do
  ty <- (mkHType ty) `Error.catchError` (\e -> return $ Invalid e)
  return $ case ty of
    Invalid e -> False
    _         -> True
    
assertReprType :: Type.Type -> NetlistSession Bool
assertReprType ty = do
  _ <- mkHType ty
  return True

-- | Turn a Core type into a HWType. Returns either an error message if
-- the type was not representable, or the HType generated.
mkHType :: (TypedThing t, Outputable.Outputable t) => 
  t -> NetlistSession HWType
mkHType tything =
  case getType tything of
    Nothing -> Error.throwError $ $(curLoc) ++ "Typed thing without a type: " ++ pprString tything
    Just ty -> mkHType' ty

mkHType' :: Type.Type -> NetlistSession HWType
mkHType' ty | tyHasFreeTyvars ty = Error.throwError ($(curLoc) ++ "Cannot create HWType out of type that has free type variables: " ++ pprString ty)
            | otherwise = do
  case Type.splitTyConApp_maybe ty of
    Just (tyCon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tyCon)
      builtinMaybe <- fmap (Map.lookup name) $ Label.gets nlTypes
      case builtinMaybe of
        (Just t) -> return t
        Nothing  -> case name of
          "Component" -> Error.throwError ($(curLoc) ++ "Component type is not representable, it has to be desugared")
          otherwise -> mkAdtHWType tyCon args
    Nothing -> Error.throwError ($(curLoc) ++ "Do not know how to make HWType out of type: " ++ pprString ty)

mkAdtHWType :: TyCon.TyCon -> [Type.Type] -> NetlistSession HWType
mkAdtHWType tyCon args = case TyCon.tyConDataCons tyCon of
    [] -> Error.throwError ($(curLoc) ++ "Only custom adt's are supported: " ++ pprString tyCon)
    dcs -> do
      let argTyss = map DataCon.dataConRepArgTys dcs
      let sumTy   = SumType name $ map (nameToString . DataCon.dataConName) dcs
      case (concat argTyss) of
        [] -> return sumTy
        _  -> do
          let realArgTys = (map . map) (CoreSubst.substTy subst) argTyss
          elemHTyss <- mapM (mapM mkHType) realArgTys
          case (dcs, map (filter (/= UnitType)) elemHTyss) of
            ([dc], [elemHTysMinU]) -> return $ ProductType name elemHTysMinU
            (dcs,elemHTysMinU)     -> return $ SPType name $ zip (map (nameToString . DataCon.dataConName) dcs) elemHTysMinU --Error.throwError ($(curLoc) ++ "Cannot convert SumOfProduct Types to HWTypes: " ++ pprString tyCon)
  where
    name = nameToString $ TyCon.tyConName tyCon
    
    tyvars                  = TyCon.tyConTyVars tyCon
    tyVarArgMap             = zip tyvars args
    dataConTyVars           = (concatMap VarSet.varSetElems) $ (map Type.tyVarsOfType) $ (concatMap DataCon.dataConRepArgTys) $ TyCon.tyConDataCons tyCon
    dataConTyVarArg x       = (x, snd $ head $ filter (equalTyVarName x) tyVarArgMap)
    equalTyVarName z (tv,_) = (Name.nameOccName $ Var.varName z) == (Name.nameOccName $ Var.varName tv)

    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst $ map dataConTyVarArg dataConTyVars


