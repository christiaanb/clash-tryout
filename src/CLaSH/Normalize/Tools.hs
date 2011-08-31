{-# LANGUAGE RelaxedLayout #-}
{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.Normalize.Tools where

-- External Modules
import Control.Monad.Trans
import qualified Control.Monad.Error as Error
import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Label.PureM as Label
import Language.KURE

import Debug.Trace

-- GHC API
import qualified CoreSubst
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified IdInfo
import qualified MkCore
import qualified Module
import qualified MonadUtils
import qualified Name
import qualified OccName
import qualified Outputable
import qualified SrcLoc
import qualified TcType
import qualified TyCon
import qualified Type
import qualified UniqSupply
import qualified Var
import qualified VarEnv

-- Internal Modules
import CLaSH.Driver.Tools
import CLaSH.Netlist.Constants
import qualified CLaSH.Netlist.Tools as NetlistTools
import CLaSH.Normalize.Types
import CLaSH.Util
import CLaSH.Util.Core.Types
import CLaSH.Util.Core
import CLaSH.Util.Core.Traverse
import CLaSH.Util.Core.Transform
import CLaSH.Util.GHC
import CLaSH.Util.Pretty

isNormalizable
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession Bool
isNormalizable resultNonRep bndr = do
  let {
    ; bndrTy = Id.idType bndr
    ; (argTys, resTy) = Type.splitFunTys bndrTy
    ; checkTys = if resultNonRep then argTys else resTy:argTys
    } 
  fmap and $ mapM isRepr checkTys

isNormalizableE
  :: Bool
  -> CoreSyn.CoreExpr
  -> NormalizeSession Bool
isNormalizableE resultNonRep bndr = do
  let {
    ; bndrTy = CoreUtils.exprType bndr
    ; (argTys, resTy) = Type.splitFunTys bndrTy
    ; checkTys = if resultNonRep then argTys else resTy:argTys
    } 
  fmap and $ mapM isRepr checkTys

isRepr ::
  (TypedThing t)
  => t
  -> NormalizeSession Bool
isRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> (liftErrorState nsNetlistState $ NetlistTools.isReprType ty) `Error.catchError` (\(msg :: String) -> error "DIE!")

assertRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> liftErrorState nsNetlistState $ NetlistTools.assertReprType ty

isLambdaBodyCtx (LambdaBody _) = True
isLambdaBodyCtx _              = False

isLocalVar :: CoreSyn.CoreExpr -> NormalizeSession Bool
isLocalVar (CoreSyn.Var name) = do
  bndrs <- fmap (Map.keys) $ (lift . lift) $ Label.gets nsBindings
  let isDC = Id.isDataConWorkId name
  return $ not isDC && name `notElem` bndrs
isLocalVar _ = return False

-- Create a "selector" case that selects the ith field from dc_ith
-- datacon
mkSelCase :: CoreSyn.CoreExpr -> Int -> Int -> NormalizeSession CoreSyn.CoreExpr
mkSelCase scrut dcI i = do
  case Type.splitTyConApp_maybe scrutTy of
    -- The scrutinee should have a type constructor. We keep the type
    -- arguments around so we can instantiate the field types below
    Just (tycon, tyargs) -> case TyCon.tyConDataCons_maybe tycon of
      -- The scrutinee type should have a single dataconstructor,
      -- otherwise we can't construct a valid selector case.
      Just dcs | dcI < 0 || dcI >= length dcs -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but datacon index is invalid." ++ errorMsg
               | otherwise -> do
        let datacon = (dcs!!dcI)
        let fieldTys = DataCon.dataConInstOrigArgTys datacon tyargs
        if i < 0 || i >= length fieldTys
          then Error.throwError $ $(curLoc) ++ "Creating extractor case, but field index is invalid." ++ errorMsg
          else do
            -- Create a list of wild binders for the fields we don't want
            let wildbndrs = map MkCore.mkWildValBinder fieldTys
            -- Create a single binder for the field we want
            selBndr <- mkInternalVar "sel" (fieldTys!!i)
            -- Create a wild binder for the scrutinee
            let scrutBndr = MkCore.mkWildValBinder scrutTy
            -- Create the case expression
            let binders = take i wildbndrs ++ [selBndr] ++ drop (i+1) wildbndrs
            return $ Case scrut scrutBndr scrutTy [(DataAlt datacon, binders, Var selBndr)]
      Nothing -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but scrutinee has no datacons?" ++ errorMsg
    Nothing -> Error.throwError $ $(curLoc) ++ "Creating extractor case, but scrutinee has no tycon?" ++ errorMsg
  where
    scrutTy = CoreUtils.exprType scrut
    errorMsg = " Extracting element " ++ (show i) ++ " from datacon " ++ (show dcI) ++ " from '" ++ pprString scrut ++ "'" ++ " Type: " ++ (pprString scrutTy)

getExtExpr
  :: Name.Name
  -> NormalizeSession (Maybe CoreSyn.CoreExpr)
getExtExpr name = do
  exprMaybe <- Error.liftIO $ loadExtExpr name 
  case exprMaybe of
    (Just expr) -> do
      return (Just expr)
    Nothing     -> return Nothing

splitNormalizedNonRep
  :: CoreSyn.CoreExpr
  -> ([CoreSyn.CoreBndr], [CoreBinding], CoreSyn.CoreExpr)
splitNormalizedNonRep expr = (args, binds, resExpr)
  where
    (args, letExpr) = CoreSyn.collectBinders expr
    (binds,resExpr) = flattenLets letExpr

mkFunction :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> NormalizeSession CoreSyn.CoreBndr
mkFunction bndr body = do
  let bodyTy = CoreUtils.exprType body
  bodyId <- cloneVar bndr
  let newId = Var.setVarType bodyId bodyTy
  (lift . lift) $ addGlobalBind nsBindings newId body
  return newId

mkReferenceTo :: Var.Var -> CoreSyn.CoreExpr
mkReferenceTo var | Var.isTyVar var = (CoreSyn.Type $ Type.mkTyVarTy var)
                  | otherwise       = (CoreSyn.Var var)


mkBinderFor ::
  CoreSyn.CoreExpr 
  -> String 
  -> NormalizeSession Var.Var
mkBinderFor (CoreSyn.Type ty) name = mkTypeVar name (TcType.typeKind ty)
mkBinderFor expr name              = mkInternalVar name (CoreUtils.exprType expr)

mkTypeVar ::
  String 
  -> Type.Kind 
  -> NormalizeSession Var.Var
mkTypeVar name kind = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc (name ++ show uniq)
  let name' = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkTyVar name' kind

