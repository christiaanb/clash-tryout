{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.Normalize.Tools 
  ( isNormalizable
  , isRepr
  , isLocalVar
  , isLambdaBodyCtx
  , mkSelCase
  , mkBinderFor
  , mkReferenceTo
  , mkFunction
  , splitNormalizedNonRep
  )
where

-- External Modules
import Control.Monad.Trans (lift)
import qualified Control.Monad.Error as Error
import qualified Data.Map as Map
import qualified Data.Label.PureM as Label

-- GHC API
import CoreSyn (Expr(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified MkCore
import qualified Name
import qualified TcType
import qualified TyCon
import qualified Type
import qualified Var

-- Internal Modules
import CLaSH.Driver.Tools (addGlobalBind)
import CLaSH.Netlist.Tools (isReprType, assertReprType)
import CLaSH.Normalize.Types
import CLaSH.Util (curLoc, liftErrorState)
import CLaSH.Util.Core (CoreBinding, CoreContext(..), TypedThing, mkInternalVar, 
  mkTypeVar, cloneVar, flattenLets, getType)
import CLaSH.Util.Pretty (pprString)

isNormalizable ::
  Bool
  -> CoreSyn.CoreExpr
  -> NormalizeSession Bool
isNormalizable resultNonRep bndr = do
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
  Just ty -> (liftErrorState nsNetlistState $ isReprType ty) `Error.catchError` (\(msg :: String) -> return False)

isLambdaBodyCtx ::
  CoreContext
  -> Bool
isLambdaBodyCtx (LambdaBody _) = True
isLambdaBodyCtx _              = False

isLocalVar :: 
  CoreSyn.CoreExpr
  -> NormalizeSession Bool
isLocalVar (CoreSyn.Var name) = do
  bndrs <- fmap (Map.keys) $ (lift . lift) $ Label.gets nsBindings
  let isDC = Id.isDataConWorkId name
  return $ not isDC && name `notElem` bndrs
isLocalVar _ = return False

-- Create a "selector" case that selects the ith field from dc_ith
-- datacon
mkSelCase ::
  CoreSyn.CoreExpr
  -> Int
  -> Int
  -> NormalizeSession CoreSyn.CoreExpr
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

splitNormalizedNonRep ::
  CoreSyn.CoreExpr
  -> ([CoreSyn.CoreBndr], [CoreBinding], CoreSyn.CoreExpr)
splitNormalizedNonRep expr = (args, binds, resExpr)
  where
    (args, letExpr) = CoreSyn.collectBinders expr
    (binds,resExpr) = flattenLets letExpr

mkFunction ::
  CoreSyn.CoreBndr
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreBndr
mkFunction bndr body = do
  let bodyTy = CoreUtils.exprType body
  bodyId <- cloneVar bndr
  let newId = Var.setVarType bodyId bodyTy
  (lift . lift) $ addGlobalBind nsBindings newId body
  return newId

mkReferenceTo ::
  Var.Var
  -> CoreSyn.CoreExpr
mkReferenceTo var | Var.isTyVar var = (Type $ Type.mkTyVarTy var)
                  | otherwise       = (Var var)

mkBinderFor ::
  CoreSyn.CoreExpr 
  -> String 
  -> NormalizeSession Var.Var
mkBinderFor (Type ty) name = mkTypeVar name (TcType.typeKind ty)
mkBinderFor expr name      = mkInternalVar name (CoreUtils.exprType expr)
