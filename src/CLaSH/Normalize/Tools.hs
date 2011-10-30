{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards       #-}
module CLaSH.Normalize.Tools
  ( isNormalizable
  , assertNormalizable
  , isRepr
  , isLocalVar
  , isLambdaBodyCtx
  , mkSelCase
  , mkBinderFor
  , mkTyBinderFor
  , mkReferenceTo
  , mkFunction
  , splitNormalizedNonRep
  , getGlobalExpr
  , varInArgPosition
  )
where

-- External Modules
import Control.Monad.Trans (lift)
import qualified Control.Monad.Error as Error
import qualified Data.Map as Map
import qualified Data.Label.PureM as Label

-- GHC API
import qualified CoreUtils
import qualified DataCon
import qualified Id
import qualified Kind
import qualified MkCore
import qualified Name
import qualified TcType
import qualified TyCon
import qualified Type
import qualified Var

-- Internal Modules
import CLaSH.Netlist.Tools   (isReprType, assertReprType)
import CLaSH.Normalize.Types
import CLaSH.Util            (curLoc, liftErrorState)
import CLaSH.Util.CoreHW     (Var, Term(..), AltCon(..),CoreBinding, CoreContext(..), TypedThing(..), Type, mkInternalVar, mkTypeVar, cloneVar, flattenLets, collectBndrs, collectArgs)
import CLaSH.Util.Pretty     (pprString)

isNormalizable ::
  Bool
  -> Term
  -> NormalizeSession Bool
isNormalizable resultNonRep bndr = do
  let {
    ; bndrTy = getTypeFail bndr
    ; (argTys, resTy) = Type.splitFunTys bndrTy
    ; checkTys = if resultNonRep then argTys else resTy:argTys
    }
  fmap and $ mapM isRepr checkTys

assertNormalizable ::
  Bool
  -> Term
  -> NormalizeSession Bool
assertNormalizable resultNonRep expr = do
  let { exprTy = getTypeFail expr
      ; (argTys,resTy) = Type.splitFunTys exprTy
      ; checkTys = if resultNonRep then argTys else resTy:argTys
      }
  fmap and $ mapM assertRepr checkTys

isRepr ::
  (TypedThing t)
  => t
  -> NormalizeSession Bool
isRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> (liftErrorState nsNetlistState $ isReprType ty) `Error.catchError` (\(msg :: String) -> return False)

assertRepr ::
  (TypedThing t)
  => t
  -> NormalizeSession Bool
assertRepr tyThing = case getType tyThing of
  Nothing -> return False
  Just ty -> (liftErrorState nsNetlistState $ assertReprType ty)

isLambdaBodyCtx ::
  CoreContext
  -> Bool
isLambdaBodyCtx (LambdaBody _) = True
isLambdaBodyCtx _              = False

isLocalVar ::
  Term
  -> NormalizeSession Bool
isLocalVar (Var name) = do
  bndrs <- fmap (Map.keys) $ (lift . lift) $ Label.gets nsBindings
  let isDC = Id.isDataConWorkId name
  return $ not isDC && name `notElem` bndrs
isLocalVar _ = return False

-- Create a "selector" case that selects the ith field from dc_ith
-- datacon
mkSelCase ::
  String
  -> Term
  -> Int
  -> Int
  -> NormalizeSession Term
mkSelCase caller scrut dcI i = do
  case Type.splitTyConApp_maybe scrutTy of
    -- The scrutinee should have a type constructor. We keep the type
    -- arguments around so we can instantiate the field types below
    Just (tycon, tyargs) -> case TyCon.tyConDataCons_maybe tycon of
      -- The scrutinee type should have a single dataconstructor,
      -- otherwise we can't construct a valid selector case.
      Just dcs | dcI < 0 || dcI >= length dcs -> Error.throwError $ $(curLoc) ++ caller ++ ": Creating extractor case, but datacon index is invalid." ++ errorMsg
               | otherwise -> do
        let datacon = (dcs!!dcI)
        let fieldTys = DataCon.dataConInstOrigArgTys datacon tyargs
        if i < 0 || i >= length fieldTys
          then Error.throwError $ $(curLoc) ++ caller ++ ": Creating extractor case, but field index is invalid." ++ errorMsg
          else do
            -- Create a list of wild binders for the fields we don't want
            let wildbndrs = map MkCore.mkWildValBinder fieldTys
            -- Create a single binder for the field we want
            selBndr <- mkInternalVar "sel" (fieldTys!!i)
            let selBndrTy = getTypeFail selBndr
            -- Create the case expression
            let binders = take i wildbndrs ++ [selBndr] ++ drop (i+1) wildbndrs
            return $ Case scrut selBndrTy [(DataAlt datacon [] binders, Var selBndr)]
      Nothing -> Error.throwError $ $(curLoc) ++ caller ++ ": Creating extractor case, but scrutinee has no datacons?" ++ errorMsg
    Nothing -> Error.throwError $ $(curLoc) ++ caller ++ ": Creating extractor case, but scrutinee has no tycon?" ++ errorMsg
  where
    scrutTy = getTypeFail scrut
    errorMsg = " Extracting element " ++ (show i) ++ " from datacon " ++ (show dcI) ++ " from '" ++ pprString scrut ++ "'" ++ " Type: " ++ (pprString scrutTy)

splitNormalizedNonRep ::
  Term
  -> ([Var], [CoreBinding], Term)
splitNormalizedNonRep expr = (args, binds, resExpr)
  where
    (args, letExpr) = collectBndrs expr
    (binds,resExpr) = flattenLets letExpr

mkFunction ::
  Var
  -> Term
  -> NormalizeSession Var
mkFunction bndr body = do
  let bodyTy = getTypeFail body
  bodyId <- cloneVar bndr
  let newId = Var.setVarType bodyId bodyTy
  addGlobalBind newId body
  return newId

mkReferenceTo ::
  Var
  -> Term
mkReferenceTo var = (Var var)

mkBinderFor ::
  TypedThing t
  => t
  -> String
  -> NormalizeSession Var
mkBinderFor tt name = mkInternalVar name (getTypeFail tt)

mkTyBinderFor ::
  Type
  -> String
  -> NormalizeSession Var
mkTyBinderFor t name = mkTypeVar name (Kind.typeKind t)

addGlobalBind ::
  Var
  -> Term
  -> NormalizeSession ()
addGlobalBind vId body = do
  (lift . lift) $ Label.modify nsBindings (Map.insert vId body)

getGlobalExpr ::
  Var
  -> NormalizeSession (Maybe Term)
getGlobalExpr vId = do
  fmap (Map.lookup vId) $ (lift . lift) $ Label.gets nsBindings

varInArgPosition ::
  Var
  -> Term
  -> Bool
varInArgPosition v (App e v')      | v == v'
                                   , (Var f, _) <- collectArgs e
                                   = False
                                   | v == v'
                                   = True
varInArgPosition v (App e _)       | otherwise = varInArgPosition v e
varInArgPosition v (LetRec b e)    = or $ (map (varInArgPosition v . snd) b) ++ [varInArgPosition v e]
varInArgPosition v (Case s _ a)    = or $ (map (varInArgPosition v . snd) a) ++ [varInArgPosition v s]
varInArgPosition v (Lambda _ e)    = varInArgPosition v e
varInArgPosition v (TyLambda _ e)  = varInArgPosition v e
varInArgPosition v (Data dc as xs) = v `elem` xs
varInArgPosition _ _               = False
