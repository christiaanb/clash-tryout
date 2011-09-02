{-# LANGUAGE FlexibleContexts #-}
module CLaSH.Util.Core.Tools
  ( tyHasFreeTyvars
  , nameToString
  , isFun
  , isPoly
  , isApplicable
  , isLam
  , isLet
  , isVar
  , hasFreeTyVars
  , viewVarOrApp
  , dataconIndex
  , dataconsFor
  , exprUsesBinders
  , flattenLets
  , exprToVar
  , getValArgs
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.List as List
import qualified Data.Maybe as Maybe

-- GHC API
import qualified DataCon
import qualified CoreFVs
import qualified CoreSyn
import qualified CoreUtils
import qualified Name
import qualified OccName
import qualified TcType
import qualified TyCon
import qualified Type
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Util
import CLaSH.Util.Pretty
import CLaSH.Util.Core.Types

-- | Does the given type have any free type vars?
tyHasFreeTyvars :: Type.Type -> Bool
tyHasFreeTyvars = not . VarSet.isEmptyVarSet . Type.tyVarsOfType

-- | Extracts the string version of a name
nameToString :: Name.Name -> String
nameToString = OccName.occNameString . Name.nameOccName

isFun :: CoreSyn.CoreExpr -> Bool
isFun (CoreSyn.Type _) = False
isFun expr             = (Type.isFunTy . CoreUtils.exprType) expr

isPoly :: CoreSyn.CoreExpr -> Bool
isPoly (CoreSyn.Type _) = False
isPoly expr             = (Maybe.isJust . Type.splitForAllTy_maybe . CoreUtils.exprType) expr

isApplicable :: CoreSyn.CoreExpr -> Bool
isApplicable expr = isFun expr || isPoly expr

isLam :: CoreSyn.CoreExpr -> Bool
isLam (CoreSyn.Lam _ _) = True
isLam _                 = False

isLet :: CoreSyn.CoreExpr -> Bool
isLet (CoreSyn.Let _ _) = True
isLet _                 = False

isVar :: CoreSyn.CoreExpr -> Bool
isVar (CoreSyn.Var _) = True
isVar _               = False

hasFreeTyVars :: CoreSyn.CoreExpr -> Bool
hasFreeTyVars = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars Var.isTyVar)

viewVarOrApp :: CoreSyn.CoreExpr -> Bool
viewVarOrApp (CoreSyn.App _ _)  = True
viewVarOrApp (CoreSyn.Var _)    = True
viewVarOrApp (CoreSyn.Cast e _) = viewVarOrApp e
viewVarOrApp _                  = False

dataconIndex :: (TypedThing t, Error.MonadError String m) => t -> DataCon.DataCon -> m Int
dataconIndex tt dc = do
  dcs <- dataconsFor tt
  case List.elemIndex dc dcs of
    Nothing -> Error.throwError $ $(curLoc) ++ "Datacon " ++ pprString dc ++ " does not occur in typed thing: " ++ pprString tt
    Just i -> return i    

dataconsFor :: (TypedThing t, Error.MonadError String m) => t -> m [DataCon.DataCon]
dataconsFor tt =
  case getType tt of
    Nothing -> Error.throwError $ $(curLoc) ++ "Getting datacon index of untyped thing? " ++ pprString tt
    Just ty -> case Type.splitTyConApp_maybe ty of
      Nothing -> Error.throwError $ $(curLoc) ++ "Trying to find datacon in a type without a tycon?" ++ pprString ty
      Just (tycon, _) -> case TyCon.tyConDataCons_maybe tycon of
        Nothing -> Error.throwError $ $(curLoc) ++ "Trying to find datacon in a type without datacons?" ++ pprString ty
        Just dcs -> return dcs

exprUsesBinders :: [CoreSyn.CoreBndr] -> CoreSyn.CoreExpr -> Bool
exprUsesBinders bndrs = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` bndrs))

-- | Flattens nested lets into a single list of bindings. The expression
--   passed does not have to be a let expression, if it isn't an empty list of
--   bindings is returned.
flattenLets ::
  CoreSyn.CoreExpr -- ^ The expression to flatten.
  -> ([CoreBinding], CoreSyn.CoreExpr) -- ^ The bindings and resulting expression.
flattenLets (CoreSyn.Let binds expr) = 
  (bindings ++ bindings', expr')
  where
    -- Recursively flatten the contained expression
    (bindings', expr') =flattenLets expr
    -- Flatten our own bindings to remove the Rec / NonRec constructors
    bindings = CoreSyn.flattenBinds [binds]
flattenLets expr = ([], expr)

exprToVar :: CoreSyn.CoreExpr -> Var.Id
exprToVar (CoreSyn.Var varId) = varId
exprToVar expr = error $ $(curLoc) ++ "Not a var: " ++ show expr

getValArgs :: Type.Type -> [CoreSyn.CoreExpr] -> [CoreSyn.CoreExpr]
getValArgs ty args = drop n args
  where
    (tyvars,predtypes,_) = deepSplitSigmaTy ty
    n = length tyvars + length predtypes
    
    deepSplitSigmaTy ty = case TcType.tcSplitSigmaTy ty of
      r@([],[],ty') -> ([],[],ty')
      (tyvars, predtypes, ty') -> let (tyvars', predtypes', ty'') = TcType.tcSplitSigmaTy ty' in (tyvars ++ tyvars', predtypes ++ predtypes', ty'')
