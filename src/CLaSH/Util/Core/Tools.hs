{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}
module CLaSH.Util.Core.Tools
  ( tyHasFreeTyvars
  , nameToString
  , varToString
  , varToStringUniq
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
  , getIntegerLiteral
  , fromTfpInt
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import Data.Label ((:->))
import qualified Data.Label.PureM as Label
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- GHC API
import qualified DataCon
import qualified CoreFVs
import CoreSyn (Expr(..),Bind(..),AltCon(..))
import qualified CoreSyn
import qualified CoreUtils
import qualified Literal
import qualified Module
import qualified Name
import qualified OccName
import qualified TcType
import qualified TyCon
import qualified Type
import qualified TypeRep
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

varToString :: Var.Var -> String
varToString = nameToString . Var.varName

varToStringUniq :: Var.Var -> String
varToStringUniq v = (nameToString . Var.varName) v ++ "_" ++ (show . Var.varUnique) v

getFullString :: Name.NamedThing a => a -> String
getFullString thing = modstr ++ occstr
  where
    name    = Name.getName thing
    modstr  = case Name.nameModule_maybe name of
      Nothing -> ""
      Just mod -> Module.moduleNameString (Module.moduleName mod) ++ "."
    occstr  = Name.getOccString name

isFun :: CoreSyn.CoreExpr -> Bool
isFun (CoreSyn.Type _) = False
isFun expr             = (Type.isFunTy . getTypeFail) expr

isPoly :: CoreSyn.CoreExpr -> Bool
isPoly (CoreSyn.Type _) = False
isPoly expr             = (Maybe.isJust . Type.splitForAllTy_maybe . getTypeFail) expr

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

getIntegerLiteral ::
  (Error.MonadError String m, State.MonadState s m, Functor m)
  => s :-> (Map.Map TyCon.TyCon Integer)
  -> CoreSyn.CoreExpr
  -> m Integer
getIntegerLiteral tfpSynLens expr@(App _ _) =
  case CoreSyn.collectArgs expr of
    (_, [Lit (Literal.MachInt integer)]) -> return integer
    (_, [Lit (Literal.MachInt64 integer)]) -> return integer
    (_, [Lit (Literal.MachWord integer)]) -> return integer
    (_, [Lit (Literal.MachWord64 integer)]) -> return integer
    (Var f, [Type decTy, decDict, Type numTy, numDict, arg])
      | getFullString f == "Types.Data.Num.Ops.fromIntegerT" -> do
        fromTfpInt tfpSynLens decTy

fromTfpInt :: 
  (Error.MonadError String m, State.MonadState s m, Functor m)
  => s :-> (Map.Map TyCon.TyCon Integer)
  -> Type.Type
  -> m Integer
fromTfpInt tfpSynLens ty@(TypeRep.TyConApp tycon args) = case (TyCon.isClosedSynTyCon tycon, null args) of
  (True,True) -> makeCached tycon tfpSynLens $ do
    let tyconTy = TyCon.synTyConType tycon
    fromTfpInt tfpSynLens tyconTy
  (True,False) -> do
    let tyconName = Name.getOccString $ TyCon.tyConName tycon
    Error.throwError $ $(curLoc) ++ "Don't know how to handle type synonyms with arguments when translating type level integer: " ++ tyconName
  other -> do
    let tyconName = Name.getOccString $ TyCon.tyConName tycon
    case tyconName of
      "Dec" -> fromTfpInt tfpSynLens (head args)
      ":."  -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return (int0 * 10 + int1)
      "DecN" -> return 0
      "Dec4" -> return 4
      other -> Error.throwError $ $(curLoc) ++ "Don't know how to handle type level integer: " ++ tyconName
  

fromTfpInt tfpSynLens ty = Error.throwError $ $(curLoc) ++ "Don't know how to handle type level integer: " ++ pprString ty