{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}
module CLaSH.Util.CoreHW.Tools
  ( TypedThing(..)
  , nameString
  , termType
  , varString
  , varStringUniq
  , mkInternalVar
  , mkTypeVar
  , collectBndrs
  , isFun
  , isPoly
  , isLam
  , applyFunTy
  , termString
  , exprUsesBinders
  , dataConsFor
  , dataConIndex
  , isLet
  , tyHasFreeTyVars
  , hasFreeTyVars
  , collectExprArgs
  , collectTypeArgs
  , collectArgs
  , fromTfpInt
  , isApplicable
  , mkApps
  , mkLams
  , isVar
  , isCon
  , isPrimCon
  , isPrimFun
  , getIntegerLiteral
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import Data.Label                       ((:->))
import qualified Data.List           as List
import Data.Map                         (Map)
import qualified Data.Map            as Map
import qualified Data.Maybe          as Maybe

-- GHC API
import Coercion   (coercionType)
import DataCon    (dataConWorkId)
import FastString (mkFastString)
import Id         (idType,mkSysLocalM)
import Literal    (Literal(..), literalType)
import Name       (Name, mkInternalName, nameOccName, getOccString)
import OccName    (mkVarOcc, occNameString)
import SrcLoc     (noSrcSpan)
import TyCon      (TyCon,tyConDataCons_maybe,isClosedSynTyCon,synTyConType,tyConName)
import Type       (Type, Kind, applyTy, applyTys, mkForAllTy, mkFunTy, splitFunTy, splitFunTy_maybe, isFunTy, splitTyConApp_maybe, tyVarsOfType, splitForAllTy_maybe)
import TypeRep    (Type(..))
import Var        (Var, mkTyVar, varName, varUnique, isTyVar)

-- Internal Modules
import CLaSH.Util
import CLaSH.Util.CoreHW.FreeVars
import CLaSH.Util.CoreHW.Syntax
import CLaSH.Util.CoreHW.Types
import CLaSH.Util.Pretty

class Outputable t => TypedThing t where
  getType :: t -> Maybe Type
  getTypeFail :: t -> Type
  getTypeFail t = case getType t of Just t -> t ; Nothing -> error ("getType")

instance TypedThing Term where
  getType = Just . termType

instance TypedThing Var where
  getType = Just . idType

instance TypedThing Type where
  getType = Just

nameString ::
  Name
  -> String
nameString = occNameString . nameOccName

varString ::
  Var
  -> String
varString = nameString . varName

varStringUniq ::
  Var
  -> String
varStringUniq v = varString v ++ "_" ++ (show . varUnique) v

termType ::
  Term
  -> Type
termType e = case e of
  Var x         -> idType x
  Prim x        -> primType x
  Literal l     -> literalType l
  TyLambda tv e -> tv `mkForAllTy` termType e
  Lambda v e    -> idType v `mkFunTy` termType e
  Data dc       -> idType (dataConWorkId dc)
  TyApp e a     -> termType e `applyTy` a
  Case _ ty _   -> ty
  LetRec _ e    -> termType e
  App _ _       -> case collectArgs e of
                    (fun, args) -> applyTypeToArgs (termType fun) args

primType p = case p of
  PrimFun  x -> idType x
  PrimCon  x -> idType (dataConWorkId x)
  PrimDict x -> idType x
  PrimDFun x -> idType x
  PrimCo   x -> coercionType x

applyTypeToArgs :: Type -> [Either Term Type] -> Type
applyTypeToArgs opTy []              = opTy
applyTypeToArgs opTy (Right ty:args) = applyTypeToArgs (opTy `applyTy` ty) args
applyTypeToArgs opTy (Left e:args)   = case splitFunTy_maybe opTy of
    Just (_, resTy) -> applyTypeToArgs resTy args
    Nothing         -> error $ "applyTypeToArgs splitFunTy" ++ pprString opTy

applyFunTy ::
  Type
  -> Type
  -> Type
applyFunTy funTy argTy = resTy
  where
    (_, resTy) = Maybe.fromMaybe (error $ "applyFunTy splitFunTy: " ++ pprString (funTy, argTy)) $ splitFunTy_maybe funTy

applyFunTys ::
  Type
  -> [Type]
  -> Type
applyFunTys = foldl' applyFunTy

mkInternalVar ::
  (Monad m)
  => String
  -> Type
  -> (TransformSession m) Var
mkInternalVar n ty = mkSysLocalM (mkFastString n) ty

mkTypeVar ::
  (Monad m)
  => String
  -> Kind
  -> (TransformSession m) Var
mkTypeVar n k = do
  uniq        <- getUniqueM
  let occname = mkVarOcc (n ++ show uniq)
  let n'      = mkInternalName uniq occname noSrcSpan
  return $ mkTyVar n' k

collectBndrs ::
  Term
  -> ([Var], Term)
collectBndrs expr = go [] expr
  where
    go bs (Lambda b e)   = go (b:bs) e
    go bs (TyLambda b e) = go (b:bs) e
    go bs e              = (reverse bs, e)

mkApps ::
  Term
  -> [Either Term Type]
  -> Term
mkApps e []              = e
mkApps e1 (Left e2:args) = mkApps (App e1 e2) args
mkApps e (Right t:args)  = mkApps (TyApp e t) args

mkLams ::
  [Var]
  -> Term
  -> Term
mkLams []     e             = e
mkLams (v:vs) e | isTyVar v = (TyLambda v $ mkLams vs e)
                | otherwise = (Lambda   v $ mkLams vs e)

isFun ::
  TypedThing t
  => t
  -> Bool
isFun expr = (isFunTy . getTypeFail) expr

isPoly ::
  TypedThing t
  => t
  -> Bool
isPoly = Maybe.isJust . splitForAllTy_maybe . getTypeFail

isApplicable ::
  TypedThing t
  => t
  -> Bool
isApplicable expr = isFun expr || isPoly expr

isLam ::
  Term
  -> Bool
isLam (Lambda _ _)   = True
isLam (TyLambda _ _) = True
isLam _              = False

isLet ::
  Term
  -> Bool
isLet (LetRec _ _) = True
isLet _            = False

isVar ::
  Term
  -> Bool
isVar (Var _) = True
isVar _       = False

isCon ::
  Term
  -> Bool
isCon (Data _) = True
isCon _        = False

isPrimCon ::
  Term
  -> Bool
isPrimCon (Prim (PrimCon _)) = True
isPrimCon _                  = False

isPrimFun ::
  Term
  -> Bool
isPrimFun (Prim (PrimFun _)) = True
isPrimFun _                  = False

termString ::
  Term
  -> String
termString (Var      _)     = "Var"
termString (Literal  _)     = "Literal"
termString (TyLambda _ _)   = "TyLambda"
termString (Lambda   _ _)   = "Lambda"
termString (Data     _)     = "Data"
termString (TyApp    _ _)   = "TyApp"
termString (App      _ _)   = "App"
termString (Case     _ _ _) = "Case"
termString (LetRec   _ _)   = "LetRec"

exprUsesBinders ::
  [Var]
  -> Term
  -> Bool
exprUsesBinders bndrs = not . isEmptyVarSet . termSomeFreeVars (`elem` bndrs)

dataConIndex ::
  (TypedThing t, Error.MonadError String m)
  => t
  -> DataCon
  -> m Int
dataConIndex tt dc = do
  dcs <- dataConsFor tt
  case List.elemIndex dc dcs of
    Nothing -> Error.throwError $ $(curLoc) ++ "DataCon " ++ pprString dc ++ " does not occur in typed thing: " ++ pprString tt
    Just i  -> return i

dataConsFor ::
  (TypedThing t, Error.MonadError String m)
  => t
  -> m [DataCon]
dataConsFor tt =
  case getType tt of
    Nothing -> Error.throwError $ $(curLoc) ++ "Getting datacon index of untyped thing? " ++ pprString tt
    Just ty -> case Type.splitTyConApp_maybe ty of
      Nothing -> Error.throwError $ $(curLoc) ++ "Trying to find datacon in a type without a tycon?" ++ pprString ty
      Just (tycon, _) -> case TyCon.tyConDataCons_maybe tycon of
        Nothing -> Error.throwError $ $(curLoc) ++ "Trying to find datacon in a type without datacons?" ++ pprString ty
        Just dcs -> return dcs

tyHasFreeTyVars ::
  Type
  -> Bool
tyHasFreeTyVars = not . isEmptyVarSet . tyVarsOfType

hasFreeTyVars ::
  Term
  -> Bool
hasFreeTyVars = not . isEmptyVarSet . termSomeFreeVars isTyVar

collectExprArgs ::
  Term
  -> (Term, [Term])
collectExprArgs = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args (TyApp e t) = go args e
    go args e           = (e, args)

collectTypeArgs ::
  Term
  -> (Term,[Type])
collectTypeArgs = go []
  where
    go args (App e v)   = go args e
    go args (TyApp e t) = go (t:args) e
    go args e           = (e, args)

collectArgs ::
  Term
  -> (Term, [Either Term Type])
collectArgs = go []
  where
    go args (App e1 e2) = go (Left e2:args) e1
    go args (TyApp e t) = go (Right t:args) e
    go args e           = (e, args)

getIntegerLiteral ::
  (Error.MonadError String m, State.MonadState s m, Functor m)
  => s :-> (Map.Map TyCon.TyCon Integer)
  -> Term
  -> m Integer
getIntegerLiteral tfpSynLens expr@(App _ _) =
  case collectArgs expr of
    (_, [Left (Literal (MachInt integer))])    -> return integer
    (_, [Left (Literal (MachInt64 integer))])  -> return integer
    (_, [Left (Literal (MachWord integer))])   -> return integer
    (_, [Left (Literal (MachWord64 integer))]) -> return integer
    _ -> Error.throwError $ $(curLoc) ++ "No integer literal found: " ++ pprString expr
    --(Var f, [Type decTy, decDict, Type numTy, numDict, arg])
    --  | getFullString f == "Types.Data.Num.Ops.fromIntegerT" -> do
    --    fromTfpInt tfpSynLens decTy
getIntegerLiteral _ e = Error.throwError $ $(curLoc) ++ "No integer literal found: " ++ pprString e

fromTfpInt ::
  (Error.MonadError String m, State.MonadState s m, Functor m)
  => s :-> (Map TyCon Integer)
  -> Type
  -> m Integer
fromTfpInt tfpSynLens ty@(TyConApp tycon args) = case (isClosedSynTyCon tycon, null args) of
  (True,True) -> makeCached tycon tfpSynLens $ do
    let tyconTy = synTyConType tycon
    fromTfpInt tfpSynLens tyconTy
  (True,False) -> do
    let tyconName = getOccString $ tyConName tycon
    Error.throwError $ $(curLoc) ++ "Don't know how to handle type synonyms with arguments when translating type level integer: " ++ tyconName
  other -> do
    let tyconName = getOccString $ tyConName tycon
    case tyconName of
      "Dec" -> fromTfpInt tfpSynLens (head args)
      ":."  -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return (int0 * 10 + int1)
      "DecN" -> return 0
      "Dec1" -> return 1
      "Dec2" -> return 2
      "Dec3" -> return 3
      "Dec4" -> return 4
      "Dec5" -> return 5
      "Dec6" -> return 6
      "Dec7" -> return 7
      "Dec8" -> return 8
      "Dec9" -> return 9
      "Succ" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ int + 1
      "Pred" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ int - 1
      ":+:" -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return $ int0 + int1
      ":-:" -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return $ int0 - int1
      ":*:" -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return $ int0 * int1
      "Pow2" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ 2 ^ int
      "Mul2" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ 2 * int
      "Div2" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ int `div` 2
      "Fac" -> do
        int <- fromTfpInt tfpSynLens $ head args
        return $ product [1..int]
      "Min" -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return $ min int0 int1
      "Max" -> do
        [int0,int1] <- mapM (fromTfpInt tfpSynLens) $ take 2 args
        return $ max int0 int1
      other -> Error.throwError $ $(curLoc) ++ "Don't know how to handle type level integer: " ++ tyconName

fromTfpInt tfpSynLens ty = Error.throwError $ $(curLoc) ++ "Don't know how to handle type level integer: " ++ pprString ty
