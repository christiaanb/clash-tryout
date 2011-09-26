{-# LANGUAGE TypeOperators #-}
module CLaSH.Netlist.Tools
  ( isReprType
  , assertReprType
  , mkHType
  , splitNormalized
  , hasNonEmptyType
  , mkUncondAssign
  , varToExpr
  , isNormalizedBndr
  , typeFieldRange
  , mkSliceExpr
  , genBinaryOperator
  , genUnaryOperator
  , dataconToExpr
  , htypeSize
  , genComment
  , argsToExpr
  , argToExpr
  , mkVHDLBasicId
  , toSLV
  , fromSLV
  , genBinaryOperatorSLV
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Label.PureM as Label
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Debug.Trace

-- GHC API
import qualified CoreSubst
import qualified CoreSyn
import qualified DataCon
import qualified Id
import qualified Name
import qualified Outputable
import qualified TyCon
import qualified Type
import qualified Var
import qualified VarSet

-- internal Module
import CLaSH.Netlist.Types
import CLaSH.Util (curLoc,makeCached)
import CLaSH.Util.Core (CoreBinding, TypedThing(..), nameToString, varToStringUniq, tyHasFreeTyvars,
  flattenLets, fromTfpInt)
import CLaSH.Util.Pretty (pprString)

isReprType :: 
  Type.Type 
  -> NetlistSession Bool
isReprType ty = do
  ty <- (mkHType ty) `Error.catchError` (\e -> return $ Invalid e)
  return $ case ty of
    Invalid e -> False
    _         -> True
    
assertReprType ::
  Type.Type
  -> NetlistSession Bool
assertReprType ty = do
  hTy <- mkHType ty
  case hTy of
    (Invalid e) -> Error.throwError e
    others      -> return True

-- | Turn a Core type into a HWType. Returns either an error message if
-- the type was not representable, or the HType generated.
mkHType :: (TypedThing t, Outputable.Outputable t) => 
  t
  -> NetlistSession HWType
mkHType tything =
  case getType tything of
    Nothing -> Error.throwError $ $(curLoc) ++ "Typed thing without a type: " ++ pprString tything
    Just ty -> makeCached (OrdType ty) nlTypes $ mkHType' ty

mkHType' ::
  Type.Type
  -> NetlistSession HWType
mkHType' ty | tyHasFreeTyvars ty = Error.throwError ($(curLoc) ++ "Cannot create HWType out of type that has free type variables: " ++ pprString ty)
            | otherwise = do
  case Type.splitTyConApp_maybe ty of
    Just (tyCon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tyCon)
      case name of
        "Vector"    -> do
          let [lenTy, elTy] = args
          elHWTy          <- mkHType elTy
          len             <- fmap fromInteger $ fromTfpInt nlTfpSyn lenTy
          return $ VecType len elHWTy
        "Unsigned"  -> do
          let [lenTy] = args
          len         <- fmap fromInteger $ fromTfpInt nlTfpSyn lenTy
          return $ UnsignedType len
        "Bit"       -> return BitType
        "Bool"      -> return BoolType
        "()"        -> return UnitType
        "Component" -> Error.throwError ($(curLoc) ++ "Component type is not representable, it has to be desugared")
        otherwise -> mkAdtHWType tyCon args
    Nothing -> Error.throwError ($(curLoc) ++ "Do not know how to make HWType out of type: " ++ pprString ty)

mkAdtHWType ::
  TyCon.TyCon
  -> [Type.Type]
  -> NetlistSession HWType
mkAdtHWType tyCon args = case TyCon.tyConDataCons tyCon of
    [] -> Error.throwError ($(curLoc) ++ "Only custom adt's are supported: " ++ pprString tyCon ++ pprString args)
    dcs -> do
      let argTyss = map DataCon.dataConRepArgTys dcs
      let sumTy   = SumType name $ map (nameToString . DataCon.dataConName) dcs
      case (concat argTyss) of
        [] -> return sumTy
        _  -> do
          let realArgTys = (map . map) (CoreSubst.substTy subst) argTyss
          elemHTyss <- mapM (mapM mkHType) realArgTys
          case (dcs, map (filter (/= UnitType)) elemHTyss) of
            ([dc], [[elemHTy]]) -> return elemHTy
            ([dc], [elemHTys]) -> return $ ProductType name elemHTys
            (dcs,elemHTyss)     -> return $ SPType name $ zip (map (nameToString . DataCon.dataConName) dcs) elemHTyss --Error.throwError ($(curLoc) ++ "Cannot convert SumOfProduct Types to HWTypes: " ++ pprString tyCon)
  where
    name = nameToString $ TyCon.tyConName tyCon
    
    tyvars                  = TyCon.tyConTyVars tyCon
    tyVarArgMap             = zip tyvars args
    dataConTyVars           = (concatMap VarSet.varSetElems) $ (map Type.tyVarsOfType) $ (concatMap DataCon.dataConRepArgTys) $ TyCon.tyConDataCons tyCon
    dataConTyVarArg x       = (x, snd $ head $ filter (equalTyVarName x) tyVarArgMap)
    equalTyVarName z (tv,_) = (Name.nameOccName $ Var.varName z) == (Name.nameOccName $ Var.varName tv)

    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst $ map dataConTyVarArg dataConTyVars

splitNormalized ::
  CoreSyn.CoreExpr
  -> NetlistSession ([CoreSyn.CoreBndr], [CoreBinding], CoreSyn.CoreBndr)
splitNormalized expr = do
  let (args, letExpr) = CoreSyn.collectBinders expr
  let (binds,resExpr) = flattenLets letExpr
  case (args,binds,resExpr) of
    (args, binds, CoreSyn.Var res) -> return (args, binds, res)
    _                              -> Error.throwError $ $(curLoc) ++ "not in normal form: " ++ (pprString expr)

hasNonEmptyType ::
  (TypedThing t, Outputable.Outputable t)
  => t
  -> NetlistSession Bool
hasNonEmptyType thing = do
  thingTy <- mkHType thing
  case thingTy of
    UnitType -> return False
    _ -> return True

mkUncondAssign ::
  (CoreSyn.CoreBndr, HWType)
  -> Expr
  -> [Decl]
mkUncondAssign dst expr = mkAssign dst Nothing expr

mkAssign ::
  (CoreSyn.CoreBndr, HWType)
  -> Maybe (Expr, Expr)
  -> Expr
  -> [Decl]
mkAssign (dst,dstTy) cond falseExpr = [NetDecl dstName dstTy Nothing, NetAssign dstName assignExpr]
  where
    dstName    = varToStringUniq dst
    assignExpr = case cond of
      Nothing -> falseExpr
      Just (condExpr,trueExpr) -> ExprCond condExpr trueExpr falseExpr
      
varToExpr ::
  Var.Var
  -> NetlistSession Expr
varToExpr var = case Id.isDataConWorkId_maybe var of
  Just dc -> do
    varTy <- mkHType var
    dataconToExpr varTy dc
  Nothing -> return $ ExprVar $ varToStringUniq var

dataconToExpr ::
  HWType
  -> DataCon.DataCon
  -> NetlistSession Expr
dataconToExpr hwType dc = do
  let dcName = DataCon.dataConName dc
  case hwType of
    BitType -> return $ ExprLit Nothing $ ExprBit (case Name.getOccString dcName of "H" -> H; "L" -> L ; other -> error $ "other: " ++ show other)
    other -> error $ show other

isNormalizedBndr ::
  CoreSyn.CoreBndr
  -> NetlistSession Bool
isNormalizedBndr bndr = fmap (Map.member bndr) $ Label.gets nlNormalized

htypeSize :: HWType -> Size
htypeSize UnitType                = 0
htypeSize BitType                 = 1
htypeSize BoolType                = 1
htypeSize ClockType               = 1
htypeSize (UnsignedType len)      = len
htypeSize (VecType s eType)       = s * htypeSize eType
htypeSize (SumType _ fields)      = ceiling $ logBase 2 $ fromIntegral $ length fields
htypeSize (ProductType _ fields)  = sum $ map htypeSize fields
htypeSize (SPType _ fields)       = conSize + (maximum $ map (sum . map (htypeSize) . snd) fields)
  where
    conSize = ceiling $ logBase 2 $ fromIntegral $ length fields

typeFieldRange ::
  HWType
  -> Int
  -> (Int,Int)
typeFieldRange hwType dcI = (typeFieldRanges hwType)!!dcI

typeFieldRanges (ProductType _ fields) = ranges
  where
    fieldLengths = map (htypeSize) fields
    (_,ranges)   = List.mapAccumL (\acc l -> let next = acc-l in (next,(acc,next + 1))) ((sum fieldLengths)-1) fieldLengths

mkSliceExpr ::
  Ident
  -> (Int,Int)
  -> Expr
mkSliceExpr varId (left,right) = ExprSlice varId (ExprLit Nothing (ExprNum $ toInteger left)) (ExprLit Nothing (ExprNum $ toInteger right))

argsToExpr ::
  [CoreSyn.CoreExpr]
  -> NetlistSession [Expr]
argsToExpr = mapM argToExpr

argToExpr ::
  CoreSyn.CoreExpr
  -> NetlistSession Expr
argToExpr arg = case arg of
  CoreSyn.Var v -> varToExpr v 
  _     -> Error.throwError $ $(curLoc) ++ "Not in normal form: found non-Var arg: " ++ pprString arg

genBinaryOperator ::
  String
  -> BinaryOp
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genBinaryOperator opS op dst args = do
  dstType     <- mkHType dst
  [arg1,arg2] <- argsToExpr args
  let comment = genComment dst opS args
  return (comment:(mkUncondAssign (dst,dstType) (ExprBinary op arg1 arg2)), [])

genBinaryOperatorSLV ::
  String
  -> BinaryOp
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genBinaryOperatorSLV opS op dst args = do
  dstType     <- mkHType dst
  argTys      <- mapM mkHType args
  [arg1,arg2] <- fmap (zipWith fromSLV argTys) $ argsToExpr args
  let comment = genComment dst opS args
  return (comment:(mkUncondAssign (dst,dstType) (toSLV dstType $ ExprBinary op arg1 arg2)), [])

genUnaryOperator ::
  String
  -> UnaryOp
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genUnaryOperator opS op dst [arg] = do
  dstType <- mkHType dst
  arg'    <- argToExpr arg
  let comment = genComment dst opS [arg]
  return (comment:(mkUncondAssign (dst,dstType) (ExprUnary op arg')), [])

genComment ::
  CoreSyn.CoreBndr
  -> String
  -> [CoreSyn.CoreExpr]
  -> Decl
genComment dst f args = CommentDecl $ pprString dst ++ " = " ++ f ++ (concatMap (\x -> " " ++ pprString x) args) ++ " :: " ++ ((pprString . Maybe.fromJust . getType) dst)

mkVHDLBasicId :: String -> Ident
mkVHDLBasicId = (stripLeading . stripInvalid)
  where
    stripInvalid    = filter (`elem` ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'])
    stripLeading    = dropWhile (`elem` ['0'..'9'])

toSLV :: HWType -> Expr -> Expr
toSLV (UnsignedType _) = ExprFunCall "std_logic_vector" . (:[])

fromSLV :: HWType -> Expr -> Expr
fromSLV (UnsignedType _) = ExprFunCall "unsigned" . (:[])
