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
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Data.Label.PureM as Label
import qualified Data.List as List
import qualified Data.Map as Map

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
import CLaSH.Util.Core (CoreBinding, TypedThing(..), nameToString, tyHasFreeTyvars,
  flattenLets)
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
  _ <- mkHType ty
  return True

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
        "Bit"       -> return BitType
        "Clock"     -> return ClockType
        "()"        -> return UnitType
        "Component" -> Error.throwError ($(curLoc) ++ "Component type is not representable, it has to be desugared")
        otherwise -> mkAdtHWType tyCon args
    Nothing -> Error.throwError ($(curLoc) ++ "Do not know how to make HWType out of type: " ++ pprString ty)

mkAdtHWType ::
  TyCon.TyCon
  -> [Type.Type]
  -> NetlistSession HWType
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
          case (dcs, elemHTyss) of
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
  -> Decl
mkUncondAssign dst expr = mkAssign dst Nothing expr

mkAssign ::
  (CoreSyn.CoreBndr, HWType)
  -> Maybe (Expr, Expr)
  -> Expr
  -> Decl
mkAssign (dst,dstTy) cond falseExpr = NetDecl dstName dstTy (Just assignExpr)
  where
    dstName    = nameToString $ Var.varName dst
    assignExpr = case cond of
      Nothing -> falseExpr
      Just (condExpr,trueExpr) -> ExprCond condExpr trueExpr falseExpr
      
varToExpr ::
  Var.Var
  -> NetlistSession Expr
varToExpr var = case Id.isDataConWorkId_maybe var of
  Just dc -> dataconToExpr dc
  Nothing -> return $ ExprVar $ nameToString $ Var.varName var

dataconToExpr ::
  DataCon.DataCon
  -> NetlistSession Expr
dataconToExpr dc = error "dataconToExpr"

isNormalizedBndr ::
  CoreSyn.CoreBndr
  -> NetlistSession Bool
isNormalizedBndr bndr = fmap (Map.member bndr) $ Label.gets nlNormalized

htypeSize :: HWType -> Int
htypeSize UnitType                = 0
htypeSize BitType                 = 1
htypeSize ClockType               = 1
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
    (_,ranges)   = List.mapAccumL (\acc l -> let next = acc+l in (next,(acc,next-1))) 0 fieldLengths

mkSliceExpr ::
  Ident
  -> (Int,Int)
  -> Expr
mkSliceExpr varId (left,right) = ExprSlice varId (ExprLit (ExprNum $ toInteger left)) (ExprLit (ExprNum $ toInteger right))

genBinaryOperator ::
  BinaryOp
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genBinaryOperator op dst args = do
  dstType     <- mkHType dst
  [arg1,arg2] <- mapM (\arg -> case arg of (CoreSyn.Var v) -> varToExpr v; other -> Error.throwError $ $(curLoc) ++ "Not in normal form: arg" ++ pprString arg) args
  return ([mkUncondAssign (dst,dstType) (ExprBinary op arg1 arg2)], [])

genUnaryOperator ::
  UnaryOp
  -> CoreSyn.CoreBndr
  -> [CoreSyn.CoreExpr]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genUnaryOperator op dst [arg] = do
  dstType <- mkHType dst
  arg'    <- case arg of (CoreSyn.Var v) -> varToExpr v; other -> Error.throwError $ $(curLoc) ++ "Not in normal form: arg" ++ pprString arg
  return ([mkUncondAssign (dst,dstType) (ExprUnary op arg')], [])