{-# LANGUAGE PatternGuards #-}
module CLaSH.Netlist
  ( genNetlist
  )
where

-- External Modules
import qualified Control.Monad as Monad
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import qualified Data.Label as Label
import qualified Data.Label.PureM as LabelM
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Debug.Trace

-- GHC API
import qualified CoreSyn
import qualified CoreUnfold
import qualified DataCon
import qualified FastString
import qualified Id
import qualified IdInfo
import qualified Literal
import qualified Name
import qualified Var

-- Internal Modules
import CLaSH.Driver.Types (DriverSession)
import CLaSH.Netlist.Tools
import CLaSH.Netlist.Types
import CLaSH.Util (curLoc,makeCached,first,second)
import CLaSH.Util.CoreHW (Var, Term(..), Prim(..), AltCon(..), CoreBinding, varString, varStringUniq, collectExprArgs, dataConIndex, dataConsFor, getTypeFail, isVar, getIntegerLiteral, filterLiterals, getType, mkApps)
import CLaSH.Util.Pretty (pprString)

genNetlist ::
  NetlistState
  -> [(Var, Term)]
  -> Var
  -> Maybe Integer
  -> DriverSession ([Module], [HWType], NetlistState)
genNetlist nlState normalized topEntity mStart = do
  let (retVal, nlState') = State.runState (Error.runErrorT (genModules topEntity mStart)) (nlState { _nlNormalized = Map.fromList normalized })
  case retVal of
    Left errMsg   -> error errMsg
    Right netlist -> do
      let elTypes = List.nub . map (\(VecType _ e) -> e) . filter (\t -> case t of VecType _ e -> e /= BitType; _ -> False) . Map.elems . Label.get nlTypes $ nlState'
      return (netlist,elTypes,nlState')

genModules ::
  Var
  -> Maybe Integer
  -> NetlistSession [Module]
genModules topEntity mStart = do
  topMod <- genModule topEntity mStart
  allMods <- LabelM.gets nlMods
  return $ map snd $ Map.toList allMods

genModule ::
  Var
  -> Maybe Integer
  -> NetlistSession Module
genModule modName mStart = do
  modExprMaybe <- fmap (Map.lookup modName) $ LabelM.gets nlNormalized
  case modExprMaybe of
    Nothing      -> Error.throwError $ $(curLoc) ++ "No normalized expr for bndr: " ++ (show modName)
    Just modExpr -> makeCached modName nlMods $ genModule' modName modExpr mStart

genModule' ::
  Var
  -> Term
  -> Maybe Integer
  -> NetlistSession Module
genModule' modName modExpr mStart = do
  LabelM.puts nlVarCnt (Maybe.fromMaybe 0 mStart)
  (args,binds,res)       <- (\m -> splitNormalized m >>= makeUnique) modExpr
  (resType:argTypes)     <- mapM mkHType (res:args)
  let (resName:argNames) = map varString (res:args)
  modCnt           <- LabelM.gets nlModCnt
  LabelM.modify nlModCnt (+1)
  let modName'     = ((++ (show modCnt)) . (\v -> if null v then (v ++ "Component_") else (v ++ "_")) . mkVHDLBasicId . varString) modName
  (assigns,clocks) <- fmap unzip $ mapM mkConcSm binds
  let modInps'     = (zip argNames argTypes) ++ (List.nub $ concat clocks)
  let modInps      = filter (not . untranslatableHType . snd) modInps'
  let modOutps     = [(resName,resType)]
  modDecls         <- mapM (\(d,_) -> mkHType d >>= \t -> return $ NetDecl (varString d) t Nothing) (filter ((/= res) . fst) binds)
  let modAssigns   = concat assigns
  return $ Module modName' modInps modOutps (modDecls ++ modAssigns)

mkConcSm ::
  CoreBinding
  -> NetlistSession ([Decl],[(Ident,HWType)])

mkConcSm (bndr, Var v) = genApplication bndr v []

mkConcSm (bndr, app@(App _ _)) = do
  let (appF, args) = collectExprArgs app
  args'            <- Monad.filterM (fmap not . hasUntranslatableType) args
  case appF of
    Var f -> case (all isVar args') of
      True  -> genApplication bndr f args'
      False -> Error.throwError $ $(curLoc) ++ "Not in normal form: Var-application with non-Var arguments:\n" ++ pprString app
    Data dc -> case (all isVar args') of
      True  -> genApplication bndr (DataCon.dataConWorkId dc) args'
      False -> Error.throwError $ $(curLoc) ++ "Not in normal form: Data-application with non-Var arguments:\n" ++ pprString app
    Prim (PrimFun f) -> case (List.lookup (varString f) builtinBuilders) of
      Just (argCount, builder) -> if length args == argCount
          then builder bndr args
          else Error.throwError $ $(curLoc) ++ "Incorrect number of arguments to builtin function(exptected: " ++ show argCount ++ ", actual: " ++ show (length args) ++"): " ++ pprString (bndr,app,args)
      Nothing -> Error.throwError $ $(curLoc) ++ "Using a primitive function that is not a known builtin: " ++ pprString (bndr,app)
    Prim (PrimCon dc) -> case (List.lookup (varString $ DataCon.dataConWorkId dc) builtinBuilders) of
      Just (argCount, builder) -> if length args == argCount
        then builder bndr args
        else Error.throwError $ $(curLoc) ++ "Incorrect number of arguments to builtin constructor(exptected: " ++ show argCount ++ ", actual: " ++ show (length args) ++"): " ++ pprString (bndr,app,args)
      Nothing -> Error.throwError $ $(curLoc) ++ "Using a primitive constructor that is not a known builtin: " ++ pprString (bndr,app)
    _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: application of a non-Var:\n" ++ pprString app

mkConcSm (bndr, expr@(Case (Var scrut) ty [alt])) = do
  let comment = genComment bndr (pprString expr) []
  case alt of
    (DataAlt dc varbndrs, (Var selBndr)) -> do
      nonEmptySel <- hasNonEmptyType selBndr
      if nonEmptySel
        then do
          bndrs' <- Monad.filterM hasNonEmptyType varbndrs
          case List.elemIndex selBndr bndrs' of
            Just selI -> do
              hwTypeScrut <- mkHType scrut
              hwTypeBndr  <- mkHType bndr
              if hwTypeScrut == hwTypeBndr
                then do
                  let selName = varString scrut
                  let selExpr = ExprVar selName
                  return (comment:(mkUncondAssign (bndr,hwTypeBndr) selExpr), [])
                else do
                  case hwTypeScrut of
                    ProductType _ _ -> do
                      let fieldSlice = typeFieldRange hwTypeScrut 0 selI
                      let sliceExpr = mkSliceExpr (varString scrut) fieldSlice
                      (tempVar, tempExpr) <- mkTempAssign (VecType (htypeSize hwTypeBndr) BitType) sliceExpr
                      return (comment:tempExpr ++ (mkUncondAssign (bndr,hwTypeBndr) (fromSLV hwTypeBndr $ ExprVar tempVar)),[])
                    SPType _ _ -> do
                      dcI <- dataConIndex scrut dc
                      let fieldSlice = typeFieldRange hwTypeScrut dcI selI
                      let sliceExpr = mkSliceExpr (varString scrut) fieldSlice
                      return (comment:(mkUncondAssign (bndr,hwTypeBndr) sliceExpr),[])
                    other -> do
                      error $ "mkConcSm: extractor case" ++ show (hwTypeScrut,selI)
            Nothing -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case: result is not one of the bndrs:\n" ++ pprString expr
        else
          return ([],[])

    _ -> Error.throwError $ $(curLoc) ++ "Not in normal form: not a selector case:\n" ++ pprString expr

mkConcSm (bndr, expr@(Case (Var scrut) _ alts)) = do
  let comment = genComment bndr (pprString expr) []
  scrutHWType <- mkHType scrut
  bndrType    <- mkHType bndr
  scrutExpr   <- varToExpr (Var scrut)
  (enums, cmp) <- case scrutHWType of
    SumType _ enums -> do
      return (map (ExprLit (Just $ htypeSize scrutHWType) . ExprNum . toInteger) [0..(length enums)-1], scrutExpr)
    BitType -> do
      return (map (ExprLit Nothing . ExprBit) [H,L], scrutExpr)
    BoolType -> do
      return (map (ExprLit Nothing . ExprBool) [False,True], scrutExpr)
    SPType _ conArgsPairs -> do
      let conSize = ceiling $ logBase 2 $ fromIntegral $ length conArgsPairs
      let hSize   = htypeSize scrutHWType
      let es      = map (ExprLit (Just conSize) . ExprNum . toInteger) [0..(length conArgsPairs)-1]
      let cmpE    = mkSliceExpr (varString scrut) (hSize-1,hSize-conSize)
      return (es,cmpE)
    other -> error $ "mkConcSm (bndr, expr@(Case (Var scrut) _ _ alts)) " ++ show scrutHWType ++ show scrutExpr
  altcons <- mapM (\(DataAlt dc _, _) -> fmap (enums!!) $ dataConIndex scrut dc) $ tail alts
  (defaultExpr:otherExprs) <- mapM (varToExpr . snd) alts
  let caseExpr = ExprCase cmp (zip (map (:[]) altcons) otherExprs) (Just defaultExpr)
  return (comment:(mkUncondAssign (bndr,bndrType) caseExpr),[])

mkConcSm (bndr, expr@(Case _ _ _)) = Error.throwError $ $(curLoc) ++ "Not in normal form: Case statement does not have a simple variable as scrutinee:\n" ++ pprString expr

mkConcSm (bndr, Literal lit) = do
  bndrType <- mkHType bndr
  i <- case lit of
        Literal.MachInt    integer -> return integer
        Literal.MachInt64  integer -> return integer
        Literal.MachWord   integer -> return integer
        Literal.MachWord64 integer -> return integer
        _                          -> Error.throwError $ $(curLoc) ++ "Not an integer literal:\n" ++ pprString lit
  let comment = genComment bndr (pprString lit) []
  return  (comment:mkUncondAssign (bndr,bndrType) (ExprLit Nothing $ ExprNum i), [])

mkConcSm (bndr, Data dc)
  = genApplication bndr (DataCon.dataConWorkId dc) []

mkConcSm (bndr, expr) = Error.throwError $ $(curLoc) ++ "Not in normal form: let-bound expr is not a Lit, Var, Case or App:\n" ++ pprString expr

genApplication ::
  Var
  -> Var
  -> [Term]
  -> NetlistSession ([Decl],[(Ident,HWType)])
genApplication dst f args =  do
  nonEmptyDst <- hasNonEmptyType dst
  dstType     <- mkHType dst
  if nonEmptyDst
    then do
      if (Var.isGlobalId f)
        then do
          case Var.idDetails f of
            IdInfo.DataConWorkId dc -> do
              args' <- Monad.filterM hasNonEmptyType args
              dcs   <- dataConsFor dst
              case (dcs,args') of
                ([dc],[arg]) -> do
                  let comment = genComment dst (pprString f) args
                  argExpr <- varToExpr arg
                  return (comment:(mkUncondAssign (dst,dstType) argExpr),[])
                others -> do
                  case dstType of
                    SumType _ _ -> error "genApp dataConWork SumType"
                    ProductType _ argTys -> do
                      argTys' <- mapM mkHType args'
                      let comment = genComment dst (pprString f) args
                      args'' <- mapM varToExpr args'
                      let args3 = zipWith toSLV argTys' args''
                      if [dstType] == argTys'
                        then return (comment:(mkUncondAssign (dst,dstType) (head args'')),[])
                        else do
                          case (compare (length argTys) (length args3)) of
                            EQ -> do
                              let comment = genComment dst (pprString f) args
                              return (comment:(mkUncondAssign (dst,dstType) (ExprConcat args3)),[])
                            LT -> Error.throwError $ $(curLoc) ++ "Not in normal form: overapplied constructor: " ++ pprString (dst,f,args) ++ show argTys
                            GT -> Error.throwError $ $(curLoc) ++ "Not in normal form: underapplied constructor: " ++ pprString (dst,f,args') ++ show argTys
                    SPType _ conArgsPairs -> do
                      dcI <- dataConIndex dst dc
                      let argTys = snd . (!! dcI) $ conArgsPairs
                      dcExpr <- dataconToExpr dstType dc
                      args'' <- mapM varToExpr args'
                      case (compare (length argTys) (length args'')) of
                        EQ -> do
                          let comment = genComment dst (pprString f) args
                          return (comment:(mkUncondAssign (dst,dstType) (ExprConcat (dcExpr:args''))), [])
                        LT -> Error.throwError $ $(curLoc) ++ "Not in normal form: overapplied constructor: " ++ pprString (dst,f,args) ++ show argTys
                        GT -> Error.throwError $ $(curLoc) ++ "Not in normal form: underapplied constructor: " ++ pprString (dst,f,args') ++ show argTys
                    BitType -> simpleAssign dstType args'
                    BoolType -> simpleAssign dstType args'
                    other -> error $ "genApp dataConWork: " ++ show other
                    where
                      simpleAssign dstType [] = do
                        expr <- dataconToExpr dstType dc
                        let comment = genComment dst (pprString f) []
                        return ((comment:mkUncondAssign (dst,dstType) expr),[])
                      simpleAssign dstType [v] = do
                        expr <- varToExpr v
                        let comment = genComment dst "" [v]
                        return ((comment:mkUncondAssign (dst,dstType) expr),[])
            IdInfo.DataConWrapId dc -> do
              error "genApp dataConWrap"
            IdInfo.VanillaId -> do
              normalized <- isNormalizedBndr f
              if normalized
                then do
                  vCnt <- LabelM.gets nlVarCnt
                  modu@(Module modName modInps (modOutps:_) _)  <- genModule f Nothing
                  LabelM.puts nlVarCnt vCnt
                  let (clocks,clocksN)  = List.partition ((\a -> case a of (ClockType _) -> True; ResetType _ -> True; _ -> False) . snd) modInps
                  if (length clocks + length args) == (length modInps)
                    then do
                      let dstName = (varString dst)
                      args' <- mapM varToExpr args
                      let clocksAssign = map (\(c,_) -> (c,ExprVar c)) clocks
                      let inpsAssign = zip (map fst clocksN) args'
                      let outpAssign  = (fst modOutps, ExprVar dstName)
                      let comment = genComment dst (pprString f) args
                      return ([comment, InstDecl modName ("comp_inst_" ++ dstName) [] (clocksAssign ++ inpsAssign) [outpAssign]],clocks)
                    else do
                      Error.throwError $ $(curLoc) ++ "Under applied normalized function: " ++ pprString (dst,f,args) ++ show modu
                else do
                  Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has " ++ (if untranslatableHType dstType then "untranslatable" else "translatable") ++ " type: " ++ show dstType
            _ -> Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has type: " ++ show dstType
        else do
          normalized <- isNormalizedBndr f
          if normalized
            then do
              vCnt <- LabelM.gets nlVarCnt
              modu@(Module modName modInps [modOutps] _)  <- genModule f Nothing
              LabelM.puts nlVarCnt vCnt
              let (clocks,clocksN)  = List.partition ((\a -> case a of ClockType _ -> True; ResetType _ -> True; _ -> False) . snd) modInps
              if (length clocks + length args) == (length modInps)
                then do
                  let dstName = (varString dst)
                  args' <- mapM varToExpr args
                  let clocksAssign = map (\(c,_) -> (c,ExprVar c)) clocks
                  let inpsAssign = zip (map fst clocksN) args'
                  let outpAssign  = (fst modOutps, ExprVar dstName)
                  let comment = genComment dst (pprString f) args
                  return ([comment, InstDecl modName ("comp_inst_" ++ dstName) [] (clocksAssign ++ inpsAssign) [outpAssign]],clocks)
                else do
                  Error.throwError $ $(curLoc) ++ "Under applied normalized function: " ++ pprString (dst,f,args) ++ show modu
            else Error.throwError $ $(curLoc) ++ "Using a function that is not normalizable and not a known builtin: " ++ pprString (dst,f,args) ++ "\nWhich has type: " ++ show dstType
    else
      return ([],[])

type BuiltinBuilder =
  Var
  -> [Term]
  -> NetlistSession ([Decl],[(Ident,HWType)])

type BuilderTable = [(String, (Int, BuiltinBuilder))]

builtinBuilders :: BuilderTable
builtinBuilders =
  [ ("xorB"               , (2, genBinaryOperator "xorB" Xor))
  , ("andB"               , (2, genBinaryOperator "andB" And))
  , ("orB"                , (2, genBinaryOperator "orB"  Or ))
  , ("notB"               , (1, genUnaryOperator  "notB" LNeg))
  , ("delay"              , (3, genDelay))
  , ("eqUnsigned"         , (3, \d args -> genBinaryOperator "(==)"  Equals d (tail args)))
  , ("neqUnsigned"        , (3, \d args -> genBinaryOperator "(/=)"  NotEquals d (tail args)))
  , ("plusUnsigned"       , (3, \d args -> genBinaryOperator "(+)" Plus  d (tail args)))
  , ("minUnsigned"        , (3, \d args -> genBinaryOperator "(-)" Minus d (tail args)))
  , ("plusSigned"         , (3, \d args -> genBinaryOperator "(+)" Plus  d (tail args)))
  , ("minSigned"          , (3, \d args -> genBinaryOperator "(-)" Minus d (tail args)))
  , ("timesSigned"        , (3, genTimes))
  , ("negateSigned"       , (2, genNegate))
  , ("unsignedFromInteger", (2, genFromInteger))
  , ("signedFromInteger"  , (2, genFromInteger))
  , ("+>>"                , (2, genShiftIntoL))
  , ("<<+"                , (2, genShiftIntoR))
  , ("+>"                 , (2, genVcons))
  , ("vlast"              , (2, genVlast))
  , ("vinit"              , (2, genVinit))
  , ("singleton"          , (1, genSingleton))
  , ("vcopy"              , (2, genVCopy))
  , ("vcopyn"             , (3, genVCopyn))
  , ("vfoldl"             , (3, genVfoldl))
  , ("vzipWith"           , (4, genVzipWith))
  , ("vmap"               , (2, genVmap))
  , ("!"                  , (3, genIndex))
  , ("vreplace"           , (4, genVreplace))
  , ("Signed"             , (1, \d args -> genFromInteger d (undefined:args)))
  , ("Unsigned"           , (1, \d args -> genFromInteger d (undefined:args)))
  ]

genDelay :: BuiltinBuilder
genDelay state args@[Var initS, clock, Var stateP] = do
  stateTy <- mkHType state
  let [stateName,initSName,statePName] = map varString [state,initS,stateP]
  (clockName,clockPeriod,clockEdge) <- parseClock clock
  let resetName  = clockName ++ "Reset"
  let resetEvent = Event  (ExprVar resetName) AsyncLow
  let resetStmt  = Assign (ExprVar stateName) (ExprVar initSName)
  let clockEvent = Event  (ExprVar clockName) clockEdge
  let clockStmt  = Assign (ExprVar stateName) (ExprVar statePName)
  let register   = ProcessDecl $ Left [(resetEvent,resetStmt),(clockEvent,clockStmt)]
  let comment    = genComment state "delay" args
  return $ ([comment,register],[(clockName,ClockType clockPeriod),(resetName,ResetType clockPeriod)])

parseClock ::
  Term
  -> NetlistSession (Ident,Integer,Edge)
parseClock clock = do
  case clock of
    (App _ _) -> do
      let (Data clockDataCon, [clockNameCString,clockPeriod]) = collectExprArgs clock
      clockFS <- case (filterLiterals clockNameCString) of
            [(Literal.MachStr fs)] -> return fs
            _ -> Error.throwError $ $(curLoc) ++ "Don't know how to handle clock: " ++ pprString clock
      clockPeriod <- case (filterLiterals clockPeriod) of
            [Literal.MachInt    integer] -> return integer
            [Literal.MachInt64  integer] -> return integer
            [Literal.MachWord   integer] -> return integer
            [Literal.MachWord64 integer] -> return integer
            _ -> Error.throwError $ $(curLoc) ++ "Don't know how to handle clock: " ++ pprString clock
      let clockName = FastString.unpackFS clockFS
      case (Name.getOccString clockDataCon) of
        "ClockUp"   -> return (clockName,clockPeriod,PosEdge)
        "ClockDown" -> return (clockName,clockPeriod,NegEdge)
    _ -> Error.throwError $ $(curLoc) ++ "Don't know how to handle clock: " ++ pprString clock

genFromInteger :: BuiltinBuilder
genFromInteger dst [_,arg] = do
  lit <- getIntegerLiteral nlTfpSyn arg
  dstType <- mkHType dst
  litExpr <- case dstType of
        UnsignedType len -> if len < 32 then
            return $ mkUncondAssign (dst,dstType) (ExprFunCall "to_unsigned" [ExprLit Nothing $ ExprNum lit,ExprLit Nothing $ ExprNum $ toInteger len])
          else do
            (tempVar, tempExpr) <- mkTempAssign (SignedType len) (ExprLit (Just len) $ ExprNum lit)
            let assignment = mkUncondAssign (dst,dstType) (ExprFunCall "unsigned" [ExprVar tempVar])
            return (tempExpr ++ assignment)
        SignedType   len -> if len < 32 then
            return $ mkUncondAssign (dst,dstType) (ExprFunCall "to_signed" [ExprLit Nothing $ ExprNum lit,ExprLit Nothing $ ExprNum $ toInteger len])
          else do
            (tempVar, tempExpr) <- mkTempAssign (SignedType len) (ExprLit (Just len) $ ExprNum lit)
            let assignment = mkUncondAssign (dst,dstType) (ExprFunCall "signed" [ExprVar tempVar])
            return (tempExpr ++ assignment)
  let comment = genComment dst "fromInteger" [arg]
  return (comment:litExpr,[])

genShiftIntoL :: BuiltinBuilder
genShiftIntoL dst args@[Var elArg,Var vecArg] = do
  dstType@(VecType len etype) <- mkHType vecArg
  let [elName,vecName] = map (mkVHDLBasicId . varString) [elArg,vecArg]
  let assignExpr = mkUncondAssign (dst,dstType) (ExprConcat [ExprSlice vecName (ExprLit Nothing $ ExprNum $ toInteger (len - 2)) (ExprLit Nothing $ ExprNum 0), ExprVar elName])
  let comment = genComment dst "(+>>)" [Var elArg, Var vecArg]
  return (comment:assignExpr,[])

genShiftIntoR :: BuiltinBuilder
genShiftIntoR dst [Var vecArg,Var elArg] = do
  dstType@(VecType len etype) <- mkHType vecArg
  let [elName,vecName] = map (mkVHDLBasicId . varString) [elArg,vecArg]
  let assignExpr = mkUncondAssign (dst,dstType) (ExprConcat [ExprVar elName, ExprSlice vecName (ExprLit Nothing $ ExprNum $ toInteger (len - 1)) (ExprLit Nothing $ ExprNum 1)])
  let comment = genComment dst "(<<+)" [Var vecArg, Var elArg]
  return (comment:assignExpr,[])

genVlast :: BuiltinBuilder
genVlast dst [_,Var vecArg] = do
  dstType <- mkHType dst
  (VecType len _) <- mkHType (Var vecArg)
  let vecName = (mkVHDLBasicId . varString) vecArg
  let selExpr = mkUncondAssign (dst,dstType) (ExprIndex vecName (ExprLit Nothing $ ExprNum (toInteger $ len - 1)))
  let comment = genComment dst "vlast" [Var vecArg]
  return (comment:selExpr,[])

genVinit :: BuiltinBuilder
genVinit dst [_,Var vecArg] = do
  dstType <- mkHType dst
  (VecType len _) <- mkHType vecArg
  let vecName = (mkVHDLBasicId . varString) vecArg
  let selExpr = mkUncondAssign (dst,dstType) (ExprSlice vecName (ExprLit Nothing $ ExprNum $ toInteger (len - 2)) (ExprLit Nothing $ ExprNum 0))
  let comment = genComment dst "vinit" [Var vecArg]
  return (comment:selExpr,[])

genSingleton :: BuiltinBuilder
genSingleton dst [Var eArg] = do
  dstType <- mkHType dst
  let eName = varString eArg
  let assignExpr = mkUncondAssign (dst,dstType) (ExprAll (ExprVar eName))
  let comment = genComment dst "singleton" [Var eArg]
  return (comment:assignExpr,[])

genVCopy :: BuiltinBuilder
genVCopy dst [_,Var eArg] = do
  dstType <- mkHType dst
  let eName = varString eArg
  let assignExpr = mkUncondAssign (dst,dstType) (ExprAll (ExprVar eName))
  let comment = genComment dst "vcopy" [Var eArg]
  return (comment:assignExpr,[])

genVCopyn :: BuiltinBuilder
genVCopyn dst args = genVCopy dst (tail args)

genVfoldl :: BuiltinBuilder
genVfoldl dst [fArg,Var zArg,Var vArg] = do
  vType@(VecType len etype) <- mkHType vArg
  let comment  = genComment dst "vfoldl" [fArg,Var zArg, Var vArg]
  let vIndexed = map (\i -> (:[]) . Left . Var $ appendToName vArg ("(" ++ show i ++ ")")) $ reverse [0..len-1]
  bndrs        <- mapM mkTempVar (replicate (len-1) dst)
  let bndrs'   = map (Left . Var) (zArg:bndrs)
  let vs       = zipWith (:) bndrs' vIndexed
  let exprs    = map (mkApps fArg) vs
  let tempDecls = map (\v -> NetDecl (varString v) etype Nothing) bndrs
  (assigns,clks) <- fmap (first concat . second concat . unzip) $ mapM mkConcSm $ zip (bndrs++[dst]) exprs
  return (comment:tempDecls ++ assigns,clks)

genVzipWith :: BuiltinBuilder
genVzipWith dst [_,fArg,Var v1Arg,Var v2Arg] = do
  dstType@(VecType len etype) <- mkHType dst
  let comment    = genComment dst "vzipWith" [fArg,Var v1Arg,Var v2Arg]
  let v1Indexed  = map (\i -> Left . Var $ appendToName v1Arg ("(" ++ show i ++ ")")) $ [0..len-1]
  let v2Indexed  = map (\i -> (:[]) . Left . Var $ appendToName v2Arg ("(" ++ show i ++ ")")) $ [0..len-1]
  let vs         = zipWith (:) v1Indexed v2Indexed
  let exprs      = map (mkApps fArg) vs
  bndrs          <- mapM mkTempVar (replicate len dst)
  let tempDecls  = map (\v -> NetDecl (mkVHDLBasicId $ varString v) etype Nothing) bndrs
  (assigns,clks) <- fmap (first concat . second concat . unzip) $ mapM mkConcSm $ zip bndrs exprs
  let assignExpr = mkUncondAssign (dst,dstType) (ExprFunCall "" $ map (ExprVar . mkVHDLBasicId . varString) $ reverse bndrs)
  return (comment : tempDecls ++ assigns ++ assignExpr,clks)

genVmap :: BuiltinBuilder
genVmap dst [fArg,Var vArg] = do
  dstType@(VecType len etype) <- mkHType dst
  let comment    = genComment dst "vmap" [fArg,Var vArg]
  let vIndexed   = map (\i -> (:[]) . Left . Var $ appendToName vArg ("(" ++ show i ++ ")")) $ [0..len-1]
  bndrs          <- mapM mkTempVar (replicate len dst)
  let exprs      = map (mkApps fArg) vIndexed
  let tempDecls  = map (\v -> NetDecl (mkVHDLBasicId $ varString v) etype Nothing) bndrs
  (assigns,clks) <- fmap (first concat . second concat . unzip) $ mapM mkConcSm $ zip bndrs exprs
  let assignExpr = mkUncondAssign (dst,dstType) (ExprFunCall "" $ map (ExprVar . mkVHDLBasicId . varString) $ reverse bndrs)
  return (comment : tempDecls ++ assigns ++ assignExpr,clks)

genIndex :: BuiltinBuilder
genIndex dst [_,Var vecArg,Var iArg] = do
  dstType <- mkHType dst
  let [vecName,iName] = map (mkVHDLBasicId . varString) [vecArg,iArg]
  let selExpr = mkUncondAssign (dst,dstType) (ExprIndex vecName (ExprFunCall "to_integer" [ExprVar iName]))
  let comment = genComment dst "(!)" [Var vecArg,Var iArg]
  return (comment:selExpr,[])

genVreplace :: BuiltinBuilder
genVreplace dst [_,Var vecArg,Var iArg,Var eArg] = do
  dstType@(VecType len _) <- mkHType dst
  let [dstName,vecName,iName,eName] = map (mkVHDLBasicId . varString) [dst,vecArg,iArg,eArg]
  let ifCond = ExprBinary Equals (ExprVar "n") (ExprFunCall "to_integer" [ExprVar iName])
  let thenB = Assign (ExprIndex dstName (ExprVar "n")) (ExprVar eName)
  let elseB = Assign (ExprIndex dstName (ExprVar "n")) (ExprIndex vecName (ExprVar "n"))
  let forSt = ForSt "n" 0 (toInteger $ len - 1) (IfSt ifCond thenB (Just elseB))
  let comment = genComment dst "vreplace" [Var vecArg,Var iArg,Var eArg]
  return ([comment,ProcessDecl (Right [forSt])],[])

genVcons :: BuiltinBuilder
genVcons dst [eArg,vArg] = do
  dstType <- mkHType dst
  let comment = genComment dst "(+>)" [eArg,vArg]
  args' <- mapM varToExpr [vArg,eArg]
  let assignExpr = mkUncondAssign (dst,dstType) (ExprConcat args')
  return (comment:assignExpr,[])

genTimes :: BuiltinBuilder
genTimes dst [_,arg1,arg2] = do
  dstType <- mkHType dst
  let len = (case dstType of UnsignedType l -> l; SignedType l -> l)
  [arg1',arg2'] <- mapM varToExpr [arg1,arg2]
  let comment = genComment dst "(*)" [arg1,arg2]
  return (comment:(mkUncondAssign (dst,dstType) (ExprFunCall "resize" [ExprBinary Times arg1' arg2',ExprLit Nothing $ ExprNum $ fromIntegral len])), [])

genNegate :: BuiltinBuilder
genNegate dst [_,arg] = do
  dstType <- mkHType dst
  arg'    <- varToExpr arg
  case dstType of
    SignedType _ -> genUnaryOperator "-" Neg dst [arg]
    _            -> Error.throwError $ $(curLoc) ++ "Negation is not allowed for type: " ++ show dstType
