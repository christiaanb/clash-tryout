{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module CLaSH.Driver.TestbenchGen where

-- External Modules
import Control.Monad        (zipWithM)
import qualified Data.Label as Label
import qualified Data.List  as List
import Data.Map             (Map)
import qualified Data.Map   as Map
import Data.Maybe           (fromMaybe)

-- GHC API
import qualified CoreSyn
import qualified FastString
import qualified Id
import qualified Type

-- Internal Modules
import CLaSH.Driver.PrepareBinding (prepareBinding)
import CLaSH.Driver.Types
import CLaSH.Netlist               (genNetlist)
import CLaSH.Netlist.Types
import CLaSH.Normalize             (normalize)
import CLaSH.Util                  (curLoc,mapAccumLM,secondM)
import CLaSH.Util.CoreHW           (Term(..), Var, TypedThing(..), collectExprArgs, varString)
import CLaSH.Util.Pretty           (pprString)

genTestbench ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> NetlistState
  -> Maybe Var -- ^ Input stimuli container
  -> Maybe Var -- ^ Expected Output container
  -> Module    -- ^ Top Entity
  -> DriverSession ([Module], [HWType])
genTestbench globals nlState mStimuli mExpectedOutput (Module modName inps [modOutp] _) = do
  (inpDecls,inpMods,inpTypes,nlState',nInps) <- case mStimuli of
    Just stimuli -> do
      (decls,signals,mods,hwtypes,nlState') <- prepareSignals globals nlState stimuli Nothing
      let inpAssign   = case inps of
                          -- Single input and clock
                          [modInp,modClock@(_,ClockType clockRate),modReset] ->
                            (NetAssign (fst modInp) $ ExprDelay $ zipWith ((,) . ExprVar) signals (iterate (+(fromIntegral clockRate)) 0.0)):decls
                          -- Clock only
                          [modClock@(_,ClockType clockRate),modReset] -> decls
                          -- Input only
                          [modInp] -> (NetAssign (fst modInp) (ExprVar $ head signals)):decls
                          -- No input
                          [] -> []
                          _  -> error $ $(curLoc) ++ "Can't make testbench for module with following inputs: " ++ show (modName,inps)
      return (inpAssign,mods,hwtypes,nlState',length signals)
    Nothing -> return ([],[],[],nlState,0)

  (expDecls,expMods,expTypes,nExps) <- case mExpectedOutput of
    Just expectedOutput -> do
      (decls,signals,mods,hwtypes,_) <- prepareSignals globals nlState expectedOutput (Just $ Label.get nlVarCnt nlState')
      let assertStmt = ProcessDecl $ Right $ case inps of
                        -- Single input and clock
                        [modInp,modClock@(_,ClockType clockRate),modReset] -> concat
                                                                              [ [Wait (Just $ fromIntegral clockRate / 2.0)]
                                                                              , List.intersperse (Wait (Just $ fromIntegral clockRate)) $ map (\e -> genAssertion (fst modOutp) e) signals
                                                                              , [Wait Nothing]
                                                                              ]
                        -- Clock only
                        [modClock@(_,ClockType clockRate),modReset]        -> concat
                                                                              [ [Wait (Just $ fromIntegral clockRate / 2.0)]
                                                                              , List.intersperse (Wait (Just $ fromIntegral clockRate)) $ map (\e -> genAssertion (fst modOutp) e) signals
                                                                              , [Wait Nothing]
                                                                              ]
                        -- Input only
                        [modInp]                                           -> [genAssertion (fst modOutp) $ head signals]
                        -- No input
                        []                                                 -> [genAssertion (fst modOutp) $ head signals]
      return (assertStmt:decls,mods,hwtypes,length signals)
    Nothing -> return ([],[],[],0)

  let topDecls = concatMap (genDecl (max nInps nExps)) (modOutp:inps)
  let instDecl = InstDecl modName "totest" [] (map genPortAssign inps) (map genPortAssign [modOutp])

  return ((Module "testBench" [] [] (topDecls ++ instDecl:inpDecls ++ expDecls)):inpMods ++ expMods, List.nub $ inpTypes ++ expTypes)

genTestbench globals nlState mStimuli mExpectedOutput (Module modName inps outps _) =
  error $ $(curLoc) ++ "Can't make testbench for module with multiple outputs: " ++ show (modName,outps)

prepareSignals ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> NetlistState
  -> Var            -- ^ Signal container
  -> Maybe Integer  -- ^ Var counter start
  -> DriverSession ([Decl], [Ident], [Module], [HWType], NetlistState)
prepareSignals globals nlState signals mStart = do
  signals'              <- prepareBinding globals signals
  signals''             <- termToList (fromMaybe (error $ $(curLoc) ++ "Unable to find: " ++ varString signals) $ Map.lookup signals signals')
  sigNames              <- zipWithM (\s e -> Id.mkSysLocalM (FastString.mkFastString s) (getTypeFail e)) (map ((varString signals ++) . show) [0..]) signals''
  let signals3          = zip sigNames signals''
  (nlState',normalized) <- normalizedSignals (signals' `Map.union` (Map.fromList signals3)) nlState sigNames
  createSignals nlState' normalized mStart

createSignals ::
  NetlistState
  -> [[(Var,Term)]] -- ^ Signals
  -> Maybe Integer  -- ^ Var counter start
  -> DriverSession ([Decl], [Ident], [Module], [HWType], NetlistState)
createSignals nlState normalized mStart = do
  let idents  = map ((\(LetRec _ (Var v)) -> v) . snd . head) normalized
  let exprs   = concatMap ((\(LetRec bnds _) -> bnds) . snd . head) normalized
  let exprs'  = (\(a,b) -> a ++ b) . List.partition ((`elem` idents) . fst) $ exprs
  let newExpr = (fst . head . head $ normalized, LetRec exprs' (Var . fst . head . head $ normalized))

  ((Module modName _ _ decls):mods,hwtypes,nlState') <- genNetlist nlState (newExpr : concatMap tail normalized) (fst . head . head $ normalized) mStart
  return (decls,zipWith (\s i -> varString s ++ "_" ++ show i) idents [(fromMaybe 0 mStart)..],mods,hwtypes,nlState')

genDecl ::
  Int
  -> (Ident,HWType)
  -> [Decl]
genDecl n (ident,ClockType i) = [ NetDecl   ident      (ClockType i) (Just $ ExprLit Nothing (ExprBit L))
                                , NetDecl   "finished" BitType (Just $ ExprLit Nothing (ExprBit L))
                                , ClockDecl ident i    (ExprBinary Equals
                                                          (ExprVar "finished")
                                                          (ExprLit Nothing (ExprBit L))
                                                       )
                                , NetAssign "finished" (ExprDelay
                                                          [(ExprLit Nothing (ExprBit H)
                                                          , fromIntegral n)
                                                          ]
                                                       )
                                ]

genDecl _ (ident,ResetType i) = [ NetDecl   ident               (ResetType i) (Just $ ExprLit Nothing (ExprBit L))
                                , NetAssign "defaultClockReset" (ExprDelay
                                                                  [ (ExprLit Nothing (ExprBit L), 0.0)
                                                                  , (ExprLit Nothing (ExprBit H), (fromIntegral i) / 4.0)
                                                                  ]
                                                                )
                                ]

genDecl _ (ident,hwType)      = [ NetDecl ident hwType (Just $ ExprAll (ExprLit Nothing (ExprBit L)))]

genPortAssign ::
  (Ident, HWType)
  -> (Ident, Expr)
genPortAssign (ident,_) = (ident, ExprVar ident)

genAssertion ::
  Ident
  -> Ident
  -> Stmt
genAssertion i1 i2 =
  Assert
    (ExprBinary Equals (ExprVar i1) (ExprVar i2))
    (ExprFunCall "to_string" [ExprVar i1])
    (ExprFunCall "to_string" [ExprVar i2])

termToList ::
  Term
  -> DriverSession [Term]
termToList app@(App _ _) = do
  let (fun,args) = collectExprArgs app
  case args of
    [elArg,restArg] -> fmap (elArg:) $ termToList restArg
    others          -> error $ $(curLoc) ++ "Don't know how to deconstruct string literal: " ++ pprString others

termToList tyApp@(TyApp e _) = termToList e
termToList (Data dc)         = return []

normalizedSignals ::
  Map Var Term
  -> NetlistState
  -> [Var]
  -> DriverSession (NetlistState, [[(Var,Term)]])
normalizedSignals globals = mapAccumLM (normalize globals)

flattenLets :: Term -> [Term]
flattenLets (LetRec binds e) = concatMap (flattenLets . snd) binds
flattenLets e                = [e]
