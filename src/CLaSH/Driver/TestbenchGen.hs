{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module CLaSH.Driver.TestbenchGen where

-- External Modules
import Control.Monad (zipWithM)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

-- GHC API
import qualified CoreSyn
import qualified FastString
import qualified Id
import qualified Type

-- Internal Modules
import CLaSH.Driver.PrepareBinding (prepareBinding)
import CLaSH.Driver.Types
import CLaSH.Netlist (genNetlist)
import CLaSH.Netlist.Types
import CLaSH.Normalize                (normalize)
import CLaSH.Util (mapAccumLM,secondM)
import CLaSH.Util.CoreHW (Term(..), Var, TypedThing(..), collectExprArgs, varString)
import CLaSH.Util.Pretty (pprString)

genTestbench ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> NetlistState
  -> Var    -- ^ Input stimuli
  -> Module -- ^ Top Entity
  -> DriverSession ([Module], [HWType])
genTestbench globals nlState stimuli (Module modName inps@[modInp,modClock,modReset] [modOutp] _) = do
  stimuli'  <- prepareBinding globals stimuli
  stimuli'' <- termToList (fromJust $ Map.lookup stimuli stimuli')
  stiNames  <- zipWithM (\s e -> Id.mkSysLocalM (FastString.mkFastString s) (getTypeFail e)) (map (("testInput" ++) . show) [0..]) stimuli''
  let stimuli3 = zip stiNames stimuli''
  (nlState',normalized) <- normalizedStimuli (stimuli' `Map.union` (Map.fromList stimuli3)) nlState stiNames
  (decls,signals,mods,hwtypes) <- createStimuli nlState' normalized
  let topDecls = concatMap (genDecl (length signals)) [modInp,modClock,modReset,modOutp]
  let (_,ClockType clockRate) = modClock
  let inpAssign = NetAssign (fst modInp) $ ExprDelay $ zipWith ((,) . ExprVar) signals (iterate (+(fromIntegral clockRate)) 0.0)
  let instDecl  = InstDecl modName "totest" [] (map genPortAssign inps) (map genPortAssign [modOutp])
  return ((Module "testbench" [] [] (instDecl:topDecls ++ inpAssign:decls)):mods,hwtypes)

genTestbench _ _ _ (Module modName inps outps decls) = error $ "Don't know how to make testbench for: " ++ show (modName,inps,outps)

genDecl :: Int -> (Ident,HWType) -> [Decl]
genDecl n (ident,ClockType i) = [ NetDecl ident (ClockType i) (Just $ ExprLit Nothing (ExprBit L))
                              , NetDecl "finished" BitType (Just $ ExprLit Nothing (ExprBit L))
                              , ClockDecl ident i (ExprBinary Equals (ExprVar "finished") (ExprLit Nothing (ExprBit L)))
                              , NetAssign "finished" $ ExprDelay [(ExprLit Nothing (ExprBit H), fromIntegral n)]
                              ]
genDecl _ (ident,ResetType i) = [ NetDecl   ident (ResetType i) (Just $ ExprLit Nothing (ExprBit L))
                              , NetAssign "defaultClockReset" $ ExprDelay [(ExprLit Nothing (ExprBit L), 0.0),(ExprLit Nothing (ExprBit H), (fromIntegral i) / 4.0)]
                              ]
genDecl _ (ident,hwType)    = [ NetDecl ident hwType (Just $ ExprAll (ExprLit Nothing (ExprBit L)))]

genPortAssign (ident,_) = (ident, ExprVar ident)

termToList ::
  Term
  -> DriverSession [Term]
termToList app@(App _ _) = do
  let (fun,args) = collectExprArgs app
  case args of
    [elArg,restArg] -> fmap (elArg:) $ termToList restArg
    others          -> error $ "others" ++ pprString others

termToList tyApp@(TyApp e _) = termToList e
termToList (Data dc)         = return []

normalizedStimuli ::
  Map Var Term
  -> NetlistState
  -> [Var]
  -> DriverSession (NetlistState, [[(Var,Term)]])
normalizedStimuli globals = mapAccumLM (normalize globals)

createStimuli ::
  NetlistState
  -> [[(Var,Term)]]
  -> DriverSession ([Decl], [Ident], [Module], [HWType])
createStimuli nlState normalized = do
  let aapjes = map (varString . fst . head) normalized
  let idents = map ((\(LetRec _ (Var v)) -> v) . snd . head) normalized
  let exprs  = concatMap ((\(LetRec bnds _) -> bnds) . snd . head) normalized
  let exprs' = (\(a,b) -> a ++ b) . List.partition ((`elem` idents) . fst) $ exprs
  let newExpr = (fst . head . head $ normalized, LetRec exprs' (Var . fst . head . head $ normalized))
  ((Module _ _ _ decls):mods,hwtypes) <- genNetlist nlState (newExpr : concatMap tail normalized) (fst . head . head $ normalized)
  return (decls,zipWith (\s i -> varString s ++ "_" ++ show i) idents [0..],mods,hwtypes)

flattenLets :: Term -> [Term]
flattenLets (LetRec binds e) = concatMap (flattenLets . snd) binds
flattenLets e                = [e]
