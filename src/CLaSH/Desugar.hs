module CLaSH.Desugar
  ( desugar
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans (lift)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Label as Label
import qualified Data.Label.PureM as LabelM
import Language.KURE (runRewrite)

import Debug.Trace

-- GHC API
import qualified CoreFVs
import qualified CoreSubst
import qualified CoreSyn
import qualified CoreUtils
import qualified Id
import qualified Outputable
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Desugar.Strategy
import CLaSH.Desugar.Types
import CLaSH.Driver.Tools (getGlobalExpr)
import CLaSH.Driver.Types (DriverSession,drUniqSupply)
import CLaSH.Netlist.Constants (builtinIds)
import CLaSH.Util (curLoc, makeCachedT2)
import CLaSH.Util.Core (startContext, nameToString, TypedThing(..))
import CLaSH.Util.Core.Types (tsUniqSupply, tsTransformCounter, emptyTransformState)
import CLaSH.Util.Pretty (pprString)

desugar ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> CoreSyn.CoreBndr
  -> DriverSession (Map CoreSyn.CoreBndr CoreSyn.CoreExpr)
desugar globals bndr = do
  uniqSupply <- LabelM.gets drUniqSupply
  ((retVal,tState),dState) <- State.liftIO $ 
      State.runStateT
        (State.runStateT 
          (Error.runErrorT (desugar' [bndr])) 
          (emptyTransformState uniqSupply)) 
        (emptyDesugarState globals)
  case retVal of
    Left  errMsg -> error errMsg
    Right desugared -> do
      let uniqSupply' = Label.get tsUniqSupply tState
      let transformations = Label.get tsTransformCounter tState
      LabelM.puts drUniqSupply uniqSupply'
      return $ trace ("Desugar transformations: " ++ show transformations) $ (Map.fromList desugared) `Map.union` globals

desugar' ::
  [CoreSyn.CoreBndr]
  -> DesugarSession [(CoreSyn.CoreBndr,CoreSyn.CoreExpr)]
desugar' (bndr:bndrs) = do
  exprMaybe <- (lift . lift) $ getGlobalExpr dsBindings bndr
  case exprMaybe of
    Just expr -> do
      desugaredExpr <- makeCachedT2 bndr dsDesugared $ desugarExpr (show bndr) expr
      let usedBndrs    = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars 
                              (\v -> (not $ Id.isDictId v) && 
                                     (not $ Id.isDataConWorkId v) && 
                                     (not $ Id.isEvVar v) &&
                                     (Id.isDataConId_maybe v == Nothing) &&
                                     (nameToString $ Var.varName v) `notElem` builtinIds) 
                              desugaredExpr
      desugaredUsed <- desugar' usedBndrs
      let desugaredUsedTys = map (getTypeFail . snd) $ filter ((`elem` usedBndrs) . fst) desugaredUsed
      let usedBndrs' = zipWith Var.setVarType usedBndrs desugaredUsedTys
      let desugaredExpr' = foldl doSubstitute desugaredExpr $ zip usedBndrs (map CoreSyn.Var usedBndrs')
      desugaredOthers <- desugar' bndrs
      return ((bndr,desugaredExpr'):(desugaredUsed ++ desugaredOthers))
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ show bndr ++ " is not found."

desugar' [] = return []

desugarExpr ::
  String
  -> CoreSyn.CoreExpr
  -> DesugarSession CoreSyn.CoreExpr
desugarExpr bndrString expr = do
  rewritten <- runRewrite desugarStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'

doSubstitute expr (find, repl) = CoreSubst.substExpr (Outputable.text "substitute") subst expr
  where
    subst = CoreSubst.extendSubst CoreSubst.emptySubst find repl
