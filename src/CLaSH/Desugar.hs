module CLaSH.Desugar
  ( desugar
  , desugar'
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
import Debug.Trace (trace)
import Language.KURE (runRewrite)

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
import CLaSH.Util (curLoc, makeCachedT2)
import CLaSH.Util.Core (startContext, nameToString, TypedThing(..))
import CLaSH.Util.Core.Types (tsUniqSupply, tsTransformCounter, emptyTransformState)
import CLaSH.Util.CoreHW.Constants (builtinIds)
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
          (Error.runErrorT (desugar' bndr))
          (emptyTransformState uniqSupply))
        (emptyDesugarState globals)
  case retVal of
    Left  errMsg -> error errMsg
    Right _ -> do
      let uniqSupply'     = Label.get tsUniqSupply tState
      let transformations = Label.get tsTransformCounter tState
      let desugared       = Label.get dsDesugared dState
      let globals'        = Label.get dsBindings dState
      LabelM.puts drUniqSupply uniqSupply'
      return $ trace ("Desugar transformations: " ++ show transformations) $ desugared `Map.union` globals'

desugar' ::
  CoreSyn.CoreBndr
  -> DesugarSession (CoreSyn.CoreBndr,CoreSyn.CoreExpr)
desugar' bndr = do
  exprMaybe <- (lift . lift) $ getGlobalExpr dsBindings bndr
  case exprMaybe of
    Just expr -> do
      desugaredExpr <- makeCachedT2 bndr dsDesugared $ desugarExpr (show bndr) expr
      let bndr'     = Var.setVarType bndr (getTypeFail desugaredExpr)
      return (bndr',desugaredExpr)
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ show bndr ++ " is not found."

desugarExpr ::
  String
  -> CoreSyn.CoreExpr
  -> DesugarSession CoreSyn.CoreExpr
desugarExpr bndrString expr = trace ("desugaring: " ++ bndrString) $ do
  rewritten <- runRewrite desugarStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'
