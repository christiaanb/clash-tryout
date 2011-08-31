module CLaSH.Desugar
  ( desugar
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Label as Label
import qualified Data.Label.PureM as LabelM
import Language.KURE (runRewrite)

import Debug.Trace

-- GHC API
import qualified CoreSyn

-- Internal Modules
import CLaSH.Desugar.Strategy
import CLaSH.Desugar.Types
import CLaSH.Driver.Tools
import CLaSH.Driver.Types
import CLaSH.Util
import CLaSH.Util.Core.Types
import CLaSH.Util.Core.Traverse (startContext)
import CLaSH.Util.Pretty

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
      let uniqSupply' = Label.get tsUniqSupply tState
      let transformations = Label.get tsTransformCounter tState
      let desugared   = Label.get dsDesugared  dState
      LabelM.puts drUniqSupply uniqSupply'
      return $ trace ("Desugar transformations: " ++ show transformations) $ desugared `Map.union` globals

desugar' ::
  CoreSyn.CoreBndr
  -> DesugarSession CoreSyn.CoreExpr
desugar' bndr = do
  exprMaybe <- (lift . lift) $ getGlobalExpr dsBindings bndr
  case exprMaybe of
    Just expr -> do
      desugaredExpr <- makeCached bndr dsDesugared $ desugarExpr (show bndr) expr
      return desugaredExpr
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ show bndr ++ " is not found."

desugarBndr
  :: CoreSyn.CoreBndr
  -> DesugarSession CoreSyn.CoreExpr
desugarBndr bndr = desugar' bndr

desugarExpr
  :: String
  -> CoreSyn.CoreExpr
  -> DesugarSession CoreSyn.CoreExpr
desugarExpr bndrString expr = do
  rewritten <- runRewrite desugarStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'
