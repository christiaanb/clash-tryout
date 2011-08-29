{-# LANGUAGE RelaxedLayout #-}
module CLaSH.Normalize
  ( normalize
  , normalizeMaybe
  , normalizeBndr
  , normalizeExpr
  , desugarArrowExpr
  )
where

-- External Modules
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Label as Label
import Language.KURE (runRewrite)

import Debug.Trace

-- GHC API
import qualified CoreFVs
import qualified CoreSyn
import qualified CoreUtils
import qualified Id
import qualified UniqSupply
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Driver.Types (DriverSession)
import CLaSH.Netlist.Constants
import CLaSH.Netlist.Types
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Normalize.Strategy
import CLaSH.Util
import CLaSH.Util.Core
import CLaSH.Util.Pretty

normalize
  :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> CoreSyn.CoreBndr
  -> DriverSession (Map CoreSyn.CoreBndr CoreSyn.CoreExpr)
normalize binderMap bndr = do
  uniqSupply <- State.liftIO $ UniqSupply.mkSplitUniqSupply 'z'
  let initState = Label.set nsBindings binderMap (emptyNormalizeState uniqSupply)
  (retVal,nState) <- State.liftIO $ State.runStateT (Error.runErrorT (normalize' False [bndr])) initState
  case retVal of
    Left errMsg -> error errMsg
    Right r     -> return $ Label.get nsNormalized nState

normalize'
  :: Bool
  -> [CoreSyn.CoreBndr]
  -> NormalizeSession [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
normalize' nonRepr (bndr:bndrs) = do
  exprMaybe <- getGlobalExpr bndr
  case exprMaybe of
    Just expr' -> do
      (normalizable,expr) <- if (isArrowBinder bndr)
        then do
          desugaredExpr <- desugarArrowExpr (show bndr) expr'
          normalizable  <- isNormalizableE nonRepr desugaredExpr
          return (normalizable,desugaredExpr)
        else do
          normalizable <- isNormalizable nonRepr bndr
          return (normalizable,expr')
      if not normalizable
        then
          Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ show bndr ++ " is not normalizable (" ++ show (CoreUtils.exprType expr) ++ "):\n" ++ pprString expr
        else do
          normalizedExpr <- makeCached bndr nsNormalized $
            normalizeExpr (show bndr) expr
          let usedBndrs    = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars (\v -> (not $ Id.isDictId v) && (nameToString $ Var.varName v) `notElem` builtinIds) normalizedExpr
          normalizedOthers <- normalize' nonRepr (usedBndrs ++ bndrs)
          let normalizedOthers = []
          return ((bndr,normalizedExpr):normalizedOthers)
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ show bndr ++ " is not found."

normalize' _ [] = return []

normalizeMaybe
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession (Maybe (CoreSyn.CoreBndr, CoreSyn.CoreExpr))
normalizeMaybe nonRepr bndr = do
  normBinds <- (normalize' nonRepr [bndr]) `Error.catchError` (\_ -> return [])
  case normBinds of
    [] -> return Nothing
    (normBind:_) -> return (Just normBind)

normalizeBndr
  :: Bool
  -> CoreSyn.CoreBndr
  -> NormalizeSession CoreSyn.CoreExpr
normalizeBndr nonRepr bndr = do
  normBinds <- normalize' nonRepr [bndr]
  return $ snd $ head normBinds

desugarArrowExpr
  :: String
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreExpr
desugarArrowExpr bndr expr = do
  rewritten <- runRewrite arrowDesugarStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'

normalizeExpr
  :: String
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreExpr
normalizeExpr bndr expr = do
  rewritten <- runRewrite normalizeStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'
