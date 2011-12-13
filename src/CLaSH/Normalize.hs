module CLaSH.Normalize
  ( normalize
  , normalizeMaybe
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
import Debug.Trace (trace)

-- GHC API
import qualified CoreFVs
import qualified CoreSyn
import qualified CoreUtils
import qualified Id
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Driver.Types        (DriverSession, drUniqSupply)
import CLaSH.Netlist.Types       (NetlistState)
import CLaSH.Normalize.Strategy
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util                (curLoc, makeCachedT2)
import CLaSH.Util.CoreHW         (Var, Term, varString, startContext, tsTransformCounter, tsUniqSupply, emptyTransformState, TypedThing(..), termSomeFreeVars, builtinIds)
import CLaSH.Util.Pretty         (pprString)

-- | Normalize a bndr, errors when unsuccesfull
normalize ::
  Map Var Term
  -- ^ Global binder cache
  -> NetlistState
  -- ^ Current netlist state
  -> Var
  -- ^ Bdnr to normalize
  -> DriverSession (NetlistState, [(Var, Term)])
  -- ^ List of normalized binders, and netlist type state
normalize globals nlState bndr = do
  uniqSupply <- LabelM.gets drUniqSupply
  ((retVal,tState),nState) <- State.liftIO $
      State.runStateT
        (State.runStateT
          (Error.runErrorT (normalize' False [bndr]))
          (emptyTransformState uniqSupply))
        (emptyNormalizeState globals nlState)
  case retVal of
    Left  errMsg -> error errMsg
    Right normalized -> do
      let uniqSupply'     = Label.get tsUniqSupply       tState
      let transformations = Label.get tsTransformCounter tState
      let netlistState    = Label.get nsNetlistState     nState
      LabelM.puts drUniqSupply uniqSupply'
      return $ trace ("Normalize transformations: " ++ show transformations)
        (netlistState,normalized)

normalize' ::
  Bool
  -> [Var]
  -> NormalizeSession [(Var, Term)]
normalize' nonRepr (bndr:bndrs) = do
  globalBindings <- (lift . lift) $ LabelM.gets nsBindings
  exprMaybe <- getGlobalExpr bndr
  case exprMaybe of
    Just expr -> do
      normalizable <- (assertNormalizable nonRepr expr) `Error.catchError`
        (\e -> trace ( "\n== Warning ==\n" ++ $(curLoc) ++ "Expr belonging to binder '" ++ show bndr ++
                       "', having type:\n\n" ++ pprString (getTypeFail expr) ++
                       "\n\nis not normalizable, because:\n" ++ e ++ "\n"
                     ) $ return False
        )
      if normalizable then do
          normalizedExpr <- makeCachedT2 bndr nsNormalized $
            normalizeExpr (varString bndr) expr
          let usedBndrs = VarSet.varSetElems $ termSomeFreeVars
                            (\v -> (Var.isId v) &&
                                   (not $ Id.isDictId v) &&
                                   (not $ Id.isDFunId v) &&
                                   (not $ Id.isEvVar v) &&
                                   (not $ Id.isDataConWorkId v) &&
                                   (Id.isClassOpId_maybe v == Nothing) &&
                                   (Id.isDataConId_maybe v == Nothing) &&
                                   (varString v) `notElem` builtinIds)
                            normalizedExpr
          normalizedOthers <- normalize' nonRepr (usedBndrs ++ bndrs)
          return ((bndr,normalizedExpr):normalizedOthers)
        else
          normalize' nonRepr bndrs
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++
                show bndr ++ " is not found.: " ++ pprString globalBindings

normalize' _ [] = return []

normalizeExpr ::
  String
  -> Term
  -> NormalizeSession Term
normalizeExpr bndrName expr = trace ("normalizing: " ++ bndrName) $  do
  rewritten <- runRewrite normalizeStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'

-- | Normalize a binder (returns Nothing apon failure)
normalizeMaybe ::
  Bool
  -- ^ Expression result is allowed to be non-representable
  -> Var
  -- ^ Bndr to normalize
  -> NormalizeSession (Maybe (Var, Term))
  -- ^ Normalized binder (if succesfull)
normalizeMaybe nonRepr bndr = do
  normBinds <- (normalize' nonRepr [bndr]) `Error.catchError` (\e -> trace ("normalizeMaybe fail: " ++ e) $ return [])
  case normBinds of
    []           -> return Nothing
    (normBind:_) -> return (Just normBind)
