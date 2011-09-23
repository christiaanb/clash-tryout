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
import CLaSH.Driver.Types (DriverSession,drUniqSupply)
import CLaSH.Driver.Tools (getGlobalExpr)
import CLaSH.Netlist.Constants (builtinIds)
import CLaSH.Netlist.Types (NetlistState)
import CLaSH.Normalize.Strategy
import CLaSH.Normalize.Tools
import CLaSH.Normalize.Types
import CLaSH.Util (curLoc, makeCachedT2)
import CLaSH.Util.Core (nameToString)
import CLaSH.Util.Core.Types (tsTransformCounter, tsUniqSupply, emptyTransformState,
  TypedThing(..))
import CLaSH.Util.Core.Traverse (startContext)
import CLaSH.Util.Pretty (pprString)

-- | Normalize a bndr, errors when unsuccesfull 
normalize ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -- ^ Global binder cache
  -> CoreSyn.CoreBndr
  -- ^ Bdnr to normalize
  -> DriverSession ([(CoreSyn.CoreBndr, CoreSyn.CoreExpr)], NetlistState)
  -- ^ List of normalized binders, and netlist type state 
normalize globals bndr = do
  uniqSupply <- LabelM.gets drUniqSupply
  ((retVal,tState),nState) <- State.liftIO $ 
      State.runStateT
        (State.runStateT 
          (Error.runErrorT (normalize' False [bndr])) 
          (emptyTransformState uniqSupply)) 
        (emptyNormalizeState globals)
  case retVal of
    Left  errMsg -> error errMsg
    Right normalized -> do
      let uniqSupply'     = Label.get tsUniqSupply       tState
      let transformations = Label.get tsTransformCounter tState
      let netlistState    = Label.get nsNetlistState     nState
      LabelM.puts drUniqSupply uniqSupply'
      return $ trace ("Normalize transformations: " ++ show transformations)
        (normalized,netlistState)

normalize' ::
  Bool
  -> [CoreSyn.CoreBndr]
  -> NormalizeSession [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
normalize' nonRepr (bndr:bndrs) = do
  exprMaybe <- (lift . lift) $ getGlobalExpr nsBindings bndr
  case exprMaybe of
    Just expr -> do
      normalizable <- (assertNormalizable nonRepr expr) `Error.catchError`
        ( \e -> do Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ 
                    show bndr ++ " is not normalizable (" ++ 
                    show (getTypeFail expr) ++ "):\n" ++ e
        )
      normalizedExpr <- makeCachedT2 bndr nsNormalized $
        normalizeExpr (show bndr) expr
      let usedBndrs = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars 
                        (\v -> (Var.isId v) &&
                               (not $ Id.isDictId v) && 
                               (not $ Id.isDFunId v) &&
                               (not $ Id.isEvVar v) &&
                               (not $ Id.isDataConWorkId v) &&
                               (Id.isDataConId_maybe v == Nothing) &&
                               (nameToString $ Var.varName v) `notElem` builtinIds) 
                        normalizedExpr
      normalizedOthers <- normalize' nonRepr (usedBndrs ++ bndrs)
      return ((bndr,normalizedExpr):normalizedOthers)
    Nothing -> Error.throwError $ $(curLoc) ++ "Expr belonging to binder: " ++ 
                show bndr ++ " is not found."

normalize' _ [] = return []

normalizeExpr ::
  String
  -> CoreSyn.CoreExpr
  -> NormalizeSession CoreSyn.CoreExpr
normalizeExpr bndrName expr = trace ("normalizing: " ++ bndrName ++ " :: " ++ pprString (getTypeFail expr)) $ do
  rewritten <- runRewrite normalizeStrategy startContext expr
  expr' <- case rewritten of
    Right (expr',_,_) -> return expr'
    Left errMsg       -> Error.throwError $ $(curLoc) ++ errMsg
  return expr'

-- | Normalize a binder (returns Nothing apon failure)
normalizeMaybe ::
  Bool
  -- ^ Expression result is allowed to be non-representable
  -> CoreSyn.CoreBndr
  -- ^ Bndr to normalize
  -> NormalizeSession (Maybe (CoreSyn.CoreBndr, CoreSyn.CoreExpr))
  -- ^ Normalized binder (if succesfull)
normalizeMaybe nonRepr bndr = do
  normBinds <- (normalize' nonRepr [bndr]) `Error.catchError` (\_ -> return [])
  case normBinds of
    []           -> return Nothing
    (normBind:_) -> return (Just normBind)
