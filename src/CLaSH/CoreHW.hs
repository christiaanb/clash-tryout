module CLaSH.CoreHW
  (coreToCoreHW)
where

-- External Modules
import qualified Control.Monad              as Monad
import qualified Control.Monad.Error        as Error
import qualified Control.Monad.Identity     as Identity
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans                     (lift)
import qualified Data.Label                 as Label
import qualified Data.Label.PureM           as LabelM
import Data.Map                                (Map)
import qualified Data.Map                   as Map
import qualified Data.Maybe                 as Maybe

-- GHC API
import qualified CoreFVs
import qualified CoreSyn
import qualified Id
import qualified Var
import qualified VarSet

-- Internal Modules
import CLaSH.Driver.Tools             (getGlobalExpr)
import CLaSH.Driver.Types             (DriverSession, drUniqSupply)
import CLaSH.Util                     (UniqSupply, curLoc, makeCached)
import CLaSH.Util.CoreHW.Constants    (builtinIds)
import CLaSH.Util.CoreHW.CoreToCoreHW (coreExprToTerm)
import CLaSH.Util.CoreHW.FreeVars     (termFreeVars)
import CLaSH.Util.CoreHW.Syntax       (Var, Term)
import CLaSH.Util.CoreHW.Tools        (varString,varStringUniq)
import CLaSH.Util.CoreHW.Transform    (regenUniques)
import CLaSH.Util.CoreHW.Types        (TransformSession, emptyTransformState, tsUniqSupply)
import CLaSH.Util.Pretty

data CoreHWState = CoreHWState
  { _chwTranslated :: Map Var Term
  , _chwBindings   :: Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , _chwUniqSupply :: UniqSupply
  }

Label.mkLabels [''CoreHWState]

type CoreHWSession = State.StateT CoreHWState IO

coreToCoreHW ::
  Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  -> CoreSyn.CoreBndr
  -> DriverSession (Map Var Term)
coreToCoreHW globals bndr = do
  uniqSupply <- LabelM.gets drUniqSupply
  (_,chwState) <- State.liftIO $
    State.runStateT (coreToCoreHW' [bndr]) (CoreHWState Map.empty globals uniqSupply)
  LabelM.puts drUniqSupply (Label.get chwUniqSupply chwState)
  return $ Label.get chwTranslated chwState

coreToCoreHW' ::
  [CoreSyn.CoreBndr]
  -> CoreHWSession [(Var, Term)]
coreToCoreHW' []           = return []
coreToCoreHW' (bndr:bndrs) = do
  exprMaybe <- getGlobalExpr chwBindings bndr
  case exprMaybe of
    Just expr -> do
      unlocatable       <- unlocatableFVs expr
      term              <- makeCached bndr chwTranslated $ coreToCoreHW'' unlocatable expr
      let usedFreeBndrs = VarSet.varSetElems $ VarSet.filterVarSet
                            (\v -> (Var.isId v) &&
                                   (Id.isClassOpId_maybe v == Nothing) &&
                                   (varString v) `notElem` builtinIds)
                            (termFreeVars term)
      translatedUsed    <- coreToCoreHW' usedFreeBndrs
      translatedOthers  <- coreToCoreHW' bndrs
      return ((bndr,term):(translatedUsed ++ translatedOthers))
    Nothing -> fail $ $(curLoc) ++ "Expr belonging to binder: " ++ varStringUniq bndr ++ " is not found."

coreToCoreHW'' ::
  [Var]
  -> CoreSyn.CoreExpr
  -> CoreHWSession Term
coreToCoreHW'' unlocatable expr = do
  us                  <- LabelM.gets chwUniqSupply
  let term            = coreExprToTerm unlocatable expr
  let (retVal,tState) = Identity.runIdentity $
        State.runStateT
          (Error.runErrorT (regenUniques term))
          (emptyTransformState us)
  LabelM.puts chwUniqSupply (Label.get tsUniqSupply tState)
  case retVal of
    Left errMsg -> fail errMsg
    Right term' -> return term'

unlocatableFVs ::
  CoreSyn.CoreExpr
  -> CoreHWSession [Var]
unlocatableFVs e = do
  let usedBndrs = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars
                    (\v -> Var.isGlobalId v &&
                           (Id.isClassOpId_maybe v == Nothing) &&
                           (not $ Id.isDataConWorkId v) &&
                           varString v `notElem` builtinIds
                    ) e
  unlocatable   <- Monad.filterM
                     (\b -> do
                       eMaybe <- getGlobalExpr chwBindings b
                       case eMaybe of
                         Nothing -> return True
                         _       -> return False
                     ) usedBndrs

  return unlocatable
