{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.Driver.Tools
  ( isTopEntity
  , isTestInput
  , isExpectedOutput
  , getGlobalExpr
  , addGlobalBind
  )
where

-- External Modules
import Control.Exception (SomeException,catch)
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import Data.Label ((:->))
import qualified Data.Label.PureM as Label
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (catch)

-- GHC API
import qualified CoreSyn
import qualified Id
import qualified Name
import qualified Var

-- Internal Modules
import CLaSH.Driver.Types
import CLaSH.Util.Core         (nameToString)
import CLaSH.Util.CoreHW       (Var,Term,varStringUniq,builtinIds)
import CLaSH.Util.GHC          (loadExtExpr)
import CLaSH.Util.Pretty       (pprString)

isTopEntity ::
  Var.Var
  -> Bool
isTopEntity bind =
  "topEntity" == (Name.occNameString . Name.nameOccName . Name.getName) bind

isTestInput ::
  Var.Var
  -> Bool
isTestInput bind =
  "testInput" == (Name.occNameString . Name.nameOccName . Name.getName) bind

isExpectedOutput ::
  Var.Var
  -> Bool
isExpectedOutput bind =
  "expectedOutput" == (Name.occNameString . Name.nameOccName . Name.getName) bind

getGlobalExpr ::
  (State.MonadState s m, Error.MonadIO m, Functor m)
  => (s :-> Map CoreSyn.CoreBndr CoreSyn.CoreExpr)
  -> CoreSyn.CoreBndr
  -> m (Maybe CoreSyn.CoreExpr)
getGlobalExpr globalsLens bndr = do
  if ((nameToString $ Var.varName bndr) `elem` builtinIds || Id.isDataConWorkId bndr)
    then do
      return Nothing
    else do
      bindings <- fmap (Map.lookup bndr) $ Label.gets globalsLens
      case bindings of
        Just a  -> return $ Just a
        Nothing -> getExternalExpr globalsLens bndr

getExternalExpr ::
  (State.MonadState s m, Error.MonadIO m)
  => (s :-> Map CoreSyn.CoreBndr CoreSyn.CoreExpr)
  -> CoreSyn.CoreBndr
  -> m (Maybe CoreSyn.CoreExpr)
getExternalExpr globalsLens bndr = do
  if (not $ Var.isLocalVar bndr)
    then do
      exprMaybe <- Error.liftIO $ (loadExtExpr (Var.varName bndr)) `catch` (\(e :: SomeException) -> return Nothing)
      case exprMaybe of
        (Just expr) -> do
          addGlobalBind globalsLens bndr expr
          return (Just expr)
        Nothing     -> return Nothing
    else return Nothing

addGlobalBind ::
  (State.MonadState s m)
  => (s :-> Map CoreSyn.CoreBndr CoreSyn.CoreExpr)
  -> CoreSyn.CoreBndr
  -> CoreSyn.CoreExpr
  -> m ()
addGlobalBind globalsLens bndr expr =
  Label.modify globalsLens (Map.insert bndr expr)
