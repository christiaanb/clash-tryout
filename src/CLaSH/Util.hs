{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
module CLaSH.Util where

import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Label ((:->))
import qualified Data.Label.PureM as Label
import qualified Language.Haskell.TH as TH

makeCached 
  :: (State.MonadState s m, Ord k) 
  => k
  -> s :-> (Map k v)
  -> m v
  -> m v
makeCached key lens create = do
  cache <- Label.gets lens
  case Map.lookup key cache of
    Just value -> return value
    Nothing -> do
      value <- create
      Label.modify lens (Map.insert key value)
      return value

curLoc = do
  (TH.Loc _ _ modName (startPosL,startPosC) _) <- TH.location
  TH.litE (TH.StringL $ modName ++ "(" ++ show startPosL ++ "): ")

errorCurLoc s = do
  (TH.Loc _ _ modName (startPosL,startPosC) _) <- TH.location
  let err = [| error |]
  TH.appE err (TH.litE (TH.StringL $ modName ++ "(" ++ show startPosL ++ "): " ++ s))

liftState
  :: State.MonadState s m
  => s :-> s'
  -> State.State s' a
  -> m a
liftState lens m = do
  st <- Label.gets lens
  let (a,st') = State.runState m st
  Label.puts lens st'
  return a

liftErrorState
  :: (State.MonadState s m, Error.MonadError e m)
  => s :-> s'
  -> Error.ErrorT e (State.State s') a
  -> m a
liftErrorState lens m = do
  st <- Label.gets lens
  let (a,st') = State.runState (Error.runErrorT m) st
  case a of
    Left errMsg -> Error.throwError errMsg
    Right val   -> do  
      Label.puts lens st'
      return val

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a]) 
partitionM _ []     = return ([], []) 
partitionM p (x:xs) = do 
  test      <- p x 
  (ys, ys') <- partitionM p xs 
  return $ if test then (x:ys, ys') else (ys, x:ys') 
  