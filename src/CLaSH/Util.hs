{-# LANGUAGE TypeOperators #-}
module CLaSH.Util
  ( curLoc
  , makeCached
  , liftErrorState
  , partitionM
  )
where

import qualified Control.Monad.Error as Error
import qualified Control.Monad.State as State
import Control.Monad.Trans
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Label ((:->))
import qualified Data.Label.PureM as Label
import qualified Language.Haskell.TH as TH

makeCached ::
  (MonadTrans t1, MonadTrans t2, State.MonadState s m, Ord k, Monad (t2 m), Monad (t1 (t2 m))) 
  => k
  -> s :-> (Map k v)
  -> (t1 (t2 m)) v
  -> (t1 (t2 m)) v
makeCached key lens create = do
  cache <- (lift . lift) $ Label.gets lens
  case Map.lookup key cache of
    Just value -> return value
    Nothing -> do
      value <- create
      (lift . lift) $ Label.modify lens (Map.insert key value)
      return value

curLoc :: 
  TH.Q TH.Exp
curLoc = do
  (TH.Loc _ _ modName (startPosL,startPosC) _) <- TH.location
  TH.litE (TH.StringL $ modName ++ "(" ++ show startPosL ++ "): ")

liftErrorState ::
  (MonadTrans t1, MonadTrans t2, Monad (t2 m), State.MonadState s m, Error.MonadError e (t1 (t2 m)))
  => s :-> s'
  -> Error.ErrorT e (State.State s') a
  -> (t1 (t2 m)) a
liftErrorState lens m = do
  st <- (lift . lift) $ Label.gets lens
  let (a,st') = State.runState (Error.runErrorT m) st
  case a of
    Left errMsg -> Error.throwError errMsg
    Right val   -> do  
      (lift . lift) $ Label.puts lens st'
      return val

partitionM :: 
  (Monad m) 
  => (a -> m Bool)
  -> [a] 
  -> m ([a], [a]) 
partitionM _ []     = return ([], []) 
partitionM p (x:xs) = do 
  test      <- p x 
  (ys, ys') <- partitionM p xs 
  return $ if test then (x:ys, ys') else (ys, x:ys') 
  