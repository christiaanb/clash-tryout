{-# LANGUAGE TypeOperators #-}
module CLaSH.Util
  ( module CLaSH.Util

  , module Data.List
  , module Data.Maybe

  , module Control.Arrow

  , module Outputable
  , module Unique
  , module UniqSupply
  )
where

-- External Modules
import Control.Arrow (first, second)
import qualified Control.Monad.Error as Error
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans (MonadTrans, lift)
import Data.Label ((:->))
import qualified Data.Label.PureM as Label
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Language.Haskell.TH as TH

-- GHC API
import Outputable
import Unique
import UniqSupply

makeCached ::
  (State.MonadState s m, Ord k)
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

makeCachedT2 ::
  (MonadTrans t1, MonadTrans t2, State.MonadState s m, Ord k, Monad (t2 m), Monad (t1 (t2 m)))
  => k
  -> s :-> (Map k v)
  -> (t1 (t2 m)) v
  -> (t1 (t2 m)) v
makeCachedT2 key lens create = do
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

takeWhileJust ::
  (a -> Maybe b)
  -> [a]
  -> ([b], [a])
takeWhileJust f = go
  where
    go [] = ([], [])
    go (x:xs) = case f x of
      Nothing -> ([], x:xs)
      Just y  -> first (y:) $ go xs

mapAccumLM ::
  Monad m
  => (acc -> x -> m (acc, y))
  -> acc
  -> [x]
  -> m (acc, [y])
mapAccumLM f = go []
  where
    go ys acc []     = return (acc, reverse ys)
    go ys acc (x:xs) = do
      (acc, y) <- f acc x
      go (y:ys) acc xs

secondM ::
  Functor f
  => (b -> f c)
  -> (a, b)
  -> f (a, c)
secondM f (x,y) = fmap ((,) x) (f y)

firstM ::
  Functor f
  => (a -> f c)
  -> (a, b)
  -> f (c, b)
firstM f (x,y) = fmap (flip (,) $ y) (f x)

