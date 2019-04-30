{-# LANGUAGE UndecidableInstances, Rank2Types, FlexibleInstances, MultiParamTypeClasses #-}

-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.Logic
-- Copyright   : (c) Dan Doel
-- License     : BSD3
--
-- Maintainer  : dan.doel@gmail.com
-- Stability   : experimental
-- Portability : non-portable (multi-parameter type classes)
--
-- A backtracking, logic programming monad.
--
--    Adapted from the paper
--    /Backtracking, Interleaving, and Terminating
--        Monad Transformers/, by
--    Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry
--    (<http://www.cs.rutgers.edu/~ccshan/logicprog/LogicT-icfp2005.pdf>).
-------------------------------------------------------------------------

module Control.Monad.Logic (
    module Control.Monad.Logic.Class,
    -- * The Logic monad
    Logic,
    logic,
    runLogic,
    observe,
    observeMany,
    observeAll,
    -- * The LogicT monad transformer
    LogicT(..),
    runLogicT,
    observeT,
    observeManyT,
    observeAllT,
    module Control.Monad,
    module Control.Monad.Trans
  ) where

import Control.Applicative

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans

import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class

import Data.Monoid (Monoid(mappend, mempty))
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Control.Monad.Logic.Class

-------------------------------------------------------------------------
-- | A monad transformer for performing backtracking computations
-- layered over another monad 'm'
newtype LogicT m a =
    LogicT { unLogicT :: forall r. (a -> m r -> m r) -> m r -> m r }

-------------------------------------------------------------------------
-- | Extracts the first result from a LogicT computation,
-- failing otherwise.
observeT :: Monad m => LogicT m a -> m a
observeT lt = unLogicT lt (const . return) (fail "No answer.")

-------------------------------------------------------------------------
-- | Extracts all results from a LogicT computation.
observeAllT :: Monad m => LogicT m a -> m [a]
observeAllT m = unLogicT m (liftM . (:)) (return [])

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a LogicT computation.
observeManyT :: Monad m => Int -> LogicT m a -> m [a]
observeManyT n m
    | n <= 0 = return []
    | n == 1 = unLogicT m (\a _ -> return [a]) (return [])
    | otherwise = unLogicT (msplit m) sk (return [])
 where
 sk Nothing _ = return []
 sk (Just (a, m')) _ = (a:) `liftM` observeManyT (n-1) m'

-------------------------------------------------------------------------
-- | Runs a LogicT computation with the specified initial success and
-- failure continuations.
runLogicT :: LogicT m a -> (a -> m r -> m r) -> m r -> m r
runLogicT = unLogicT

-------------------------------------------------------------------------
-- | The basic Logic monad, for performing backtracking computations
-- returning values of type 'a'
type Logic = LogicT Identity

-------------------------------------------------------------------------
-- | A smart constructor for Logic computations.
logic :: (forall r. (a -> r -> r) -> r -> r) -> Logic a
logic f = LogicT $ \k -> Identity .
                         f (\a -> runIdentity . k a . Identity) .
                         runIdentity

-------------------------------------------------------------------------
-- | Extracts the first result from a Logic computation.
observe :: Logic a -> a
observe = runIdentity . observeT 

-------------------------------------------------------------------------
-- | Extracts all results from a Logic computation.
observeAll :: Logic a -> [a]
observeAll = runIdentity . observeAllT

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a Logic computation.
observeMany :: Int -> Logic a -> [a]
observeMany i = runIdentity . observeManyT i

-------------------------------------------------------------------------
-- | Runs a Logic computation with the specified initial success and
-- failure continuations.
runLogic :: Logic a -> (a -> r -> r) -> r -> r
runLogic l s f = runIdentity $ unLogicT l si fi
 where
 si = fmap . s
 fi = Identity f

instance Functor (LogicT f) where
    fmap f lt = LogicT $ \sk fk -> unLogicT lt (sk . f) fk

instance Applicative (LogicT f) where
    pure a = LogicT $ \sk fk -> sk a fk
    f <*> a = LogicT $ \sk fk -> unLogicT f (\g fk' -> unLogicT a (sk . g) fk') fk

instance Alternative (LogicT f) where
    empty = LogicT $ \_ fk -> fk
    f1 <|> f2 = LogicT $ \sk fk -> unLogicT f1 sk (unLogicT f2 sk fk)

instance Monad (LogicT m) where
    return a = LogicT $ \sk fk -> sk a fk
    m >>= f = LogicT $ \sk fk -> unLogicT m (\a fk' -> unLogicT (f a) sk fk') fk
    fail _ = LogicT $ \_ fk -> fk

instance MonadPlus (LogicT m) where
    mzero = LogicT $ \_ fk -> fk
    m1 `mplus` m2 = LogicT $ \sk fk -> unLogicT m1 sk (unLogicT m2 sk fk)

instance MonadTrans LogicT where
    lift m = LogicT $ \sk fk -> m >>= \a -> sk a fk

instance (MonadIO m) => MonadIO (LogicT m) where
    liftIO = lift . liftIO

instance (Monad m) => MonadLogic (LogicT m) where
    msplit m = lift $ unLogicT m ssk (return Nothing)
     where
     ssk a fk = return $ Just (a, (lift fk >>= reflect))

instance (Monad m, F.Foldable m) => F.Foldable (LogicT m) where
    foldMap f m = F.fold $ unLogicT m (liftM . mappend . f) (return mempty)

instance T.Traversable (LogicT Identity) where
    traverse g l = runLogic l (\a ft -> cons <$> g a <*> ft) (pure mzero)
     where cons a l' = return a `mplus` l'

-- Needs undecidable instances
instance MonadReader r m => MonadReader r (LogicT m) where
    ask = lift ask
    local f m = LogicT $ \sk fk -> unLogicT m ((local f .) . sk) (local f fk)

-- Needs undecidable instances
instance MonadState s m => MonadState s (LogicT m) where
    get = lift get
    put = lift . put

-- Needs undecidable instances
instance MonadError e m => MonadError e (LogicT m) where
  throwError = lift . throwError
  catchError m h = LogicT $ \sk fk -> let
      handle r = r `catchError` \e -> unLogicT (h e) sk fk
    in handle $ unLogicT m (\a -> sk a . handle) fk
