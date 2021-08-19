-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.Logic
-- Copyright   : (c) 2007-2014 Dan Doel,
--               (c) 2011-2013 Edward Kmett,
--               (c) 2014      Roman Cheplyaka,
--               (c) 2020-2021 Andrew Lelechenko,
--               (c) 2020-2021 Kevin Quick
-- License     : BSD3
-- Maintainer  : Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Adapted from the paper
-- <http://okmij.org/ftp/papers/LogicT.pdf Backtracking, Interleaving, and Terminating Monad Transformers>
-- by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry.
-- Note that the paper uses 'MonadPlus' vocabulary
-- ('mzero' and 'mplus'),
-- while examples below prefer 'empty' and '<|>'
-- from 'Alternative'.
-------------------------------------------------------------------------

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

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
    fromLogicT,
    fromLogicTWith,
    module Control.Monad,
    module Trans
  ) where

import Control.Applicative

import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity (Identity(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.Trans as Trans

import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.State.Class (MonadState(..))
import Control.Monad.Error.Class (MonadError(..))

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid (..))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup (..))
#endif

import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Control.Monad.Logic.Class

-------------------------------------------------------------------------
-- | A monad transformer for performing backtracking computations
-- layered over another monad @m@.
--
-- When @m@ is 'Identity', 'LogicT' @m@ becomes isomorphic to a list
-- (see 'Logic'). Thus 'LogicT' @m@ for non-trivial @m@ can be imagined
-- as a list, pattern matching on which causes monadic effects.
--
newtype LogicT m a =
    LogicT { unLogicT :: forall r. (a -> m r -> m r) -> m r -> m r }

-------------------------------------------------------------------------
-- | Extracts the first result from a 'LogicT' computation,
-- failing if there are no results at all.
#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => LogicT m a -> m a
#else
observeT :: MonadFail m => LogicT m a -> m a
#endif
observeT lt = unLogicT lt (const . return) (fail "No answer.")

-------------------------------------------------------------------------
-- | Extracts all results from a 'LogicT' computation, unless blocked by the
-- underlying monad.
--
-- For example, given
--
-- >>> let nats = pure 0 <|> fmap (+ 1) nats
--
-- some monads (like 'Identity', 'Control.Monad.Reader.Reader',
-- 'Control.Monad.Writer.Writer', and 'Control.Monad.State.State')
-- will be productive:
--
-- >>> take 5 $ runIdentity (observeAllT nats)
-- [0,1,2,3,4]
--
-- but others (like 'Control.Monad.Except.ExceptT',
-- and 'Control.Monad.Cont.ContT') will not:
--
-- >>> take 20 <$> runExcept (observeAllT nats)
--
-- In general, if the underlying monad manages control flow then
-- 'observeAllT' may be unproductive under infinite branching,
-- and 'observeManyT' should be used instead.
observeAllT :: Applicative m => LogicT m a -> m [a]
observeAllT m = unLogicT m (fmap . (:)) (pure [])

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a 'LogicT' computation.
observeManyT :: Monad m => Int -> LogicT m a -> m [a]
observeManyT n m
    | n <= 0 = return []
    | n == 1 = unLogicT m (\a _ -> return [a]) (return [])
    | otherwise = unLogicT (msplit m) sk (return [])
 where
 sk Nothing _ = return []
 sk (Just (a, m')) _ = (a:) `liftM` observeManyT (n-1) m'

-------------------------------------------------------------------------
-- | Runs a 'LogicT' computation with the specified initial success and
-- failure continuations.
--
-- The second argument ("success continuation") takes one result of
-- the 'LogicT' computation and the monad to run for any subsequent
-- matches.
--
-- The third argument ("failure continuation") is called when the
-- 'LogicT' cannot produce any more results.
--
-- For example:
--
-- >>> yieldWords = foldr ((<|>) . pure) empty
-- >>> showEach wrd nxt = putStrLn wrd >> nxt
-- >>> runLogicT (yieldWords ["foo", "bar"]) showEach (putStrLn "none!")
-- foo
-- bar
-- none!
-- >>> runLogicT (yieldWords []) showEach (putStrLn "none!")
-- none!
-- >>> showFirst wrd _ = putStrLn wrd
-- >>> runLogicT (yieldWords ["foo", "bar"]) showFirst (putStrLn "none!")
-- foo
--
runLogicT :: LogicT m a -> (a -> m r -> m r) -> m r -> m r
runLogicT (LogicT r) = r

-- | Convert from 'LogicT' to an arbitrary logic-like monad transformer,
-- such as <https://hackage.haskell.org/package/logict-sequence logict-sequence>
#if MIN_VERSION_base(4,8,0)
fromLogicT :: (Alternative (t m), MonadTrans t, Monad m, Monad (t m))
  => LogicT m a -> t m a
#else
fromLogicT :: (Alternative (t m), MonadTrans t, Applicative m, Monad m, Monad (t m))
  => LogicT m a -> t m a
#endif
fromLogicT = fromLogicTWith lift

-- | Convert from @'LogicT' m@ to an arbitrary logic-like monad,
-- such as @[]@.
-- The first argument should be a
-- <https://hackage.haskell.org/package/mmorph/docs/Control-Monad-Morph.html monad morphism>.
-- to produce sensible results.
fromLogicTWith :: (Applicative m, Monad n, Alternative n)
  => (forall x. m x -> n x) -> LogicT m a -> n a
fromLogicTWith p (LogicT f) = join . p $
  f (\a v -> pure (pure a <|> join (p v))) (pure empty)

-------------------------------------------------------------------------
-- | The basic 'Logic' monad, for performing backtracking computations
-- returning values (e.g. 'Logic' @a@ will return values of type @a@).
--
-- __Technical perspective.__
-- 'Logic' is a
-- <http://okmij.org/ftp/tagless-final/course/Boehm-Berarducci.html Boehm-Berarducci encoding>
-- of lists. Speaking plainly, its type is identical (up to 'Identity' wrappers)
-- to 'foldr' applied to a given list. And this list itself can be reconstructed
-- by supplying @(:)@ and @[]@.
--
-- > import Data.Functor.Identity
-- >
-- > fromList :: [a] -> Logic a
-- > fromList xs = LogicT $ \cons nil -> foldr cons nil xs
-- >
-- > toList :: Logic a -> [a]
-- > toList (LogicT fld) = runIdentity $ fld (\x (Identity xs) -> Identity (x : xs)) (Identity [])
--
type Logic = LogicT Identity

-------------------------------------------------------------------------
-- | A smart constructor for 'Logic' computations.
logic :: (forall r. (a -> r -> r) -> r -> r) -> Logic a
logic f = LogicT $ \k -> Identity .
                         f (\a -> runIdentity . k a . Identity) .
                         runIdentity

-------------------------------------------------------------------------
-- | Extracts the first result from a 'Logic' computation, failing if
-- there are no results.
--
-- >>> observe (pure 5 <|> pure 3 <|> empty)
-- 5
--
-- >>> observe empty
-- *** Exception: No answer.
--
-- Since 'Logic' is isomorphic to a list, 'observe' is analogous to 'head'.
--
observe :: Logic a -> a
observe lt = runIdentity $ unLogicT lt (const . pure) (error "No answer.")

-------------------------------------------------------------------------
-- | Extracts all results from a 'Logic' computation.
--
-- >>> observeAll (pure 5 <|> empty <|> empty <|> pure 3 <|> empty)
-- [5,3]
--
-- 'observeAll' reveals a half of the isomorphism between 'Logic'
-- and lists. See description of 'runLogic' for the other half.
--
observeAll :: Logic a -> [a]
observeAll = runIdentity . observeAllT

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a 'Logic' computation.
--
-- >>> let nats = pure 0 <|> fmap (+ 1) nats
-- >>> observeMany 5 nats
-- [0,1,2,3,4]
--
-- Since 'Logic' is isomorphic to a list, 'observeMany' is analogous to 'take'.
--
observeMany :: Int -> Logic a -> [a]
observeMany i = take i . observeAll
-- Implementing 'observeMany' using 'observeManyT' is quite costly,
-- because it calls 'msplit' multiple times.

-------------------------------------------------------------------------
-- | Runs a 'Logic' computation with the specified initial success and
-- failure continuations.
--
-- >>> runLogic empty (+) 0
-- 0
--
-- >>> runLogic (pure 5 <|> pure 3 <|> empty) (+) 0
-- 8
--
-- When invoked with @(:)@ and @[]@ as arguments, reveals
-- a half of the isomorphism between 'Logic' and lists.
-- See description of 'observeAll' for the other half.
--
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
    return = pure
    m >>= f = LogicT $ \sk fk -> unLogicT m (\a fk' -> unLogicT (f a) sk fk') fk
#if !MIN_VERSION_base(4,13,0)
    fail = Fail.fail
#endif

instance Fail.MonadFail (LogicT m) where
    fail _ = LogicT $ \_ fk -> fk

instance MonadPlus (LogicT m) where
  mzero = empty
  mplus = (<|>)

#if MIN_VERSION_base(4,9,0)
instance Semigroup (LogicT m a) where
  (<>) = mplus
  sconcat = foldr1 mplus
#endif

instance Monoid (LogicT m a) where
  mempty = empty
#if MIN_VERSION_base(4,9,0)
  mappend = (<>)
#else
  mappend = (<|>)
#endif
  mconcat = F.asum

instance MonadTrans LogicT where
    lift m = LogicT $ \sk fk -> m >>= \a -> sk a fk

instance (MonadIO m) => MonadIO (LogicT m) where
    liftIO = lift . liftIO

instance (Monad m) => MonadLogic (LogicT m) where
    -- 'msplit' is quite costly even if the base 'Monad' is 'Identity'.
    -- Try to avoid it.
    msplit m = lift $ unLogicT m ssk (return Nothing)
     where
     ssk a fk = return $ Just (a, lift fk >>= reflect)
    once m = LogicT $ \sk fk -> unLogicT m (\a _ -> sk a fk) fk
    lnot m = LogicT $ \sk fk -> unLogicT m (\_ _ -> fk) (sk () fk)

#if MIN_VERSION_base(4,8,0)

instance {-# OVERLAPPABLE #-} (Applicative m, F.Foldable m) => F.Foldable (LogicT m) where
    foldMap f m = F.fold $ unLogicT m (fmap . mappend . f) (pure mempty)

instance {-# OVERLAPPING #-} F.Foldable (LogicT Identity) where
    foldr f z m = runLogic m f z

#else

instance (Applicative m, F.Foldable m) => F.Foldable (LogicT m) where
    foldMap f m = F.fold $ unLogicT m (fmap . mappend . f) (pure mempty)

#endif

instance T.Traversable (LogicT Identity) where
  traverse g l = runLogic l (\a ft -> cons <$> g a <*> ft) (pure empty)
    where
      cons a l' = pure a <|> l'

-- Needs undecidable instances
instance MonadReader r m => MonadReader r (LogicT m) where
    ask = lift ask
    local f (LogicT m) = LogicT $ \sk fk -> do
        env <- ask
        local f $ m ((local (const env) .) . sk) (local (const env) fk)

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
