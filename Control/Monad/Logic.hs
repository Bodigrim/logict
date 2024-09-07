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
-- ('Control.Monad.mzero' and 'Control.Monad.mplus'),
-- while examples below prefer 'empty' and '<|>'
-- from 'Alternative'.
-------------------------------------------------------------------------

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE Trustworthy           #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid restricted function" #-}

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
    hoistLogicT,
    embedLogicT
  ) where

import Prelude (error, (-))

import Control.Applicative (Alternative(..), Applicative, liftA2, pure, (<*>), (*>))
import Control.Exception (Exception, evaluate, throw)
import Control.Monad (join, MonadPlus(..), Monad(..), fail)
import Control.Monad.Catch (MonadThrow, MonadCatch, throwM, catch)
import Control.Monad.Error.Class (MonadError(..))
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity (Identity(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.State.Class (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Zip (MonadZip (..))

import Data.Bool (Bool (..), otherwise)
import Data.Eq (Eq, (==))
import qualified Data.Foldable as F
import Data.Function (($), (.), const, on)
import Data.Functor (Functor(..), (<$>))
import Data.Int
import qualified Data.List as L
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (Monoid (..))
import Data.Ord (Ord, (<=), (>), compare)
import Data.Semigroup (Semigroup (..))
import qualified Data.Traversable as T
import System.IO.Unsafe (unsafePerformIO)
import Text.Show (Show, showsPrec, showParen, showString, shows)
import Text.Read (Read, readPrec, Lexeme (Ident), parens, lexP, prec, readListPrec, readListPrecDefault)

#if MIN_VERSION_base(4,17,0)
import GHC.IsList (IsList(..))
#else
import GHC.Exts (IsList(..))
#endif

#if MIN_VERSION_base(4,18,0)
import qualified Data.Foldable1 as F1
#endif

import Control.Monad.Logic.Class

-------------------------------------------------------------------------
-- | A monad transformer for performing backtracking computations
-- layered over another monad @m@.
--
-- When @m@ is 'Identity', 'LogicT' @m@ becomes isomorphic to a list
-- (see 'Logic'). Thus 'LogicT' @m@ for non-trivial @m@ can be imagined
-- as a list, pattern matching on which causes monadic effects.
--
-- It's important to remember that 'LogicT' on its own is just
-- a lawful list monad transformer, adding a nondeterministic effect,
-- and its 'Monad' instance behaves just as @instance@ 'Monad' @[]@:
--
-- >>> :set -XOverloadedLists
-- >>> observeMany 9 $ do {x <- [100,200] :: Logic Int; fmap (+x) [1..]}
-- [101,102,103,104,105,106,107,108,109]
-- >>> observeMany 9 $ do {[100,200] >>= \x -> fmap (+x) [1..] :: Logic Int}
-- [101,102,103,104,105,106,107,108,109]
--
-- One should explicitly use methods of 'MonadLogic' such as '(>>-)' and 'interleave'
-- to get fair conjunction / disjunction:
--
-- >>> observeMany 9 $ do {[100,200] >>- \x -> fmap (+x) [1..] :: Logic Int}
-- [101,201,102,202,103,203,104,204,105]
--
-- @since 0.2
newtype LogicT m a =
    LogicT { unLogicT :: forall r. (a -> m r -> m r) -> m r -> m r }

-------------------------------------------------------------------------
-- | Extracts the first result from a 'LogicT' computation,
-- failing if there are no results at all.
--
-- @since 0.2
#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => LogicT m a -> m a
#else
observeT :: Fail.MonadFail m => LogicT m a -> m a
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
--
-- @since 0.2
observeAllT :: Applicative m => LogicT m a -> m [a]
observeAllT m = unLogicT m (fmap . (:)) (pure [])

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a 'LogicT' computation.
--
-- @since 0.2
observeManyT :: Monad m => Int -> LogicT m a -> m [a]
observeManyT n m
    | n <= 0 = return []
    | n == 1 = unLogicT m (\a _ -> return [a]) (return [])
    | otherwise = unLogicT (msplit m) sk (return [])
  where
    sk Nothing _ = return []
    sk (Just (a, m')) _ = (a:) <$> observeManyT (n-1) m'

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
-- @since 0.2
runLogicT :: LogicT m a -> (a -> m r -> m r) -> m r -> m r
runLogicT (LogicT r) = r

-- | Convert from 'LogicT' to an arbitrary logic-like monad transformer,
-- such as <https://hackage.haskell.org/package/list-t list-t>
-- or <https://hackage.haskell.org/package/logict-sequence logict-sequence>
--
-- For example, to show a representation of the structure of a `LogicT`
-- computation, @l@, over a data-like `Monad` (such as @[]@,
-- @Data.Sequence.Seq@, etc.), you could write
--
-- @
-- import ListT (ListT)
--
-- 'Text.Show.show' $ fromLogicT @ListT l
-- @
--
-- @since 0.8.0.0
fromLogicT :: (Alternative (t m), MonadTrans t, Monad m, Monad (t m))
  => LogicT m a -> t m a
fromLogicT = fromLogicTWith lift

-- | Convert from @'LogicT' m@ to an arbitrary logic-like monad,
-- such as @[]@.
--
-- Examples:
--
-- @
-- 'fromLogicT' = fromLogicTWith d
-- 'hoistLogicT' f = fromLogicTWith ('lift' . f)
-- 'embedLogicT' f = 'fromLogicTWith' f
-- @
--
-- The first argument should be a
-- <https://hackage.haskell.org/package/mmorph/docs/Control-Monad-Morph.html monad morphism>.
-- to produce sensible results.
--
-- @since 0.8.0.0
fromLogicTWith :: (Applicative m, Monad n, Alternative n)
  => (forall x. m x -> n x) -> LogicT m a -> n a
fromLogicTWith p (LogicT f) = join . p $
  f (\a v -> pure (pure a <|> join (p v))) (pure empty)

-- | Convert a 'LogicT' computation from one underlying monad to another.
-- For example,
--
-- @
-- hoistLogicT lift :: LogicT m a -> LogicT (StateT m) a
-- @
--
-- The first argument should be a
-- <https://hackage.haskell.org/package/mmorph/docs/Control-Monad-Morph.html monad morphism>.
-- to produce sensible results.
--
-- @since 0.8.0.0
hoistLogicT :: (Applicative m, Monad n) => (forall x. m x -> n x) -> LogicT m a -> LogicT n a
hoistLogicT f = fromLogicTWith (lift . f)

-- | Convert a 'LogicT' computation from one underlying monad to another.
--
-- The first argument should be a
-- <https://hackage.haskell.org/package/mmorph/docs/Control-Monad-Morph.html monad morphism>.
-- to produce sensible results.
--
-- @since 0.8.0.0
embedLogicT :: Applicative m => (forall a. m a -> LogicT n a) -> LogicT m b -> LogicT n b
embedLogicT f = fromLogicTWith f

-------------------------------------------------------------------------
-- | The basic 'Logic' monad, for performing backtracking computations
-- returning values (e.g. 'Logic' @a@ will return values of type @a@).
--
-- It's important to remember that 'Logic' on its own is just
-- a lawful list monad, behaving exactly as @instance@ 'Monad' @[]@.
-- One should explicitly use methods of 'MonadLogic' such as '(>>-)' and 'interleave'
-- to get fair conjunction / disjunction. Note that usual
-- lists have an instance of 'MonadLogic', so maybe you don't need 'Logic' at all.
--
-- __Technical perspective.__
-- 'Logic' is a
-- <http://okmij.org/ftp/tagless-final/course/Boehm-Berarducci.html Boehm-Berarducci encoding>
-- of lists. Speaking plainly, its type is identical (up to 'Identity' wrappers)
-- to 'Data.List.foldr' applied to a given list. And this list itself can be reconstructed
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
-- Here is a systematic derivation of the isomorphism. We start with observing
-- that @[a]@ is isomorphic to a fix point of a non-recursive
-- base algebra @Fix@ (@ListF@ @a@):
--
-- > newtype Fix f = Fix (f (Fix f))
-- > data ListF a r = ConsF a r | NilF deriving (Functor)
-- >
-- > cata :: Functor f => (f r -> r) -> Fix f -> r
-- > cata f = go where go (Fix x) = f (fmap go x)
-- >
-- > from :: [a] -> Fix (ListF a)
-- > from = foldr (\a acc -> Fix (ConsF a acc)) (Fix NilF)
-- >
-- > to :: Fix (ListF a) -> [a]
-- > to = cata (\case ConsF a r -> a : r; NilF -> [])
--
-- Further, @Fix@ (@ListF@ @a@) is isomorphic to Boehm-Berarducci encoding @ListC@ @a@:
--
-- > newtype ListC a = ListC (forall r. (ListF a r -> r) -> r)
-- >
-- > from :: Fix (ListF a) -> ListC a
-- > from xs = ListC (\f -> cata f xs)
-- >
-- > to :: ListC a -> Fix (ListF a)
-- > to (ListC f) = f Fix
--
-- Finally, @ListF@ @a@ @r@ → @r@ is isomorphic to a pair (@a@ → @r@ → @r@, @r@),
-- so @ListC@ is isomorphic to the 'Logic' type modulo 'Identity' wrappers:
--
-- > newtype Logic a = Logic (forall r. (a -> r -> r) -> r -> r)
--
-- And wrapping every occurence of @r@ into @m@ gives us 'LogicT':
--
-- > newtype LogicT m a = Logic (forall r. (a -> m r -> m r) -> m r -> m r)
--
-- @since 0.5.0
type Logic = LogicT Identity

-------------------------------------------------------------------------
-- | A smart constructor for 'Logic' computations.
--
-- @since 0.5.0
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
-- Since 'Logic' is isomorphic to a list, 'observe' is analogous to 'Data.List.head'.
--
-- @since 0.2
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
-- @since 0.2
observeAll :: Logic a -> [a]
observeAll = runIdentity . observeAllT

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a 'Logic' computation.
--
-- >>> let nats = pure 0 <|> fmap (+ 1) nats
-- >>> observeMany 5 nats
-- [0,1,2,3,4]
--
-- Since 'Logic' is isomorphic to a list, 'observeMany' is analogous to 'Data.List.take'.
--
-- @since 0.2
observeMany :: Int -> Logic a -> [a]
observeMany i = L.take i . observeAll
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
-- @since 0.2
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
    m *> k = LogicT $ \sk fk -> unLogicT m (const $ unLogicT k sk) fk

instance Alternative (LogicT f) where
    empty = LogicT $ \_ fk -> fk
    f1 <|> f2 = LogicT $ \sk fk -> unLogicT f1 sk (unLogicT f2 sk fk)

instance Monad (LogicT m) where
    return = pure
    m >>= f = LogicT $ \sk fk -> unLogicT m (\a fk' -> unLogicT (f a) sk fk') fk
    (>>) = (*>)
#if !MIN_VERSION_base(4,13,0)
    fail = Fail.fail
#endif

-- | @since 0.6.0.3
instance Fail.MonadFail (LogicT m) where
    fail _ = LogicT $ \_ fk -> fk

instance MonadPlus (LogicT m) where
  mzero = empty
  mplus = (<|>)

-- | @since 0.7.0.3
instance Semigroup (LogicT m a) where
  (<>) = mplus
#if MIN_VERSION_base(4,18,0)
  sconcat = F1.foldr1 mplus
#else
  sconcat = F.foldr1 mplus
#endif

-- | @since 0.7.0.3
instance Monoid (LogicT m a) where
  mempty = empty
  mappend = (<>)
  mconcat = F.asum

instance MonadTrans LogicT where
    lift m = LogicT $ \sk fk -> m >>= \a -> sk a fk

instance (MonadIO m) => MonadIO (LogicT m) where
    liftIO = lift . liftIO

instance {-# OVERLAPPABLE #-} (Monad m) => MonadLogic (LogicT m) where
    -- 'msplit' is quite costly even if the base 'Monad' is 'Identity'.
    -- Try to avoid it.
    msplit m = lift $ unLogicT m ssk (return Nothing)
     where
     ssk a fk = return $ Just (a, lift fk >>= reflect)
    once m = LogicT $ \sk fk -> unLogicT m (\a _ -> sk a fk) fk
    lnot m = LogicT $ \sk fk -> unLogicT m (\_ _ -> fk) (sk () fk)

instance {-# INCOHERENT #-} MonadLogic Logic where
    -- Same as in the generic instance above
    msplit m = lift $ unLogicT m ssk (return Nothing)
     where
     ssk a fk = return $ Just (a, lift fk >>= reflect)
    once m = LogicT $ \sk fk -> unLogicT m (\a _ -> sk a fk) fk
    lnot m = LogicT $ \sk fk -> unLogicT m (\_ _ -> fk) (sk () fk)

    m >>- f
      | isConstantFailure f = empty
      -- Otherwise apply the default definition from Control.Monad.Logic.Class
      | otherwise = msplit m >>= maybe empty (\(a, m') -> interleave (f a) (m' >>- f))

data MyException = MyException
  deriving (Show)

instance Exception MyException

isConstantFailure :: (a -> Logic b) -> Bool
isConstantFailure f = unsafePerformIO $ do
  let eval foo = runIdentity (unLogicT foo (const $ const $ Identity False) (Identity True))
  evaluate (eval (f (throw MyException))) `catch` (\MyException -> pure False)

-- | @since 0.5.0
instance {-# OVERLAPPABLE #-} (Applicative m, F.Foldable m) => F.Foldable (LogicT m) where
    foldMap f m = F.fold $ unLogicT m (fmap . mappend . f) (pure mempty)

-- | @since 0.5.0
instance {-# INCOHERENT #-} F.Foldable Logic where
    foldr f z m = runLogic m f z

-- A much simpler logic monad representation used to define the Traversable and
-- MonadZip instances. This is essentially the same as ListT from the list-t
-- package, but it uses a slightly more efficient representation: MLView m a is
-- more compact than Maybe (a, ML m a), and the additional laziness in the
-- latter appears to be incidental/historical.
newtype ML m a = ML (m (MLView m a))
  deriving (Functor, F.Foldable, T.Traversable)

data MLView m a = EmptyML | ConsML a (ML m a)
  deriving (Functor, F.Foldable)

instance T.Traversable m => T.Traversable (MLView m) where
  traverse _ EmptyML = pure EmptyML
  traverse f (ConsML x (ML m))
    = liftA2 (\y ym -> ConsML y (ML ym)) (f x) (T.traverse (T.traverse f) m)
  {- The derived instance would write the second case as
   -
   -   traverse f (ConsML x xs) = liftA2 ConsML (f x) (traverse @(ML m) f xs)
   -
   - Inlining the inner traverse gives
   -
   -   traverse f (ConsML x (ML m)) = liftA2 ConsML (f x) (ML <$> traverse (traverse f) m)
   -
   - revealing fmap under liftA2. We fuse those into a single application of liftA2,
   - in case fmap isn't free.
  -}

toML :: Applicative m => LogicT m a -> ML m a
toML (LogicT q) = ML $ q (\a m -> pure $ ConsML a (ML m)) (pure EmptyML)

fromML :: Monad m => ML m a -> LogicT m a
fromML (ML m) = lift m >>= \case
  EmptyML -> empty
  ConsML a xs -> pure a <|> fromML xs

-- | @since 0.5.0
instance {-# OVERLAPPING #-} T.Traversable (LogicT Identity) where
  traverse g l = runLogic l (\a ft -> cons <$> g a <*> ft) (pure empty)
    where
      cons a l' = pure a <|> l'

-- | @since 0.8.0.0
instance {-# OVERLAPPABLE #-} (Monad m, T.Traversable m) => T.Traversable (LogicT m) where
  traverse f = fmap fromML . T.traverse f . toML

zipWithML :: MonadZip m => (a -> b -> c) -> ML m a -> ML m b -> ML m c
zipWithML f = go
    where
      go (ML m1) (ML m2) =
        ML $ mzipWith zv m1 m2
      zv (a `ConsML` as) (b `ConsML` bs) = f a b `ConsML` go as bs
      zv _ _ = EmptyML

unzipML :: MonadZip m => ML m (a, b) -> (ML m a, ML m b)
unzipML (ML m)
    | (l, r) <- munzip (fmap go m)
    = (ML l, ML r)
    where
      go EmptyML = (EmptyML, EmptyML)
      go ((a, b) `ConsML` listab)
        = (a `ConsML` la, b `ConsML` lb)
        where
          -- If the underlying munzip is careful not to leak memory, then we
          -- don't want to defeat it. We need to be sure that la and lb are
          -- realized as selector thunks. Hopefully the CPSish conversion
          -- doesn't muck anything up at another level.
          {-# NOINLINE remains #-}
          {-# NOINLINE la #-}
          {-# NOINLINE lb #-}
          remains = unzipML listab
          (la, lb) = remains

-- | @since 0.8.0.0
instance MonadZip m => MonadZip (LogicT m) where
  mzipWith f xs ys = fromML $ zipWithML f (toML xs) (toML ys)
  munzip xys = case unzipML (toML xys) of
    (xs, ys) -> (fromML xs, fromML ys)

instance MonadReader r m => MonadReader r (LogicT m) where
    ask = lift ask
    local f (LogicT m) = LogicT $ \sk fk -> do
        env <- ask
        local f $ m ((local (const env) .) . sk) (local (const env) fk)

instance MonadState s m => MonadState s (LogicT m) where
    get = lift get
    put = lift . put

-- | @since 0.4
instance MonadError e m => MonadError e (LogicT m) where
  throwError = lift . throwError
  catchError m h = LogicT $ \sk fk -> let
      handle r = r `catchError` \e -> unLogicT (h e) sk fk
    in handle $ unLogicT m (\a -> sk a . handle) fk

instance MonadThrow m => MonadThrow (LogicT m) where
  throwM = lift . throwM

instance MonadCatch m => MonadCatch (LogicT m) where
  catch m h = LogicT $ \sk fk -> let
      handle r = r `catch` \e -> unLogicT (h e) sk fk
    in handle $ unLogicT m (\a -> sk a . handle) fk

instance IsList (Logic a) where
  type Item (Logic a) = a
  fromList xs = LogicT $ \cons nil -> L.foldr cons nil xs
  toList = observeAll

instance Eq a => Eq (Logic a) where
  (==) = (==) `on` observeAll

instance Ord a => Ord (Logic a) where
  compare = compare `on` observeAll

instance Show a => Show (Logic a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

instance Read a => Read (Logic a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault
