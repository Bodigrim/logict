-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.Logic.Class
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

{-# LANGUAGE CPP #-}
{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid restricted function" #-}

module Control.Monad.Logic.Class (MonadLogic(..), reflect) where

import Prelude ()

import Control.Applicative (Alternative(..), Applicative(..))
import Control.Exception (Exception, evaluate, catch, throw)
import Control.Monad (MonadPlus, Monad(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.State.Lazy as LazyST
import qualified Control.Monad.State.Strict as StrictST
import Data.Bool (Bool(..), otherwise)
import Data.Function (const, ($))
import Data.List (null)
import Data.Maybe (Maybe(..), maybe)
import System.IO.Unsafe (unsafePerformIO)
import Text.Show (Show)

#if MIN_VERSION_mtl(2,3,0)
import qualified Control.Monad.Writer.CPS as CpsW
import qualified Control.Monad.Trans.Writer.CPS as CpsW (writerT, runWriterT)
import Data.Monoid
#endif

-- | A backtracking, logic programming monad.
--
-- This package offers one implementation of 'MonadLogic': 'Control.Monad.Logic.LogicT'.
-- Other notable implementations:
--
-- * https://hackage.haskell.org/package/list-t/docs/ListT.html#t:ListT
-- * https://hackage.haskell.org/package/logict-sequence/docs/Control-Monad-Logic-Sequence.html#t:SeqT
-- * https://hackage.haskell.org/package/logict-state/docs/Control-Monad-LogicState.html#t:LogicStateT
-- * https://hackage.haskell.org/package/streamt/docs/Control-Monad-Stream.html#t:StreamT
--
-- @since 0.2
class (Monad m, Alternative m) => MonadLogic m where
    -- | Attempts to __split__ the computation, giving access to the first
    --   result. Satisfies the following laws:
    --
    --   > msplit empty          == pure Nothing
    --   > msplit (pure a <|> m) == pure (Just (a, m))
    msplit     :: m a -> m (Maybe (a, m a))

    -- | __Fair disjunction.__ It is possible for a logical computation
    --   to have an infinite number of potential results, for instance:
    --
    --   > odds = pure 1 <|> fmap (+ 2) odds
    --
    --   Such computations can cause problems in some circumstances. Consider:
    --
    --   > two = do x <- odds <|> pure 2
    --   >          if even x then pure x else empty
    --
    --   >>> observe two
    --   ...never completes...
    --
    --   Such a computation may never consider 'pure' @2@, and
    --   therefore even 'Control.Monad.Logic.observe' @two@ will
    --   never return any results. By
    --   contrast, using 'interleave' in place of
    --   'Control.Applicative.<|>' ensures fair consideration of both
    --   branches of a disjunction.
    --
    --   > fairTwo = do x <- odds `interleave` pure 2
    --   >              if even x then pure x else empty
    --
    --   >>> observe fairTwo
    --   2
    --
    --   Note that even with 'interleave' this computation will never
    --   terminate after returning 2: only the first value can be
    --   safely observed, after which each odd value becomes 'Control.Applicative.empty'
    --   (equivalent to
    --   <http://lpn.swi-prolog.org/lpnpage.php?pagetype=html&pageid=lpn-htmlse45 Prolog's fail>)
    --   which does not stop the evaluation but indicates there is no
    --   value to return yet.
    --
    --   Unlike '<|>', 'interleave' is not associative:
    --
    --   >>> let x = [1,2,3]; y = [4,5,6]; z = [7,8,9] :: [Int]
    --   >>> x `interleave` y
    --   [1,4,2,5,3,6]
    --   >>> (x `interleave` y) `interleave` z
    --   [1,7,4,8,2,9,5,3,6]
    --   >>> y `interleave` z
    --   [4,7,5,8,6,9]
    --   >>> x `interleave` (y `interleave` z)
    --   [1,4,2,7,3,5,8,6,9]
    --
    interleave :: m a -> m a -> m a

    -- | __Fair conjunction.__ Similarly to the previous function, consider
    --   the distributivity law, naturally expected from 'MonadPlus':
    --
    --   > (a <|> b) >>= k = (a >>= k) <|> (b >>= k)
    --
    --   If @a@ '>>=' @k@ can backtrack arbitrarily many times, @b@ '>>=' @k@
    --   may never be considered. In logic statements,
    --   "backtracking" is the process of discarding the current
    --   possible solution value and returning to a previous decision
    --   point where a new value can be obtained and tried.  For
    --   example:
    --
    --   >>> do { x <- pure 0 <|> pure 1 <|> pure 2; if even x then pure x else empty } :: [Int]
    --   [0,2]
    --
    --   Here, the @x@ value can be produced three times, where
    --   'Control.Applicative.<|>' represents the decision points of that
    --   production.  The subsequent @if@ statement specifies
    --   'Control.Applicative.empty' (fail)
    --   if @x@ is odd, causing it to be discarded and a return
    --   to an 'Control.Applicative.<|>' decision point to get the next @x@.
    --
    --   The statement "@a@ '>>=' @k@ can backtrack arbitrarily many
    --   times" means that the computation is resulting in 'Control.Applicative.empty' and
    --   that @a@ has an infinite number of 'Control.Applicative.<|>' applications to
    --   return to.  This is called a conjunctive computation because
    --   the logic for @a@ /and/ @k@ must both succeed (i.e. 'pure'
    --   a value instead of 'Control.Applicative.empty').
    --
    --   Similar to the way 'interleave' allows both branches of a
    --   disjunctive computation, the '>>-' operator takes care to
    --   consider both branches of a conjunctive computation.
    --
    --   Consider the operation:
    --
    --   > odds = pure 1 <|> fmap (2 +) odds
    --   >
    --   > oddsPlus n = odds >>= \a -> pure (a + n)
    --   >
    --   > g = do x <- (pure 0 <|> pure 1) >>= oddsPlus
    --   >        if even x then pure x else empty
    --
    --   >>> observeMany 3 g
    --   ...never completes...
    --
    --   This will never produce any value because all values produced
    --   by the @do@ program come from the 'pure' @1@ driven operation
    --   (adding one to the sequence of odd values, resulting in the
    --   even values that are allowed by the test in the second line),
    --   but the 'pure' @0@ input to @oddsPlus@ generates an infinite
    --   number of 'Control.Applicative.empty' failures so the even values generated by
    --   the 'pure' @1@ alternative are never seen.  Using
    --   'interleave' here instead of 'Control.Applicative.<|>' does not help due
    --   to the aforementioned distributivity law.
    --
    --   Also note that the @do@ notation desugars to '>>=' bind
    --   operations, so the following would also fail:
    --
    --   > do a <- pure 0 <|> pure 1
    --   >    x <- oddsPlus a
    --   >    if even x then pure x else empty
    --
    --   The solution is to use the '>>-' in place of the normal
    --   monadic bind operation '>>=' when fairness between
    --   alternative productions is needed in a conjunction of
    --   statements (rules):
    --
    --   > h = do x <- (pure 0 <|> pure 1) >>- oddsPlus
    --   >        if even x then pure x else empty
    --
    --   >>> observeMany 3 h
    --   [2,4,6]
    --
    --   However, a bit of care is needed when using '>>-' because,
    --   unlike '>>=', it is not associative.  For example:
    --
    --   >>> let m = [2,7] :: [Int]
    --   >>> let k x = [x, x + 1]
    --   >>> let h x = [x, x * 2]
    --   >>> m >>= (\x -> k x >>= h)
    --   [2,4,3,6,7,14,8,16]
    --   >>> (m >>= k) >>= h -- same as above
    --   [2,4,3,6,7,14,8,16]
    --   >>> m >>- (\x -> k x >>- h)
    --   [2,7,3,8,4,14,6,16]
    --   >>> (m >>- k) >>- h -- central elements are different
    --   [2,7,4,3,14,8,6,16]
    --
    --   This means that the following will be productive:
    --
    --   > (pure 0 <|> pure 1) >>-
    --   >   oddsPlus >>-
    --   >     \x -> if even x then pure x else empty
    --
    --   Which is equivalent to
    --
    --   > ((pure 0 <|> pure 1) >>- oddsPlus) >>-
    --   >   (\x -> if even x then pure x else empty)
    --
    --   But the following will /not/ be productive:
    --
    --   > (pure 0 <|> pure 1) >>-
    --   >   (\a -> (oddsPlus a >>- \x -> if even x then pure x else empty))
    --
    --   Since do notation desugaring results in the latter, the
    --   @RebindableSyntax@ or @QualifiedDo@ language pragmas cannot easily be used
    --   either.  Instead, it is recommended to carefully use explicit
    --   '>>-' only when needed.
    --
    --   Here is an action of '(>>-)' on lists:
    --
    --   >>> take 20 $ [100,200..500] >>- (\x -> map (x +) [1..])
    --   [101,201,102,301,103,202,104,401,105,203,106,302,107,204,108,501,109,205,110,303]
    --
    --   The result is @map (100 +) [1..]@ 'interleave'd
    --   with @[200,300..500] >>- (\x -> map (x +) [1..])@.
    --   You can see that a half of the numbers starts from 1,
    --   a quarter starts from 2, and so on exponentially.
    --   One could argue that `(>>-)` is a very __unfair__ conjunction!
    --
    (>>-)      :: m a -> (a -> m b) -> m b
    infixl 1 >>-

    -- | __Pruning.__ Selects one result out of many. Useful for when multiple
    --   results of a computation will be equivalent, or should be treated as
    --   such.
    --
    --   As an example, here's a way to determine if a number is
    --   <https://wikipedia.org/wiki/Composite_number composite>
    --   (has non-trivial integer divisors, i.e. not a
    --   prime number):
    --
    --   > choose = foldr ((<|>) . pure) empty
    --   >
    --   > divisors n = do a <- choose [2..n-1]
    --   >                 b <- choose [2..n-1]
    --   >                 guard (a * b == n)
    --   >                 pure (a, b)
    --   >
    --   > composite_ v = do _ <- divisors v
    --   >                   pure "Composite"
    --
    --   While this works as intended, it actually does too much work:
    --
    --   >>> observeAll (composite_ 20)
    --   ["Composite", "Composite", "Composite", "Composite"]
    --
    --   Because there are multiple divisors of 20, and they can also
    --   occur in either order:
    --
    --   >>> observeAll (divisors 20)
    --   [(2,10), (4,5), (5,4), (10,2)]
    --
    --   Clearly one could just use 'Control.Monad.Logic.observe' here to get the first
    --   non-prime result, but if the call to @composite@ is in the
    --   middle of other logic code then use 'once' instead.
    --
    --   > composite v = do _ <- once (divisors v)
    --   >                  pure "Composite"
    --
    --   >>> observeAll (composite 20)
    --   ["Composite"]
    --
    once       :: m a -> m a

    -- | __Inverts__ a logic computation. If @m@ succeeds with at least one value,
    --   'lnot' @m@ fails. If @m@ fails, then 'lnot' @m@ succeeds with the value @()@.
    --
    --   For example, evaluating if a number is prime can be based on
    --   the failure to find divisors of a number:
    --
    --   > choose = foldr ((<|>) . pure) empty
    --   >
    --   > divisors n = do d <- choose [2..n-1]
    --   >                 guard (n `rem` d == 0)
    --   >                 pure d
    --   >
    --   > prime v = do _ <- lnot (divisors v)
    --   >              pure True
    --
    --   >>> observeAll (prime 20)
    --   []
    --   >>> observeAll (prime 19)
    --   [True]
    --
    --   Here if @divisors@ never succeeds, then the 'lnot' will
    --   succeed and the number will be declared as prime.
    --
    -- @since 0.7.0.0
    lnot :: m a -> m ()

    -- | Logical __conditional.__ The equivalent of
    --   <http://lpn.swi-prolog.org/lpnpage.php?pagetype=html&pageid=lpn-htmlse44 Prolog's soft-cut>.
    --   If its first argument succeeds at all,
    --   then the results will be fed into the success
    --   branch. Otherwise, the failure branch is taken.  The failure
    --   branch is never considered if the first argument has any
    --   successes.  The 'ifte' function satisfies the following laws:
    --
    --   > ifte (pure a) th el       == th a
    --   > ifte empty th el          == el
    --   > ifte (pure a <|> m) th el == th a <|> (m >>= th)
    --
    --   For example, the previous @prime@ function returned nothing
    --   if the number was not prime, but if it should return 'Data.Bool.False'
    --   instead, the following can be used:
    --
    --   > choose = foldr ((<|>) . pure) empty
    --   >
    --   > divisors n = do d <- choose [2..n-1]
    --   >                 guard (n `rem` d == 0)
    --   >                 pure d
    --   >
    --   > prime v = once (ifte (divisors v)
    --   >                   (const (pure False))
    --   >                   (pure True))
    --
    --   >>> observeAll (prime 20)
    --   [False]
    --   >>> observeAll (prime 19)
    --   [True]
    --
    --   Notice that this cannot be done with a simple @if-then-else@
    --   because @divisors@ either generates values or it does not, so
    --   there's no "false" condition to check with a simple @if@
    --   statement.
    ifte       :: m a -> (a -> m b) -> m b -> m b

    -- All the class functions besides msplit can be derived from msplit, if
    -- desired
    interleave m1 m2 = msplit m1 >>=
                        maybe m2 (\(a, m1') -> pure a <|> interleave m2 m1')

    m >>- f = msplit m >>= maybe empty
      (\(a, m') -> interleave (f a) (m' >>- f))

    ifte t th el = msplit t >>= maybe el (\(a,m) -> th a <|> (m >>= th))

    once m = msplit m >>= maybe empty (\(a, _) -> pure a)

    lnot m = msplit m >>= maybe (pure ()) (const empty)

-------------------------------------------------------------------------------
-- | The inverse of 'msplit'. Satisfies the following law:
--
-- > msplit m >>= reflect == m
--
-- @since 0.2
reflect :: Alternative m => Maybe (a, m a) -> m a
reflect Nothing = empty
reflect (Just (a, m)) = pure a <|> m

-- An instance of MonadLogic for lists
instance MonadLogic [] where
    msplit []     = pure Nothing
    msplit (x:xs) = pure $ Just (x, xs)

    m >>- f
      | isConstantFailure f = []
      -- Otherwise apply the default definition
      | otherwise = msplit m >>= maybe empty (\(a, m') -> interleave (f a) (m' >>- f))

data MyException = MyException
  deriving (Show)

instance Exception MyException

isConstantFailure :: (a -> [b]) -> Bool
isConstantFailure f = unsafePerformIO $
  evaluate (null (f (throw MyException))) `catch` (\MyException -> pure False)

-- | Note that splitting a transformer does
-- not allow you to provide different input
-- to the monadic object returned.
-- For instance, in:
--
-- > let Just (_, rm') = runReaderT (msplit rm) r in runReaderT rm' r'
--
-- @r'@ will be ignored, because @r@ was already threaded through the
-- computation.
instance MonadLogic m => MonadLogic (ReaderT e m) where
    msplit rm = ReaderT $ \e -> do r <- msplit $ runReaderT rm e
                                   case r of
                                     Nothing -> pure Nothing
                                     Just (a, m) -> pure (Just (a, lift m))

#if MIN_VERSION_mtl(2,3,0)
-- | @since 0.8.1.0
instance (Monoid w, MonadLogic m, MonadPlus m) => MonadLogic (CpsW.WriterT w m) where
    msplit wm = CpsW.writerT $ do
      r <- msplit $ CpsW.runWriterT wm
      case r of
        Nothing -> pure (Nothing, mempty)
        Just ((a, w), m) -> pure (Just (a, CpsW.writerT m), w)
#endif

-- | See note on splitting above.
instance (MonadLogic m, MonadPlus m) => MonadLogic (StrictST.StateT s m) where
    msplit sm = StrictST.StateT $ \s ->
                    do r <- msplit (StrictST.runStateT sm s)
                       case r of
                            Nothing          -> pure (Nothing, s)
                            Just ((a,s'), m) ->
                                pure (Just (a, StrictST.StateT (const m)), s')

    interleave ma mb = StrictST.StateT $ \s ->
                        StrictST.runStateT ma s `interleave` StrictST.runStateT mb s

    ma >>- f = StrictST.StateT $ \s ->
                StrictST.runStateT ma s >>- \(a,s') -> StrictST.runStateT (f a) s'

    ifte t th el = StrictST.StateT $ \s -> ifte (StrictST.runStateT t s)
                                                (\(a,s') -> StrictST.runStateT (th a) s')
                                                (StrictST.runStateT el s)

    once ma = StrictST.StateT $ \s -> once (StrictST.runStateT ma s)

-- | See note on splitting above.
instance (MonadLogic m, MonadPlus m) => MonadLogic (LazyST.StateT s m) where
    msplit sm = LazyST.StateT $ \s ->
                    do r <- msplit (LazyST.runStateT sm s)
                       case r of
                            Nothing -> pure (Nothing, s)
                            Just ((a,s'), m) ->
                                pure (Just (a, LazyST.StateT (const m)), s')

    interleave ma mb = LazyST.StateT $ \s ->
                        LazyST.runStateT ma s `interleave` LazyST.runStateT mb s

    ma >>- f = LazyST.StateT $ \s ->
                LazyST.runStateT ma s >>- \(a,s') -> LazyST.runStateT (f a) s'

    ifte t th el = LazyST.StateT $ \s -> ifte (LazyST.runStateT t s)
                                              (\(a,s') -> LazyST.runStateT (th a) s')
                                              (LazyST.runStateT el s)

    once ma = LazyST.StateT $ \s -> once (LazyST.runStateT ma s)
