-------------------------------------------------------------------------
-- |
-- Module      : Control.Monad.Logic.Class
-- Copyright   : (c) Dan Doel
-- License     : BSD3
-- Maintainer  : Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- A backtracking, logic programming monad.
--
--    Adapted from the paper
--    /Backtracking, Interleaving, and Terminating Monad Transformers/,
--    by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry
--    (<http://okmij.org/ftp/papers/LogicT.pdf>).
-------------------------------------------------------------------------

{-# LANGUAGE CPP  #-}

#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Class (MonadLogic(..), reflect) where

import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as LazyST
import qualified Control.Monad.State.Strict as StrictST

-------------------------------------------------------------------------------
-- | Minimal implementation: msplit
class (MonadPlus m) => MonadLogic m where
    -- | Attempts to split the computation, giving access to the first
    --   result. Satisfies the following laws:
    --
    --   > msplit mzero                == return Nothing
    --   > msplit (return a `mplus` m) == return (Just (a, m))
    msplit     :: m a -> m (Maybe (a, m a))

    -- | Fair disjunction. It is possible for a logical computation
    --   to have an infinite number of potential results, for instance:
    --
    --   > odds = return 1 `mplus` liftM (2+) odds
    --
    --   Such computations can cause problems in some circumstances. Consider:
    --
    --   > do x <- odds `mplus` return 2
    --   >    if even x then return x else mzero
    --
    --   Such a computation may never consider the @return 2@, and
    --   will therefore never return any results. By contrast, using
    --   'interleave' in place of 'mplus' ensures fair consideration
    --   of both branches of a disjunction.
    --
    --   Note that even with 'interleave' this computation will never
    --   terminate after returning 2: only the first value can be
    --   safely observed, after which each odd value becomes 'mzero'
    --   (equivalent to a Prolog @fail@, see
    --   <http://lpn.swi-prolog.org/lpnpage.php?pagetype=html&pageid=lpn-htmlse45>)
    --   which does not stop the evaluation but indicates there is no
    --   value to return yet.
    --
    interleave :: m a -> m a -> m a

    -- | Fair conjunction. Similarly to the previous function, consider
    --   the distributivity law for 'MonadPlus':
    --
    --   > (mplus a b) >>= k = (a >>= k) `mplus` (b >>= k)
    --
    --   If @(a >>= k)@ can backtrack arbitrarily many times, @(b >>=
    --   k)@ may never be considered. In logic statements,
    --   "backtracking" is the process of discarding the current
    --   possible solution value and returning to a previous decision
    --   point where a new value can be obtained and tried.  For
    --   example:
    --
    --   >>> do number <- return 0 `mplus` return 1 `mplus` return 2
    --   >>>    if even x then return x else mzero
    --   [0,2]
    --
    --   Here, the @number@ value can be produced three times, where
    --   the 'mplus' represents the decision points of that
    --   production.  The subsequent @if@ statement specifies 'mzero' (fail)
    --   if the number is odd, causing it to be discarded and a return
    --   to an 'mplus' decision point to get the next @number@.
    --
    --   The statement @(a >>= k)@ "can backtrack arbitrarily many
    --   times" means that the computation is resulting in 'mzero' and
    --   that @a@ has an infinite number of 'mplus' applications to
    --   return to.  This is called a conjunctive computation because
    --   the logic for @a@ /and/ @k@ must both succeed (i.e. 'return'
    --   a value instead of 'mzero').
    --
    --   Similar to the way 'interleave' allows both branches of a
    --   disjunctive computation, the '>>-' operator takes care to
    --   consider both branches of a conjunctive computation.
    --
    --   Consider the operation:
    --
    --   > odds = return 1 `mplus` liftM (2+) odds
    --   >
    --   > oddsPlus n = odds >>= \a -> return (a + n)
    --   >
    --   > do x <- (return 0 `mplus` return 1) >>= oddsPlus
    --   >    if even x then return x else mzero
    --
    --   This will never produce any value because all values come
    --   from the @return 1@ driven operation, but the @return 0@
    --   driven operation generates an infinite number of potential
    --   results.  Using 'interleave' here instead of 'mplus' does not
    --   help due to the MonadPlus distributivity "Left Distribution"
    --   law noted above (see <https://wiki.haskell.org/MonadPlus>).
    --
    --   Also note that the @do@ notation desugars to '>>=' bind
    --   operations, so the following would also fail:
    --
    --   > do a <- return 0 `mplus` return 1
    --   >    x <- oddsPlus a
    --   >    if even x then return x else mzero
    --
    --   Use the '>>-' in place of the normal monadic bind operation
    --   '>>=' like so:
    --
    --   > do x <- (return 0 `mplus` return 1) >>- oddsPlus
    --   >    if even x then return x else mzero
    --
    (>>-)      :: m a -> (a -> m b) -> m b
    infixl 1 >>-

    -- | Logical conditional. The equivalent of Prolog's soft-cut. If its
    --   first argument succeeds at all, then the results will be fed into
    --   the success branch. Otherwise, the failure branch is taken.
    --   satisfies the following laws:
    --
    --   > ifte (return a) th el           == th a
    --   > ifte mzero th el                == el
    --   > ifte (return a `mplus` m) th el == th a `mplus` (m >>= th)
    ifte       :: m a -> (a -> m b) -> m b -> m b

    -- | Pruning. Selects one result out of many. Useful for when multiple
    --   results of a computation will be equivalent, or should be treated as
    --   such.
    once       :: m a -> m a

    -- | Inverts a logic computation. If @m@ succeeds with at least one value,
    --   @lnot m@ fails. If @m@ fails, then @lnot m@ succeeds with the value @()@.
    lnot :: m a -> m ()

    -- All the class functions besides msplit can be derived from msplit, if
    -- desired
    interleave m1 m2 = msplit m1 >>=
                        maybe m2 (\(a, m1') -> return a `mplus` interleave m2 m1')

    m >>- f = do (a, m') <- maybe mzero return =<< msplit m
                 interleave (f a) (m' >>- f)

    ifte t th el = msplit t >>= maybe el (\(a,m) -> th a `mplus` (m >>= th))

    once m = do (a, _) <- maybe mzero return =<< msplit m
                return a

    lnot m = ifte (once m) (const mzero) (return ())


-------------------------------------------------------------------------------
-- | The inverse of msplit. Satisfies the following law:
--
-- > msplit m >>= reflect == m
reflect :: MonadLogic m => Maybe (a, m a) -> m a
reflect Nothing = mzero
reflect (Just (a, m)) = return a `mplus` m

-- An instance of MonadLogic for lists
instance MonadLogic [] where
    msplit []     = return Nothing
    msplit (x:xs) = return $ Just (x, xs)

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
                                     Nothing -> return Nothing
                                     Just (a, m) -> return (Just (a, lift m))

-- | See note on splitting above.
instance MonadLogic m => MonadLogic (StrictST.StateT s m) where
    msplit sm = StrictST.StateT $ \s ->
                    do r <- msplit (StrictST.runStateT sm s)
                       case r of
                            Nothing          -> return (Nothing, s)
                            Just ((a,s'), m) ->
                                return (Just (a, StrictST.StateT (\_ -> m)), s')

    interleave ma mb = StrictST.StateT $ \s ->
                        StrictST.runStateT ma s `interleave` StrictST.runStateT mb s

    ma >>- f = StrictST.StateT $ \s ->
                StrictST.runStateT ma s >>- \(a,s') -> StrictST.runStateT (f a) s'

    ifte t th el = StrictST.StateT $ \s -> ifte (StrictST.runStateT t s)
                                                (\(a,s') -> StrictST.runStateT (th a) s')
                                                (StrictST.runStateT el s)

    once ma = StrictST.StateT $ \s -> once (StrictST.runStateT ma s)

-- | See note on splitting above.
instance MonadLogic m => MonadLogic (LazyST.StateT s m) where
    msplit sm = LazyST.StateT $ \s ->
                    do r <- msplit (LazyST.runStateT sm s)
                       case r of
                            Nothing -> return (Nothing, s)
                            Just ((a,s'), m) ->
                                return (Just (a, LazyST.StateT (\_ -> m)), s')

    interleave ma mb = LazyST.StateT $ \s ->
                        LazyST.runStateT ma s `interleave` LazyST.runStateT mb s

    ma >>- f = LazyST.StateT $ \s ->
                LazyST.runStateT ma s >>- \(a,s') -> LazyST.runStateT (f a) s'

    ifte t th el = LazyST.StateT $ \s -> ifte (LazyST.runStateT t s)
                                              (\(a,s') -> LazyST.runStateT (th a) s')
                                              (LazyST.runStateT el s)

    once ma = LazyST.StateT $ \s -> once (LazyST.runStateT ma s)
