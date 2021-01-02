{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import           Test.Tasty
import           Test.Tasty.HUnit

import           Control.Arrow ( left )
import           Control.Exception
import           Control.Monad.Identity
import           Control.Monad.Logic
import           Control.Monad.Reader
import qualified Control.Monad.State.Lazy as SL
import qualified Control.Monad.State.Strict as SS
import           Data.Maybe

#ifdef MIN_VERSION_tasty_expected_failure
import           Test.Tasty.ExpectedFailure
#endif

#if MIN_VERSION_base(4,9,0)
#if MIN_VERSION_base(4,11,0)
#else
import           Data.Semigroup (Semigroup (..))
#endif
#else
import           Data.Monoid
#endif

import           TestRebindableSyntax


monadReader1 :: Assertion
monadReader1 = assertEqual "should be equal" [5 :: Int] $
  runReader (observeAllT (local (+ 5) ask)) 0

monadReader2 :: Assertion
monadReader2 = assertEqual "should be equal" [(5, 0)] $
  runReader (observeAllT foo) 0
  where
    foo :: MonadReader Int m => m (Int,Int)
    foo = do
      x <- local (5+) ask
      y <- ask
      return (x,y)

monadReader3 :: Assertion
monadReader3 = assertEqual "should be equal" [5,3] $
  runReader (observeAllT (plus5 `mplus` mzero `mplus` plus3)) (0 :: Int)
  where
    plus5 = local (5+) ask
    plus3 = local (3+) ask

nats, odds, oddsOrTwo,
  oddsOrTwoUnfair, oddsOrTwoFair,
  odds5down :: Monad m => LogicT m Integer

#if MIN_VERSION_base(4,8,0)
nats = pure 0 `mplus` ((1 +) <$> nats)
#else
nats = return 0 `mplus` liftM (1 +) nats
#endif

odds = return 1 `mplus` liftM (2+) odds

oddsOrTwoUnfair = odds `mplus` return 2
oddsOrTwoFair   = odds `interleave` return 2

oddsOrTwo = do x <- oddsOrTwoFair
               if even x then once (return x) else mzero

odds5down = return 5 `mplus` mempty `mplus` mempty `mplus` return 3 `mplus` return 1

yieldWords :: [String] -> LogicT m String
yieldWords = go
  where go [] = mzero
        go (w:ws) = return w `mplus` go ws


main :: IO ()
main = defaultMain $
  localOption (mkTimeout 1000000) $  -- 1 second
  testGroup "All"
  [ testGroup "Monad Reader + env"
    [ testCase "Monad Reader 1" monadReader1
    , testCase "Monad Reader 2" monadReader2
    , testCase "Monad Reader 3" monadReader3
    ]

  , testGroup "Various monads"
    [
      -- nats will generate an infinite number of results; demonstrate
      -- various ways of observing them via Logic/LogicT
      testCase "runIdentity all"  $ [0..4] @=? (take 5 $ runIdentity $ observeAllT nats)
    , testCase "runIdentity many" $ [0..4] @=? (runIdentity $ observeManyT 5 nats)
    , testCase "observeAll"       $ [0..4] @=? (take 5 $ observeAll nats)
    , testCase "observeMany"      $ [0..4] @=? (observeMany 5 nats)

    -- Ensure LogicT can be run over other base monads other than
    -- List.  Some are productive (Reader) and some are non-productive
    -- (ExceptT, ContT) in the observeAll case.

    , testCase "runReader is productive" $
      [0..4] @=? (take 5 $ runReader (observeAllT nats) "!")

    , testCase "observeManyT can be used with Either" $
      (Right [0..4] :: Either Char [Integer]) @=?
      (observeManyT 5 nats)
    ]

  --------------------------------------------------

  , testGroup "Control.Monad.Logic tests"
    [
      testCase "runLogicT multi" $ ["Hello world !"] @=?
      let conc w o = fmap ((w <> " ") <>) o in
      (runLogicT (yieldWords ["Hello", "world"]) conc (return "!"))

    , testCase "runLogicT none" $ ["!"] @=?
      let conc w o = fmap ((w <> " ") <>) o in
      (runLogicT (yieldWords []) conc (return "!"))

    , testCase "runLogicT first" $ ["Hello"] @=?
      (runLogicT (yieldWords ["Hello", "world"]) (\w -> const $ return w) (return "!"))

    , testCase "runLogic multi" $ 20 @=? runLogic odds5down (+) 11
    , testCase "runLogic none"  $ 11 @=? runLogic mzero (+) (11 :: Integer)

    , testCase "observe multi" $ 5 @=? observe odds5down
    , testCase "observe none" $ (Left "No answer." @=?) =<< safely (observe mzero)

    , testCase "observeAll multi" $ [5,3,1] @=? observeAll odds5down
    , testCase "observeAll none" $ ([] :: [Integer]) @=? observeAll mzero

    , testCase "observeMany multi" $ [5,3] @=? observeMany 2 odds5down
    , testCase "observeMany none" $ ([] :: [Integer]) @=? observeMany 2 mzero
    ]

  --------------------------------------------------

  , testGroup "Control.Monad.Logic.Class tests"
    [
      testGroup "msplit laws"
      [
        testGroup "msplit mzero == return Nothing"
        [
          testCase "msplit mzero :: []" $
          msplit mzero @=? return (Nothing :: Maybe (String, [String]))

        , testCase "msplit mzero :: ReaderT" $
          let z :: ReaderT Int [] String
              z = mzero
          in assertBool "ReaderT" $ null $ catMaybes $ runReaderT (msplit z) 0

        , testCase "msplit mzero :: LogicT" $
          let z :: LogicT [] String
              z = mzero
          in assertBool "LogicT" $ null $ catMaybes $ concat $ observeAllT (msplit z)
        , testCase "msplit mzero :: strict StateT" $
          let z :: SS.StateT Int [] String
              z = mzero
          in assertBool "strict StateT" $ null $ catMaybes $ SS.evalStateT (msplit z) 0
        , testCase "msplit mzero :: lazy StateT" $
          let z :: SL.StateT Int [] String
              z = mzero
          in assertBool "lazy StateT" $ null $ catMaybes $ SL.evalStateT (msplit z) 0
        ]

      , testGroup "msplit (return a `mplus` m) == return (Just a, m)" $
        let sample = [1::Integer,2,3] in
        [
          testCase "msplit []" $ do
            let op = sample
                extract = fmap (fmap fst)
            extract (msplit op) @?= [Just 1]
            extract (msplit op >>= (\(Just (_,nxt)) -> msplit nxt)) @?= [Just 2]

        , testCase "msplit ReaderT" $ do
            let op = ask
                extract = fmap fst . catMaybes . flip runReaderT sample
            extract (msplit op) @?= [sample]
            extract (msplit op >>= (\(Just (_,nxt)) -> msplit nxt)) @?= []

        , testCase "msplit LogicT" $ do
            let op :: LogicT [] Integer
                op = foldr (mplus . return) mzero sample
                extract = fmap fst . catMaybes . concat . observeAllT
            extract (msplit op) @?= [1]
            extract (msplit op >>= (\(Just (_,nxt)) -> msplit nxt)) @?= [2]

        , testCase "msplit strict StateT" $ do
            let op :: SS.StateT Integer [] Integer
                op = (SS.modify (+1) >> SS.get `mplus` op)
                extract = fmap fst . catMaybes . flip SS.evalStateT 0
            extract (msplit op) @?= [1]
            extract (msplit op >>= \(Just (_,nxt)) -> msplit nxt) @?= [2]

        , testCase "msplit lazy StateT" $ do
            let op :: SL.StateT Integer [] Integer
                op = (SL.modify (+1) >> SL.get `mplus` op)
                extract = fmap fst . catMaybes . flip SL.evalStateT 0
            extract (msplit op) @?= [1]
            extract (msplit op >>= \(Just (_,nxt)) -> msplit nxt) @?= [2]
        ]
      ]

    , testGroup "fair disjunction"
      [
        -- base case
        testCase "some odds"          $ [1,3,5,7] @=? observeMany 4 odds

        -- without fairness, the second producer is never considered
      , testCase "unfair disjunction" $ [1,3,5,7] @=? observeMany 4 oddsOrTwoUnfair

        -- with fairness, the results are interleaved

      , testCase "fair disjunction :: LogicT"   $ [1,2,3,5] @=? observeMany 4 oddsOrTwoFair

        -- without fairness nothing would be produced, but with
        -- fairness, a production is obtained

      , testCase "fair production"   $ [2] @=? observeT oddsOrTwo

        -- however, asking for additional productions will not
        -- terminate (there are none, since the first clause generates
        -- an infinity of mzero "failures")

#ifdef MIN_VERSION_tasty_expected_failure
      , expectFail $ testCase "nontermination even when fair" $
        [[2]] @=? observeManyT 2 oddsOrTwo
#endif

        -- Validate fair disjunction works for other
        -- Control.Monad.Logic.Class instances

      , testCase "fair disjunction :: []" $ [1,2,3,5] @=?
        (take 4 $ let oddsL = [ 1::Integer ] `mplus` [ o | o <- [3..], odd o ]
                      oddsOrTwoLFair = oddsL `interleave` [2]
                  in oddsOrTwoLFair)

      , testCase "fair disjunction :: ReaderT" $ [1,2,3,5] @=?
        (take 4 $ runReaderT (let oddsR = return 1 `mplus` liftM (2+) oddsR
                              in oddsR `interleave` return (2 :: Integer)) "go")

      , testCase "fair disjunction :: strict StateT" $ [1,2,3,5] @=?
        (take 4 $ SS.evalStateT (let oddsS = return 1 `mplus` liftM (2+) oddsS
                                  in oddsS `interleave` return (2 :: Integer)) "go")

      , testCase "fair disjunction :: lazy StateT" $ [1,2,3,5] @=?
        (take 4 $ SL.evalStateT (let oddsS = return 1 `mplus` liftM (2+) oddsS
                                  in oddsS `interleave` return (2 :: Integer)) "go")
      ]

    , testGroup "fair conjunction" $
      [
        -- Using the fair conjunction operator (>>-) the test produces values

        testCase "fair conjunction :: LogicT" $ [2,4,6,8] @=?
        observeMany 4 (let oddsPlus n = odds >>= \a -> return (a + n) in
                       do x <- (return 0 `mplus` return 1) >>- oddsPlus
                          if even x then return x else mzero
                      )

      , testCase "fair conjunction, rebindable syntax, monadic" $
        [2,4,6,8] @=? observeMany 4 oddsPlusRSBind

        -- unfair conjunction does not terminate or produce any
        -- values: this will fail (expectedly) due to a timeout

#ifdef MIN_VERSION_tasty_expected_failure
      , expectFail $ testCase "unfair conjunction" $ [2,4,6,8] @=?
        observeMany 4 (let oddsPlus n = odds >>= \a -> return (a + n) in
                       do x <- (return 0 `mplus` return 1) >>= oddsPlus
                          if even x then return x else mzero
                      )
#endif

      , testCase "fair conjunction :: []" $ [2,4,6,8] @=?
        (take 4 $ let oddsL = [ 1 :: Integer ] `mplus` [ o | o <- [3..], odd o ]
                      oddsPlus n = [ a + n | a <- oddsL ]
                  in do x <- [0] `mplus` [1] >>- oddsPlus
                        if even x then return x else mzero
        )

      , testCase "fair conjunction :: ReaderT" $ [2,4,6,8] @=?
        (take 4 $ runReaderT (let oddsR = return (1 :: Integer) `mplus` liftM (2+) oddsR
                                  oddsPlus n = oddsR >>= \a -> return (a + n)
                              in do x <- (return 0 `mplus` return 1) >>- oddsPlus
                                    if even x then return x else mzero
                             ) "env")

      , testCase "fair conjunction :: strict StateT" $ [2,4,6,8] @=?
        (take 4 $ SS.evalStateT (let oddsS = return (1 :: Integer) `mplus` liftM (2+) oddsS
                                     oddsPlus n = oddsS >>= \a -> return (a + n)
                                 in do x <- (return 0 `mplus` return 1) >>- oddsPlus
                                       if even x then return x else mzero
                                ) "state")

      , testCase "fair conjunction :: lazy StateT" $ [2,4,6,8] @=?
        (take 4 $ SL.evalStateT (let oddsS = return (1 :: Integer) `mplus` liftM (2+) oddsS
                                     oddsPlus n = oddsS >>= \a -> return (a + n)
                                 in do x <- (return 0 `mplus` return 1) >>- oddsPlus
                                       if even x then return x else mzero
                                ) "env")
      ]

    , testGroup "ifte logical conditional (soft-cut)"
    [
      -- Initial example returns all odds which are divisible by
      -- another number.  Nothing special is needed to implement this.

      let iota n = msum (map return [1..n])
          oc = do n <- odds
                  guard (n > 1)
                  d <- iota (n - 1)
                  guard (d > 1 && n `mod` d == 0)
                  return n
      in testCase "divisible odds" $ [9,15,15,21,21,25,27,27,33,33] @=?
         observeMany 10 oc

      -- To get the inverse: all odds which are *not* divisible by
      -- another number, the guard test cannot simply be reversed:
      -- there are many produced values that are not divisors, but
      -- some that are:

    , let iota n = msum (map return [1..n])
          oc = do n <- odds
                  guard (n > 1)
                  d <- iota (n - 1)
                  guard (d > 1 && n `mod` d /= 0)
                  return n
      in testCase "indivisible odds, wrong" $
         [3,5,5,5,7,7,7,7,7,9] @=?
         observeMany 10 oc

      -- For the inverse logic to work correctly, it should return
      -- values only when there are *no* divisors at all.  This can be
      -- done using the "soft cut" or "negation as finite failure" to
      -- needed to fail the current solution entirely.  This is
      -- provided by logict as the 'ifte' operator.

    , let iota n = msum (map return [1..n])
          oc = do n <- odds
                  guard (n > 1)
                  ifte (do d <- iota (n - 1)
                           guard (d > 1 && n `mod` d == 0))
                    (const mzero)
                    (return n)
      in testCase "indivisible odds :: LogicT" $ [3,5,7,11,13,17,19,23,29,31] @=?
         observeMany 10 oc

    , let iota n = [1..n]
          oddsL = [ 1 :: Integer ] `mplus` [ o | o <- [3..], odd o ]
          oc = [ n
               | n <- oddsL
               , (n > 1)
               ] >>= \n -> ifte (do d <- iota (n - 1)
                                    guard (d > 1 && n `mod` d == 0))
                           (const mzero)
                           (return n)
      in testCase "indivisible odds :: []" $ [3,5,7,11,13,17,19,23,29,31] @=?
         take 10 oc

    , let iota n = msum (map return [1..n])
          oddsR = return (1 :: Integer) `mplus` liftM (2+) oddsR
          oc = do n <- oddsR
                  guard (n > 1)
                  ifte (do d <- iota (n - 1)
                           guard (d > 1 && n `mod` d == 0))
                    (const mzero)
                    (return n)
      in testCase "indivisible odds :: ReaderT" $ [3,5,7,11,13,17,19,23,29,31] @=?
         (take 10 $ runReaderT oc "env")

    , let iota n = msum (map return [1..n])
          oddsS = return (1 :: Integer) `mplus` liftM (2+) oddsS
          oc = do n <- oddsS
                  guard (n > 1)
                  ifte (do d <- iota (n - 1)
                           guard (d > 1 && n `mod` d == 0))
                    (const mzero)
                    (return n)
      in testCase "indivisible odds :: strict StateT" $ [3,5,7,11,13,17,19,23,29,31] @=?
         (take 10 $ SS.evalStateT oc "state")

    , let iota n = msum (map return [1..n])
          oddsS = return (1 :: Integer) `mplus` liftM (2+) oddsS
          oc = do n <- oddsS
                  guard (n > 1)
                  ifte (do d <- iota (n - 1)
                           guard (d > 1 && n `mod` d == 0))
                    (const mzero)
                    (return n)
      in testCase "indivisible odds :: strict StateT" $ [3,5,7,11,13,17,19,23,29,31] @=?
         (take 10 $ SL.evalStateT oc "state")

    ]

    , testGroup "once (pruning)" $
      -- the pruning primitive 'once' selects (non-deterministically)
      -- a single candidate from many results and disables any further
      -- backtracking on this choice.

      let bogosort l = do p <- permute l
                          if sorted p then return p else mzero

          sorted (e:e':r) = e <= e' && sorted (e':r)
          sorted _        = True

          permute []      = return []
          permute (h:t)   = do { t' <- permute t; insert h t' }

          insert e []      = return [e]
          insert e l@(h:t) = return (e:l) `mplus`
                             do { t' <- insert e t; return (h : t') }

          inp = [5,0,3,4,0,1 :: Integer]
      in
        [
          -- without pruning, get two results because 0 appears twice
          testCase "no pruning" $ [[0,0,1,3,4,5], [0,0,1,3,4,5]] @=?
          observeAll (bogosort inp)

          -- with pruning, stops after the first result
        , testCase "with pruning" $ [[0,0,1,3,4,5]] @=?
          observeAll (once (bogosort inp))
        ]
    ]

  , testGroup "lnot (inversion)" $
    let isEven n = if even n then return n else mzero in
    [
      testCase "inversion :: LogicT" $ [1,3,5,7,9] @=?
      observeMany 5 (do v <- foldr (mplus . return) mzero [(1::Integer)..]
                        lnot (isEven v)
                        return v)

    , testCase "inversion :: []" $ [1,3,5,7,9] @=?
      (take 5 $ do v <- [(1::Integer)..]
                   lnot (isEven v)
                   return v)

    , testCase "inversion :: ReaderT" $ [1,3,5,7,9] @=?
      (take 5 $ runReaderT (do v <- foldr (mplus . return) mzero [(1::Integer)..]
                               lnot (isEven v)
                               return v) "env")

    , testCase "inversion :: strict StateT" $ [1,3,5,7,9] @=?
      (take 5 $ SS.evalStateT (do v <- foldr (mplus . return) mzero [(1::Integer)..]
                                  lnot (isEven v)
                                  return v) "state")

    , testCase "inversion :: lazy StateT" $ [1,3,5,7,9] @=?
      (take 5 $ SL.evalStateT (do v <- foldr (mplus . return) mzero [(1::Integer)..]
                                  lnot (isEven v)
                                  return v) "state")
    ]
  ]

safely :: IO Integer -> IO (Either String Integer)
safely o = fmap (left (head . lines . show)) (try o :: IO (Either SomeException Integer))
