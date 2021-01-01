{-# LANGUAGE FlexibleContexts #-}

module Main where

import           Test.Tasty
import           Test.Tasty.HUnit

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Logic
import           Control.Monad.Reader
import qualified Control.Monad.State.Lazy as SL
import qualified Control.Monad.State.Strict as SS
import           Data.Bifunctor ( first )
import           Data.Either
import           Data.Maybe

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

nats, odds5down :: Monad m => LogicT m Integer

nats = pure 0 `mplus` ((1 +) <$> nats)

odds5down = return 5 `mplus` mempty `mplus` mempty `mplus` return 3 `mplus` return 1

yieldWords :: [String] -> LogicT m String
yieldWords = go
  where go [] = mzero
        go (w:ws) = return w `mplus` go ws


main :: IO ()
main = defaultMain $ testGroup "All"
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
    -- (Except) in the observeAll case.

    , testCase "runReader" $ [0..4] @=? (take 5 $ runReader (observeAllT nats) "!")

    , testCase "manyT runExceptT" $ [0..4] @=?
      (fromRight [] $ runExcept (observeManyT 5 nats))
    ]

  --------------------------------------------------

  , testGroup "Control.Monad.Logic tests"
    [
      testCase "runLogicT multi" $ ["Hello world !"] @=?
      let conc w o = ((w <> " ") <>) <$> o in
      (runLogicT (yieldWords ["Hello", "world"]) conc (pure "!"))

    , testCase "runLogicT none" $ ["!"] @=?
      let conc w o = ((w <> " ") <>) <$> o in
      (runLogicT (yieldWords []) conc (pure "!"))

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

    ]
  ]

safely :: IO Integer -> IO (Either String Integer)
safely o = first (head . lines . show) <$> (try o :: IO (Either SomeException Integer))
