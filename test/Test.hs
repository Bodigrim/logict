{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Logic
import Control.Monad.Reader
import Data.Bifunctor ( first )
import Data.Either

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
    [ testCase "Monad Reader 1" monadReader1
    , testCase "Monad Reader 2" monadReader2
    , testCase "Monad Reader 3" monadReader3

    , testCase "runIdentity all"  $ [0..4] @=? (take 5 $ runIdentity $ observeAllT nats)
    , testCase "runIdentity many" $ [0..4] @=? (runIdentity $ observeManyT 5 nats)
    , testCase "observeAll"       $ [0..4] @=? (take 5 $ observeAll nats)
    , testCase "observeMany"      $ [0..4] @=? (observeMany 5 nats)

    , testCase "runReader" $ [0..4] @=? (take 5 $ runReader (observeAllT nats) "!")

    , testCase "manyT runExceptT" $ [0..4] @=?
      (fromRight [] $ runExcept (observeManyT 5 nats))

    , testCase "runLogicT multi" $ ["Hello world !"] @=?
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

safely :: IO Integer -> IO (Either String Integer)
safely o = first (head . lines . show) <$> (try o :: IO (Either SomeException Integer))
