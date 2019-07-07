{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Logic
import Control.Monad.Reader

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

main :: IO ()
main = defaultMain $ testGroup "All"
    [ testCase "Monad Reader 1" monadReader1
    , testCase "Monad Reader 2" monadReader2
    ]
