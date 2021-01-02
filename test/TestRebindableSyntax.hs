{-# LANGUAGE RebindableSyntax #-}

module TestRebindableSyntax where

import Control.Monad.Logic

import Prelude


oddsAppl :: LogicT m Integer
oddsAppl = return 1 `mplus` liftM (2+) oddsAppl

oddsPlus' :: Integer -> LogicT m Integer
oddsPlus' n = oddsAppl >>= \a -> return (a + n)

oddsPlusRSBind :: Monad m => LogicT m Integer
oddsPlusRSBind =
  do
     -- Desugaring of do should combine these with >>-
     a <- (return 0 `mplus` return 1)
     x <- oddsPlus' a

     -- This is the explicit form
     -- x <- (return 0 `interleave` return 1) >>- oddsPlus'

     if even x then return x else mzero
  where (>>=) = (>>-)


-- Because rebindable syntax was used, this must be explicitly provided:
ifThenElse :: Bool -> a -> a -> a
ifThenElse c t e = case c of { True -> t; False -> e }
