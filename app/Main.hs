{-# OPTIONS_GHC -O2 -fspecialise-aggressively -ddump-stg-final #-}
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import DeepCopy

main :: IO ()
main = foo (Just (Right 52))

foo :: Maybe (Either String Int) -> IO ()
-- foo :: Integer -> IO ()
foo x =  do
    -- let x = Just (Right 1) :: Maybe (Either String Int)
    let (!x', !y) = deepCopy x
    print x'
    print y
{-# NOINLINE foo #-}


bar :: Maybe (Either String Int) -> IO ()
bar x = do
    let (x', y) = baz x
    print x'
    print y

{-# NOINLINE bar #-}

baz :: x -> (x, x)
baz x = (x, x)
{-# NOINLINE baz #-}