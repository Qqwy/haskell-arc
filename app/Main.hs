{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -ddump-stg-final #-}
module Main (main) where

import qualified Prelude
import Prelude.Linear
-- import Lib
-- import DeepCopy
import qualified Unique
import Unique.Array

main :: IO ()
main = do
  let mylist = [1..10]
  print $ Main.blogExample mylist
  -- print $ Main.eggsample

-- main :: IO ()
-- main = foo (Just (Right 52))

-- foo :: Maybe (Either String Int) -> IO ()
-- -- foo :: Integer -> IO ()
-- foo x =  do
--     -- let x = Just (Right 1) :: Maybe (Either String Int)
--     let (!x', !y) = deepCopy x
--     print x'
--     print y
-- {-# NOINLINE foo #-}


-- bar :: Maybe (Either String Int) -> IO ()
-- bar x = do
--     let (x', y) = baz x
--     print x'
--     print y

-- {-# NOINLINE bar #-}

-- baz :: x -> (x, x)
-- baz x = (x, x)
-- {-# NOINLINE baz #-}


blogExample :: [Int] -> (Int, [Int])
blogExample list =
  Unique.scoped (fromList list) $ \arr ->
    alloc 2 0 arr & \(prefix, arr) ->
      unsafeGet 0 arr & \(a0, arr) ->
        unsafeGet 1 arr & \(a1, arr) ->
          ( prefix
              & unsafeSet 0 a0
              & unsafeSet 1 a1
              & consumingSum,
            toList arr
          )

-- {-# NOINLINE blogExample #-}

eggsample :: ([Int], [Int], [Int])
eggsample =
  Unique.scoped (fromList [1, 2, 3]) $ \arr123 ->
    arr123 -- Array [1,2,3]
      & Unique.Array.map (Prelude.Linear.+ 1) -- Array [2,3,4]
      & fromList [4, 5, 6] -- (Array [4,5,6], Array [2,3,4])
      & fromList [7, 8, 9] -- (Array [7,8,9], (Array [4,5,6], Array [2,3,4]))
      & \(arr789, (arr456, arr234)) -> (toList arr234, toList arr456, toList arr789)
