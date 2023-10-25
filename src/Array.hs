{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant case" #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Array where

import Prelude.Linear
import qualified Prelude
-- import qualified Data.Array.Mutable.Linear
-- import Data.Array.Mutable.Unlifted.Linear (Array#(..), unArray#)
-- import qualified Data.Array.Mutable.Unlifted.Linear
import qualified GHC.Exts as GHC
import qualified Unsafe.Linear as Unsafe

import Linearly
import Data.Array.Mutable.Linear (fromList)

-- >>> let list = ([1,2,3] :: [Int]) in linearly (\() -> list & Array.fromList' & Array.arrOMap (+40) & Array.toList')
-- [41,42,43]
example =
    alloc (10 :: Int, 42 :: Int) $ \(arr :: Array Int) ->
        allocBeside ([1, 2, 3] :: [Int]) arr
        & (\(arr2 :: Array Int, arr1) ->  (toList arr1, toList arr2))

example2 :: ([Int], [Int])
-- example2 :: [Int]
example2 =
  linearly' (\(tok1, tok2) ->
    [1, 2, 3]
    & fromList' tok1
    & arrOMap (+ 40)
    -- & toList'
    & (\arr1 -> 
      buildSecond tok2
      & (\arr2 -> (toList' arr1, toList' arr2))
      -- let arr2 = fromList' tok2 in (toList' arr1, toList arr2)
      )
    -- & toList'
    -- & (\x -> (toList' x, toList' x))
  )

buildSecond :: Linearly %1 -> Array Int
buildSecond tok = 
  [4, 5, 6]
  & fromList' (splitToken tok)

class LinearOnly a where
    linId :: a %1 -> a

class LinearOnly a => Allocable a opts where
    -- | Bulds an `a` from the given options.
    --
    -- Safety: This function allows you to obtain an `a` outside of a linear context,
    -- which might be problematic for many instances.
    unsafeAlloc :: opts -> a

class Immutable a where

instance Movable a => Immutable a where

alloc :: (Immutable b, Allocable a opts) => opts -> (a %1 -> b) %1 -> b
alloc opts f = f (unsafeAlloc opts)

allocBeside :: (LinearOnly a, Allocable b bOpts) => bOpts -> a %1 -> (b, a)
allocBeside opts a = (unsafeAlloc opts, linId a)

instance LinearOnly (Array a) where
    linId = id

instance Allocable (Array a) (Int, a) where
    unsafeAlloc (size, elem) = Array (unsafeArrAlloc size elem)

instance Allocable (Array a) [a] where
    unsafeAlloc :: [a] -> Array a
    unsafeAlloc list =
        unsafeAlloc (Prelude.length list, error "invariant violation: unintialized array position" :: a)
        & doWrites (Prelude.zip list [0..])
            where
                doWrites :: [(a, Int)] -> Array a %1 -> Array a
                doWrites [] arr = arr
                doWrites ((a, ix) : xs) arr = doWrites xs (unsafeSet ix a arr)

unsafeArrAlloc :: Int -> a -> Array# a
unsafeArrAlloc (GHC.I# s) a = GHC.runRW# Prelude.$ \st ->
    case GHC.newArray# s a st of
        (# _, arr #) -> Array# arr
{-# NOINLINE unsafeArrAlloc #-}

data Array a = Array (Array# a)

-- | A mutable array holding @a@s
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

-- | Extract the underlying 'GHC.MutableArray#', consuming the 'Array#'
-- in process.
unArray# :: (GHC.MutableArray# GHC.RealWorld a -> b) -> Array# a %1 -> b
unArray# f = Unsafe.toLinear (\(Array# a) -> f a)

size :: Array a %1 -> (Ur Int, Array a)
size (Array arr) = f (size# arr)
  where
    f :: (# Ur Int, Array# a #) %1 -> (Ur Int, Array a)
    f (# s, arr #) = (s, Array arr)

size# :: Array# a %1 -> (# Ur Int, Array# a #)
size# = Unsafe.toLinear go
  where
    go :: Array# a -> (# Ur Int, Array# a #)
    go (Array# arr) =
      let !s = GHC.sizeofMutableArray# arr
       in (# Ur (GHC.I# s), Array# arr #)


-- | Same as 'set', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: Int -> a -> Array a %1 -> Array a
unsafeSet ix val (Array arr) =
  Array (unsafeSet# ix val arr)

unsafeSet# :: Int -> a -> Array# a %1 -> Array# a
unsafeSet# (GHC.I# i) (a :: a) = Unsafe.toLinear go
  where
    go :: Array# a -> Array# a
    go (Array# arr) =
      case GHC.runRW# (GHC.writeArray# arr i a) of
        _ -> Array# arr
{-# NOINLINE unsafeSet# #-} -- prevents the runRW# effect from being reordered


-- | Get the value of an index. The index should be less than the arrays 'size',
-- otherwise this errors.
get :: Int -> Array a %1 -> (Ur a, Array a)
get i arr = unsafeGet i (assertIndexInRange i arr)

-- | Same as 'get', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeGet :: Int -> Array a %1 -> (Ur a, Array a)
unsafeGet ix (Array arr) = wrap (unsafeGet# ix arr)
  where
    wrap :: (# Ur a, Array# a #) %1 -> (Ur a, Array a)
    wrap (# ret, arr #) = (ret, Array arr)

-- NOTE: is Ur usage correct here?
unsafeGet# :: Int -> Array# a %1 -> (# Ur a, Array# a #)
unsafeGet# (GHC.I# i) = Unsafe.toLinear go
  where
    go :: Array# a -> (# Ur a, Array# a #)
    go (Array# arr) =
      case GHC.runRW# (GHC.readArray# arr i) of
        (# _, ret #) -> (# Ur ret, Array# arr #)
{-# NOINLINE unsafeGet# #-} -- prevents the runRW# effect from being reordered


-- | Return the array elements as a lazy list.
toList :: Array a %1 -> [a]
toList (Array arr) = toList# arr

toList' :: Movable a => Array a %1 -> [a]
toList' (Array arr) = toList# arr

arrOMap :: forall a. (a %1 -> a) -> Array a %1 -> Array a
arrOMap f arr =
  size arr
  & uncurry (go (Ur 0))
  where
    update :: Int -> Array a %1 -> Array a
    update idx arr = 
      unsafeGet idx arr
      & (\(Ur elem, arr) -> unsafeSet idx (f elem) arr)

    go :: Ur Int %1 -> Ur Int %1 -> Array a %1 -> Array a
    go (Ur idx) (Ur size) arr' =
      if idx == size
        then arr'
        else 
          arr'
          & update idx
          & go (Ur (idx + 1)) (Ur size)

-- | Return the array elements as a lazy list.
toList# :: Array# a %1 -> [a]
toList# = unArray# Prelude.$ \arr ->
  go
    0
    (GHC.I# (GHC.sizeofMutableArray# arr))
    arr
  where
    go i len arr
      | i Prelude.== len = []
      | GHC.I# i# <- i =
          case GHC.runRW# (GHC.readArray# arr i#) of
            (# _, ret #) -> ret : go (i Prelude.+ 1) len arr
{-# NOINLINE toList# #-}

newMArray :: (?lin :: Linearly) => Int -> a -> Array a
-- newMArray :: Int -> a -> Array a
newMArray size elem = Array (unsafeArrAlloc size elem)
{-# NOINLINE newMArray #-}

fromList' :: Linearly %1 -> [a] %1 -> Array a
-- fromList' :: [a] -> Array a
fromList' = Unsafe.toLinear2 $ \lin list -> 
        let ?lin = lin in newMArray (Prelude.length list) (error "invariant violation: unintialized array position" :: a)
        & doWrites (Prelude.zip list [0..])
            where
                doWrites :: [(a, Int)] -> Array a %1 -> Array a
                doWrites [] arr = arr
                doWrites ((a, ix) : xs) arr = doWrites xs (unsafeSet ix a arr)
{-# NOINLINE fromList' #-}


-- | Check if given index is within the Array, otherwise panic.
assertIndexInRange :: Int -> Array a %1 -> Array a
assertIndexInRange i arr =
  size arr & \(Ur s, arr') ->
    if 0 <= i && i < s
      then arr'
      else arr' `lseq` error "Array: index out of bounds"


instance Consumable (Array a) where
  consume :: Array a %1 -> ()
  consume (Array arr) = arr `lseq#` ()

-- | Consume an 'Array#'.
--
-- Note that we can not implement a 'Consumable' instance because 'Array#'
-- is unlifted.
lseq# :: Array# a %1 -> b %1 -> b
lseq# = Unsafe.toLinear2 (\_ b -> b)
