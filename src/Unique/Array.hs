{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Uniqueness-based mutable arrays which do not depend on fusion for efficiency.
--
-- Much of this module's internals was copied verbatinm from the mutable arrays in `linear-base`.
module Unique.Array where

import qualified Data.List.Linear
import Data.Vector.Internal.Check (HasCallStack)
import qualified GHC.Exts as GHC
import Prelude.Linear
import Unique (Unique)
import qualified Unique
import qualified Unsafe.Linear as Unsafe
import qualified Prelude

eggsample :: ([Int], [Int], [Int])
eggsample =
  Unique.scoped (fromList [1, 2, 3]) $ \arr123 ->
    arr123 -- arr123
      & Unique.Array.map (Prelude.Linear.+ 1) -- arr234
      & fromList [4, 5, 6] -- (arr456, arr234)
      & fromList [7, 8, 9] -- (arr789, (arr456, arr234))
      & \(arr789, (arr456, arr234)) -> (toList arr234, toList arr456, toList arr789)

-- & dup2
-- & (\(x, y) -> (Unique.Array.toList x, Unique.Array.toList y))

-- A lifted mutable array holding @a@s.
data Array a = Array (Array# a)

-- | An unlifted mutable array holding @a@s.
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

fromList :: Unique b => [a] %1 -> b %1 -> (Array a, b)
fromList list b =
  list
    & Data.List.Linear.length
    & ( \(Ur size, list') ->
          alloc size (error "invariant violation: unintialized array position" :: a) b
            & (\(arr, b) -> (doWrites (listWithIndexes list') arr, b))
      )
  where
    -- NOTE: Would be nice if this function would be made part of Data.List.Linear.
    listWithIndexes :: [a] %1 -> [(a, Int)]
    listWithIndexes = Unsafe.toLinear (\list -> Prelude.zip list [0 ..])
    doWrites :: [(a, Int)] %1 -> Array a %1 -> Array a
    doWrites [] arr = arr
    doWrites ((a, ix) : xs) arr = doWrites xs (unsafeSet ix a arr)

alloc :: Unique b => Int -> a -> b %1 -> (Array a, b)
alloc size elem b = (Array (unsafeArrAlloc size elem), b)
  where
    unsafeArrAlloc (GHC.I# s) a = GHC.runRW# Prelude.$ \st ->
      case GHC.newArray# s a st of
        (# _, arr #) -> Array# arr
    {-# NOINLINE unsafeArrAlloc #-}

-- | Return the array's elements as a lazy list.
toList :: Array a %1 -> [a]
toList (Array arr) = toList# arr

-- | Return the array's elements as a lazy list.
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

-- | Extract the underlying 'GHC.MutableArray#', consuming the 'Array#'
-- in process.
--
-- An extremely low-level function.
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

-- | Get the value of an index. The index should be less than the arrays 'size',
-- otherwise this errors.
get :: HasCallStack => Int -> Array a %1 -> (Ur a, Array a)
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

set :: HasCallStack => Int -> a -> Array a %1 -> Array a
set ix val arr = unsafeSet ix val (assertIndexInRange ix arr)

-- | Same as 'set', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: Int %1 -> a %1 -> Array a %1 -> Array a
unsafeSet ix val (Array arr) =
  Array (unsafeSet# ix val arr)

unsafeSet# :: Int %1 -> a %1 -> Array# a %1 -> Array# a
unsafeSet# = Unsafe.toLinear3 go
  where
    go :: Int -> a -> Array# a -> Array# a
    go (GHC.I# i) (a :: a) (Array# arr) =
      case GHC.runRW# (GHC.writeArray# arr i a) of
        _ -> Array# arr
{-# NOINLINE unsafeSet# #-} -- prevents the runRW# effect from being reordered

instance Consumable (Array a) where
  consume (Array arr) = arr `lseq#` ()

instance Dupable (Array a) where
  dup2 (Array arr) = wrap (dup2# arr)
    where
      wrap :: (# Array# a, Array# a #) %1 -> (Array a, Array a)
      wrap (# a1, a2 #) = (Array a1, Array a2)

instance Unique (Array a)

-- | Consume an 'Array#'.
--
-- Note that we can not implement a 'Consumable' instance because 'Array#'
-- is unlifted.
lseq# :: Array# a %1 -> b %1 -> b
lseq# = Unsafe.toLinear2 (\_ b -> b)

-- | Clone an Array#.
--
-- Note that we can not implement a 'Dupable' instance because 'Array#'
-- is unlifted.
dup2# :: Array# a %1 -> (# Array# a, Array# a #)
dup2# = Unsafe.toLinear go
  where
    go :: Array# a -> (# Array# a, Array# a #)
    go (Array# arr) =
      case GHC.runRW#
        (GHC.cloneMutableArray# arr 0# (GHC.sizeofMutableArray# arr)) of
        (# _, new #) -> (# Array# arr, Array# new #)
{-# NOINLINE dup2# #-}

-- | Check if given index is within the Array, otherwise panic.
assertIndexInRange :: Int -> Array a %1 -> Array a
assertIndexInRange i arr =
  size arr & \(Ur s, arr') ->
    if 0 <= i && i < s
      then arr'
      else arr' `lseq` error "Array: index out of bounds"

omap :: (a %1 -> a) -> Array a %1 -> Array a
omap (f :: a %1 -> a) (Array arr) = Array (omap# f arr)

omap# :: (a %1 -> a) -> Array# a %1 -> Array# a
omap# (f :: a %1 -> a) = Unsafe.toLinear $ \(Array# as) ->
  let len :: GHC.Int#
      len = GHC.sizeofMutableArray# as
      go i st
        | GHC.I# i Prelude.== GHC.I# len = ()
        | Prelude.otherwise =
            case GHC.readArray# as i st of
              (# st', a #) ->
                case GHC.writeArray# as i (f a) st' of
                  !st'' -> go (i GHC.+# 1#) st''
   in GHC.runRW# (go 0#) `GHC.seq` Array# as
{-# NOINLINE omap# #-}

map :: (a %1 -> b) -> Array a %1 -> Array b
map f (Array arr) = Array (map# f arr)

map# :: (a %1 -> b) -> Array# a %1 -> Array# b
map# (f :: a %1 -> b) =
  Unsafe.toLinear
    ( \(Array# as) ->
        let -- We alias the input array to write the resulting -- 'b's to,
            -- just to make the typechecker happy. Care must be taken to
            -- only read indices from 'as' that is not yet written to 'bs'.
            bs :: GHC.MutableArray# GHC.RealWorld b
            bs = GHC.unsafeCoerce# as
            len :: GHC.Int#
            len = GHC.sizeofMutableArray# as

            -- For each index ([0..len]), we read the element on 'as', pass
            -- it through 'f' and write to the same location on 'bs'.
            go :: GHC.Int# -> GHC.State# GHC.RealWorld -> ()
            go i st
              | GHC.I# i Prelude.== GHC.I# len = ()
              | Prelude.otherwise =
                  case GHC.readArray# as i st of
                    (# st', a #) ->
                      case GHC.writeArray# bs i (f a) st' of
                        !st'' -> go (i GHC.+# 1#) st''
         in GHC.runRW# (go 0#) `GHC.seq` Array# bs
    )
{-# NOINLINE map# #-}

-- Only fires when map# is called with a function `a -> a` (otherwise it does not typecheck)
{-# RULES "map#/omap#" forall f. Unique.Array.map# f = Unique.Array.omap# f #-}
