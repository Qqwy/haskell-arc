{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -ddump-rule-firings #-}

-- | Uniqueness-based mutable arrays which do not depend on fusion for efficiency.
--
-- Much of this module's internals was copied verbatinm from the mutable arrays in `linear-base`.
module Unique.Array
  ( -- | = Unique mutable arrays
    Array,
    -- | == Unique constructors
    fromList,
    alloc,
    -- | == Consuming arrays
    toList,
    consumingSum,
    -- sum,

    -- | == Properties
    size,
    assertIndexInRange,
    -- | == Modificiation
    get,
    unsafeGet,
    set,
    unsafeSet,
    Unique.Array.map,
    omap,
    eggsample,
    blogExample,
    -- = Unlifted unique mutable arrays
    -- Array#,
    -- unArray#,
    -- unsafeGet#
  )
where

import Control.Arrow (Arrow (arr))
import qualified Control.Functor.Linear as Linear
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
    arr123 -- Array [1,2,3]
      & Unique.Array.map (Prelude.Linear.+ 1) -- Array [2,3,4]
      & fromList [4, 5, 6] -- (Array [4,5,6], Array [2,3,4])
      & fromList [7, 8, 9] -- (Array [7,8,9], (Array [4,5,6], Array [2,3,4]))
      & \(arr789, (arr456, arr234)) -> (toList arr234, toList arr456, toList arr789)

blogExample :: [Int] -> (Int, [Int])
blogExample list =
  Unique.scoped (fromList list) $ \arr ->
    alloc 2 0 arr & \(prefix, arr) ->
      get 0 arr & \(Ur a0, arr) ->
        get 1 arr & \(Ur a1, arr) ->
          ( prefix
              & set 0 a0
              & set 1 a1
              & consumingSum,
            toList arr
          )

-- blogExample2 :: [Int] -> Int
-- blogExample2 list =
--   Unique.scoped (fromList list) $ \arr ->
--     case alloc 2 0 arr of
--       (prefix, arr) ->
--         case get 0 arr of
--           (Ur a0, arr) ->
--             case get 1 arr of
--               (Ur a1, arr) ->
--                 arr `lseq` consumingSum (prefix & set 0 a0 & set 1 a1)

-- more computation involving arr3
-- arr
-- & alloc 2 0
-- & \(prefix, arr') ->
--     let (Ur a0, arr'') = get 0 arr' in
--     let (Ur a1, arr''') = get 1 arr'' in
--     let sum = prefix & set 0 a0 & set 1 a1 & consumingSum in
--         arr''' `lseq` sum

-- & dup2
-- & (\(x, y) -> (Unique.Array.toList x, Unique.Array.toList y))

-- A lifted mutable array holding @a@s.
data Array a = Array (Array# a)

-- | An unlifted mutable array holding @a@s.
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

-- | [Unique constructor]("Unique#unique_constructor") to create an `Array` from a list.
fromList :: Unique witness => [a] %1 -> witness %1 -> (Array a, witness)
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

-- | [Unique constructor]("Unique#unique_constructor") to create an `Array` with all elements initialized with the same value.
alloc :: Unique witness => Int -> a -> witness %1 -> (Array a, witness)
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
get :: (HasCallStack, Dupable a) => Int -> Array a %1 -> (a, Array a)
get i arr = unsafeGet i (assertIndexInRange i arr)

-- | Same as 'get', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeGet :: Dupable a => Int -> Array a %1 -> (a, Array a)
unsafeGet ix (Array arr) = wrap (unsafeGet# ix arr)
  where
    wrap :: (# a, Array# a #) %1 -> (a, Array a)
    wrap (# ret, arr #) = (ret, Array arr)

unsafeGet# :: Dupable a => Int -> Array# a %1 -> (# a, Array# a #)
unsafeGet# (GHC.I# i) = Unsafe.toLinear go
  where
    go :: Array# a -> (# a, Array# a #)
    go (Array# arr) =
      case GHC.runRW# (GHC.readArray# arr i) of
        (# _, ret #) -> dup ret & \(_, copy) -> (# copy, Array# arr #)
{-# NOINLINE unsafeGet# #-} -- prevents the runRW# effect from being reordered

-- | Overwrites the array's element at the given index with the new value.
--
-- Restricted to element types which are 'Consumable' because the old
-- value is consumed in the process.
set :: (Consumable a, HasCallStack) => Int -> a %1 -> Array a %1 -> Array a
set ix val arr = unsafeSet ix val (assertIndexInRange ix arr)

-- | Same as 'set', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: Consumable a => Int %1 -> a %1 -> Array a %1 -> Array a
unsafeSet ix val (Array arr) =
  Array (unsafeSet# ix val arr)

unsafeSet# :: Consumable a => Int %1 -> a %1 -> Array# a %1 -> Array# a
unsafeSet# = Unsafe.toLinear3 go
  where
    go :: Int -> a -> Array# a -> Array# a
    go (GHC.I# i) (a :: a) (Array# arr) =
        GHC.runRW# $ \st ->
            case (GHC.readArray# arr i) st of
                (# _, val #) ->
                    case (GHC.writeArray# arr i a) st of
                        _ -> 
                            (consume val) 
                            & (\() -> Array# arr)
{-# NOINLINE unsafeSet# #-} -- prevents the runRW# effect from being reordered

instance Consumable (Array a) where
  consume (Array arr) = arr `lseq#` ()

-- | Duplicating an array requires a deep copy.
instance Dupable (Array a) where
  dup2 (Array arr) = wrap (dup2# arr)
    where
      wrap :: (# Array# a, Array# a #) %1 -> (Array a, Array a)
      wrap (# a1, a2 #) = (Array a1, Array a2)

-- | Unique mutable arrays that do not depend on fusion.
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

-- | Map a linear function over an array.
--
-- Because the input and output array type is the same, the array can be modified in place.
-- No extra array has to be allocated.
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

-- | Map a linear function over an array.
--
-- An extra array needs to be allocated to store the result.
--
-- A rewrite rule exists to turn `map` into `omap` whenever possible to avoid this allocation.
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

consumingSum :: AddIdentity a => Array a %1 -> a
consumingSum arr =
  size arr & \(Ur s, arr') ->
    go zero s arr'
  where
    go :: AddIdentity a => a %1 -> Int -> Array a %1 -> a
    go acc 0 arr = arr `lseq` acc
    go acc i arr =
      get (i - 1) arr & \(a, arr') ->
        go (acc + a) (i - 1) arr'
