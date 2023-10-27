{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE LambdaCase #-}

-- {-# OPTIONS_GHC -ddump-stg #-}

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
    getMaybe,
    unsafeGet,
    set,
    setMaybe,
    unsafeSet,
    swap,
    unsafeSwap,
    Unique.Array.map,
    swapMaybe,
    -- eggsample,
    -- blogExample,
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

{-# RULES
"dup int" forall (x :: Int). dup x = (x, x)
  #-}

{-# RULES
"dup2 int" forall (x :: Int). dup2 x = (x, x)
  #-}

{-# RULES
"consume int" forall (x :: Int). consume x = ()
  #-}

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
      unsafeGet 0 arr & \(a0, arr) ->
        unsafeGet 1 arr & \(a1, arr) ->
          ( prefix
              & unsafeSet 0 a0
              & unsafeSet 1 a1
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
--
-- >>> Unique.scoped (fromList ([1.0, 2.0 ,3.0])) (\arr -> arr & Unique.Array.map (+1) & Unique.Array.toList)
-- [2.0,3.0,4.0]
--
-- >>> :t \list -> Unique.scoped (fromList list)
-- \list -> Unique.scoped (fromList list) :: Movable r => [a] -> (Array a %1 -> r) %1 -> r
--
-- >>> :t \list -> Unique.consuming (Unique.Array.fromList list)
-- \list -> Unique.consuming (Unique.Array.fromList list)
--   :: (Unique witness, Consumable witness) =>
--      [a] -> witness %1 -> Array a
fromList :: (Unique witness) => [a] %1 -> witness %1 -> (Array a, witness)
fromList = Unsafe.toLinear2 $ \list witness ->
  alloc (Prelude.length list) (error "invariant violation: unintialized array position" :: a) witness
    & (\(arr, witness) -> (doWrites (listWithIndexes list) arr, witness))
  where
    -- NOTE: Would be nice if this function would be made part of Data.List.Linear.
    listWithIndexes :: [a] %1 -> [(a, Int)]
    listWithIndexes = Unsafe.toLinear (\list -> Prelude.zip list [0 ..])
    doWrites :: [(a, Int)] %1 -> Array a %1 -> Array a
    doWrites [] arr = arr
    doWrites ((a, ix) : xs) arr = doWrites xs (writeEmpty ix arr a)
    writeEmpty :: Int %1 -> Array a %1 -> a %1 -> Array a
    writeEmpty ix arr a =
      arr
        -- SAFETY: Array has same size as input list
        & unsafeSwap ix a
        -- SAFETY: The forgotten element is a bottom:
        & uncurry unsafeForgettingLseq
{-# INLINE fromList #-}

-- | [Unique constructor]("Unique#unique_constructor") to create an `Array` with all elements initialized with the same value.
--
-- >>> Unique.scoped (alloc 3 "hello") (\arr -> arr & Unique.Array.toList)
-- ["hello","hello","hello"]
--
--
-- >>> :t \size elem -> Unique.scoped (Unique.Array.alloc size elem)
-- \size elem -> Unique.scoped (Unique.Array.alloc size elem) :: Movable r => Int -> a -> (Array a %1 -> r) %1 -> r
--
-- >>> :t \size elem -> Unique.consuming (Unique.Array.alloc size elem)
-- \size elem -> Unique.consuming (Unique.Array.alloc size elem)
--   :: (Unique witness, Consumable witness) =>
--      Int -> a -> witness %1 -> Array a
alloc :: (Unique witness) => Int %1 -> a -> witness %1 -> (Array a, witness)
alloc (GHC.I# size) elem b = (Array (Unsafe.toLinear unsafeArrAlloc size elem), b)
  where
    unsafeArrAlloc :: GHC.Int# -> a -> Array# a
    unsafeArrAlloc s a = GHC.runRW# Prelude.$ \st ->
      case GHC.newArray# s a st of
        (# _, arr #) -> Array# arr
    {-# NOINLINE unsafeArrAlloc #-}
{-# INLINE alloc #-}

-- | Return the array's elements as a lazy list.
toList :: Array a %1 -> [a]
toList (Array arr) = toList# arr
{-# INLINE toList #-}

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

size :: Array a %1 -> (Int, Array a)
size (Array arr) = f (size# arr)
  where
    f :: (# Int, Array# a #) %1 -> (Int, Array a)
    f (# s, arr #) = (s, Array arr)
{-# INLINE size #-}

size# :: Array# a %1 -> (# Int, Array# a #)
size# = Unsafe.toLinear go
  where
    go :: Array# a -> (# Int, Array# a #)
    go (Array# arr) =
      let !s = GHC.sizeofMutableArray# arr
       in (# GHC.I# s, Array# arr #)
{-# INLINE size# #-}

-- | Swaps the value at the given index with the newly given value.
-- The value previously stored at the index is returned.
--
-- This function will panic if the index is out of array bounds. (At that time, the array is consumed which is why the `Consumable` bound exists)
--
-- See `swapMaybe` and `unsafeSwap` for alternatives without this bound.
--
---- >>> Unique.scoped (fromList [1 :: Int,2,3]) (\arr -> arr & swap 1 100 & \(elem, arr) -> (elem, toList arr))
-- (2,[1,100,3])
-- >>> Unique.scoped (fromList [1 :: Int,2,3]) (\arr -> arr & swap 1000 100 & \(elem, arr) -> (elem, toList arr))
-- Array: index out of bounds
swap :: (HasCallStack, Consumable a) => Int %1 -> a %1 -> Array a %1 -> (a, Array a)
swap i val arr = dup2 i & \(i, i2) -> unsafeSwap i val (assertIndexInRange i2 arr)
{-# INLINE swap #-}

-- | Safe version of `swap`, returning @(Nothing, unchanged array)@ if the index was out of bounds.
-- >>> Unique.scoped (fromList [1 :: Int,2,3]) (\arr -> arr & swapMaybe 1 100 & \(elem, arr) -> (elem, toList arr))
-- (Just 2,[1,100,3])
--
-- >>> Unique.scoped (fromList [1 :: Int,2,3]) (\arr -> arr & swapMaybe 1000 100 & \(elem, arr) -> (elem, toList arr))
-- (Nothing,[1,2,3])
swapMaybe :: Int %1 -> a %1 -> Array a %1 -> (Maybe a, Array a)
swapMaybe = Unsafe.toLinear3 $ \ix elem arr ->
  indexInRange ix arr & \(bool, arr) ->
    if bool then unsafeSwap ix elem arr & \(a, arr) -> (Just a, arr)
    else (Nothing, arr)

-- | Version of `swap` which does not do bounds checking.
-- (As such, no `Consumable` bound on @a@ is necessary)
unsafeSwap :: Int %1 -> a %1 -> Array a %1 -> (a, Array a)
unsafeSwap ix val (Array arr) =
  wrap (unsafeSwap# ix val arr)
  where
    wrap :: (# a, Array# a #) %1 -> (a, Array a)
    wrap (# ret, arr #) = (ret, Array arr)
{-# INLINE unsafeSwap #-}

-- NOTE: We pretend we use the index linearly
-- But actually we don't. This is fine, because we _evaluate_ it exactly once,
-- after which (because we have an unlifted Int#) there is no risk of linear stuff hiding.
-- What we do here is a shorthand for calling `move` on the index.
unsafeSwap# :: Int %1 -> a %1 -> Array# a %1 -> (# a, Array# a #)
unsafeSwap# = Unsafe.toLinear3 $ \(GHC.I# i) elem (Array# arr) ->
  GHC.runRW# $ \st ->
    case GHC.readArray# arr i st of
      (# st, val #) ->
        case GHC.writeArray# arr i elem st of
          _st ->
            (# val, Array# arr #)
{-# NOINLINE unsafeSwap# #-}

-- | Get the value of an index. The index should be less than the arrays 'size',
-- otherwise this errors.
--
-- The value is copied out of the array using `dup`.
get :: (HasCallStack, Dupable a) => Int %1 -> Array a %1 -> (a, Array a)
get i arr = dup i & \(i, i2) -> unsafeGet i (assertIndexInRange i2 arr)
{-# INLINE get #-}

getMaybe :: (Dupable a) => Int %1 -> Array a %1 -> (Maybe a, Array a)
getMaybe = 
  -- NOTE: Unsafe.toLinear should not be necessary here,
  -- but for some reason GHC chokes on the linearity proof here when using `dup ix`.
  Unsafe.toLinear $ \ix arr ->
  case indexInRange ix arr of
    (True, arr) -> unsafeGet ix arr & \(a, arr) -> (Just a, arr)
    (False, arr) -> (Nothing, arr)

{-# INLINE getMaybe #-}

-- | Same as 'get', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeGet :: (Dupable a) => Int %1 -> Array a %1 -> (a, Array a)
unsafeGet ix (Array arr) = wrap (unsafeGet# ix arr)
  where
    wrap :: (# a, Array# a #) %1 -> (a, Array a)
    wrap (# ret, arr #) = (ret, Array arr)
{-# INLINE unsafeGet #-}

unsafeGet# :: (Dupable a) => Int %1 -> Array# a %1 -> (# a, Array# a #)
unsafeGet# (GHC.I# ix) arr =
  Unsafe.toLinear fixup (Unsafe.toLinear2 unsafeGet'# ix arr)
  where
    unsafeGet'# :: (Dupable a) => GHC.Int# -> Array# a -> (# a, Array# a #)
    unsafeGet'# i (Array# arr) =
      case GHC.runRW# (GHC.readArray# arr i) of
        (# _, ret #) ->
          -- dup ret & \(_, copy) -> (# copy, Array# arr #)
          (# ret, Array# arr #) -- <- NOTE: Potentially unsafe?
    {-# NOINLINE unsafeGet'# #-} -- prevents the runRW# effect from being reordered
    fixup :: (Dupable a) => (# a, Array# a #) -> (# a, Array# a #)
    fixup (# a, arr #) = dup a & \(_, copy) -> (# copy, arr #)
    {-# INLINE fixup #-}
{-# INLINE unsafeGet# #-}

-- {-# SPECIALISE unsafeGet# :: Int %1 -> Array# Int %1 -> (# Int, Array# Int #) #-}

-- | Overwrites the array's element at the given index with the new value.
--
-- Restricted to element types which are 'Consumable' because the value
-- previously stored at the index is consumed in the process.
set :: (Consumable a, HasCallStack) => Int %1 -> a %1 -> Array a %1 -> Array a
set ix val arr = dup ix & (\(ix, ix2) -> unsafeSet ix val (assertIndexInRange ix2 arr))
{-# INLINE set #-}

setMaybe :: (Consumable a) => Int %1 -> a %1 -> Array a %1 -> Array a
setMaybe = 
  -- -- NOTE: Unsafe.toLinear should not be necessary here,
  -- -- but for some reason GHC chokes on the linearity proof here when using `dup ix`.
  Unsafe.toLinear3 $ \ix elem arr ->
  case indexInRange ix arr of
    (True, arr) -> unsafeSet ix elem arr
    (False, arr) -> elem `lseq` arr 

{-# INLINE setMaybe #-}

-- | Same as 'set', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: (Consumable a) => Int %1 -> a %1 -> Array a %1 -> Array a
unsafeSet ix val (Array arr) =
  Array (unsafeSet# ix val arr)
{-# INLINE unsafeSet #-}

unsafeSet# :: (Consumable a) => Int %1 -> a %1 -> Array# a %1 -> Array# a
unsafeSet# (GHC.I# ix) elem arr = fixup (Unsafe.toLinear3 unsafeSet'# ix elem arr)
  where
    unsafeSet'# :: (Consumable a) => GHC.Int# -> a -> Array# a -> (# a, Array# a #)
    unsafeSet'# i (a :: a) (Array# arr) =
      GHC.runRW# $ \st ->
        case (GHC.readArray# arr i) st of
          (# _, val #) ->
            case (GHC.writeArray# arr i a) st of
              _ -> (# val, Array# arr #)
    {-# NOINLINE unsafeSet'# #-} -- prevents the runRW# effect from being reordered
    fixup :: (Consumable a) => (# a, Array# a #) %1 -> Array# a
    fixup (# val, arr #) = consume val & (\() -> arr)
    -- fixup = Unsafe.toLinear (\(# val, arr #) -> arr )
    {-# INLINE fixup #-}
{-# INLINE unsafeSet# #-}

-- | Consumes the array by consuming all of its elements.
instance {-# INCOHERENT #-} (Consumable a) => Consumable (Array a) where
  consume :: (Consumable a) => Array a %1 -> ()
  consume (Array arr) = consume# arr

-- | When the elements of the array are allowed to be used unrestrictedly,
-- consuming the array is a no-op. (Individual elements do not need to be consumed in this case).
instance {-# INCOHERENT #-} Movable a => Consumable (Array (Ur a)) where
  consume = Unsafe.toLinear (const ())

-- | Duplicating an array requires a deep copy.
instance {-# INCOHERENT #-} (Dupable a) => Dupable (Array a) where
  dup2 (Array arr) = wrap (dup2# arr)
    where
      wrap :: (# Array# a, Array# a #) %1 -> (Array a, Array a)
      wrap (# a1, a2 #) = (Array a1, Array a2)

-- | When the elements of the array are allowed to be used unrestrictedly,
-- duplicating the array only requires duplicating the container;
-- individual elements do not need to be duplicated.
instance {-# INCOHERENT #-} Movable a => Dupable (Array (Ur a)) where
  dup2 (Array arr) = wrap (dup2Ur# arr)
    where
      wrap :: (# Array# (Ur a), Array# (Ur a) #) %1 -> (Array (Ur a), Array (Ur a))
      wrap (# a1, a2 #) = (Array a1, Array a2)

-- | Unique mutable arrays that do not depend on fusion.
instance Unique (Array a)

-- | Consume an 'Array#'.
-- This calls `consume` on all elements.
--
-- Note that we can not implement a 'Consumable' instance because 'Array#'
-- is unlifted.
lseq# :: (Consumable a) => Array# a %1 -> b %1 -> b
lseq# arr b = (consume# arr) & \() -> () `seq` b

consume# :: (Consumable a) => Array# a %1 -> ()
consume# arr = consume (toList# arr)
{-# NOINLINE consume# #-}

-- | Clone an Array#.
--
-- Note that we can not implement a 'Dupable' instance because 'Array#'
-- is unlifted.
dup2# :: (Dupable a) => Array# a %1 -> (# Array# a, Array# a #)
dup2# arr =
  -- Approach:
  -- (1) Duplicate each element We now have an array of pairs.
  -- (2) Clone the array. /!\ The clone now aliases the same pairs /!\.
  -- (3) Use only the first pair elem in the first array and the second pair elem in the cloned array. Uniqueness is now restored.
  Unsafe.toLinear go (map# dup2 arr)
  where
    cloneArr (Array# arr) =
      case GHC.runRW# (GHC.cloneMutableArray# arr 0# (GHC.sizeofMutableArray# arr)) of
        (# _, new #) -> Array# new
    {-# NOINLINE cloneArr #-}
    go :: Array# (a, a) -> (# Array# a, Array# a #)
    go arr = (# map# unsafeFst arr, map# unsafeSnd (cloneArr arr) #)
    unsafeFst :: (a, b) %1 -> a
    unsafeFst = Unsafe.toLinear (\(a, _) -> a)
    unsafeSnd :: (a, b) %1 -> b
    unsafeSnd = Unsafe.toLinear (\(_, b) -> b)

dup2Ur# :: Array# (Ur a) %1 -> (# Array# (Ur a), Array# (Ur a) #)
dup2Ur# = Unsafe.toLinear go
  where
    go :: Array# a -> (# Array# a, Array# a #)
    go (Array# arr) =
      case GHC.runRW#
        (GHC.cloneMutableArray# arr 0# (GHC.sizeofMutableArray# arr)) of
        (# _, new #) -> (# Array# arr, Array# new #)
{-# NOINLINE dup2Ur# #-}

-- | Check if given index is within the Array, otherwise panic.
assertIndexInRange :: (Consumable a) => Int %1 -> Array a %1 -> Array a
assertIndexInRange i arr =
  indexInRange i arr & \(bool, arr) ->
        if bool then arr
        else arr `lseq` error "Array: index out of bounds"
{-# INLINE[2] assertIndexInRange #-}

-- In the case of `Ur` elements we do not need to consume the array
fastAssertIndexInRange :: Int %1 -> Array (Ur a) %1 -> Array (Ur a)
fastAssertIndexInRange i arr =
  indexInRange i arr & \(bool, arr) ->
        if bool then arr
        else arr `unsafeForgettingLseq` error "Array: index out of bounds"
{-# RULES 
  "assertIndexInRange/Ur" forall i arr. assertIndexInRange i arr = fastAssertIndexInRange i arr
#-}

indexInRange :: Int %1 -> Array a %1 -> (Bool, Array a)
indexInRange i arr =
  dup2 i & \(i1, i2) ->
  size arr & \(s, arr) ->
    (0 <= i1 && i2 < s, arr)

-- | Map a linear function over an array.
--
-- Because the array's elements are lifted,
-- the memory representation of the input array and output array match
-- and thus we can re-use the input array's memory without doing extra allocation.
map :: (a %1 -> b) -> Array a %1 -> Array b
map f (Array arr) = Array (map# f arr)
{-# INLINE [1] map #-}

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
                    (# st, a #) ->
                      case GHC.writeArray# bs i (f a) st of
                        !st -> go (i GHC.+# 1#) st
         in GHC.runRW# (go 0#) `GHC.seq` Array# bs
    )
{-# NOINLINE map# #-}

{-# RULES
"map#/map#" forall f g. Unique.Array.map f . Unique.Array.map g = Unique.Array.map (f . g)
  #-}

consumingSum :: (AddIdentity a) => Array a %1 -> a
consumingSum arr =
  size arr & \(s, arr) ->
    go zero (move s) arr
  where
    go :: (AddIdentity a) => a %1 -> Ur Int %1 -> Array a %1 -> a
    go acc (Ur 0) arr =
      -- SAFETY: `arr` now only contains bottoms so forget rather than consume.
      arr `unsafeForgettingLseq` acc
    go acc (Ur i) arr =
      -- SAFETY: go is only called with `size arr` so `i` is always in range.
      unsafeSwap (i - 1) (error "Empty placeholder element from `consumingSum`") arr & \(a, arr') ->
        go (acc + a) (Ur (i - 1)) arr'

-- | Sort of an unconstrained version of `lseq`.
-- NOTE: intentionally _lazy_ in its first element! (`lseq` and `seq` are strict in their first element)
-- Used to get rid of 'known bottoms' during construction/desctruction of a container.
--
-- >>> (error "boom" :: Int) `unsafeForgettingLseq` 1000
-- 1000
--
-- >>> (error "boom" :: Int) `seq` 1000
-- boom
--
-- >>> (error "boom" :: Int) `lseq` 1000
-- boom
unsafeForgettingLseq :: a %1 -> b %1 -> b
unsafeForgettingLseq = Unsafe.toLinear (\_ b -> b)
{-# INLINE unsafeForgettingLseq #-}
