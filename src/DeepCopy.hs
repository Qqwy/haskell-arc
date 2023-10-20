{-# LANGUAGE MagicHash #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingVia #-}

module DeepCopy where

import GHC.Exts
import GHC.Int
import GHC.Word
import GHC.Num.Integer (Integer (..))
import GHC.Num.Natural (Natural (..))
import qualified Data.Semigroup as Semigroup
import Prelude.Linear
import Prelude.Linear.Generically
import qualified Unsafe.Linear as Unsafe
import qualified Prelude
import Data.Void (Void)
import Data.List.NonEmpty (NonEmpty)
import Data.Tuple (Solo)

-- | Allows to create a 'deep copy' of a value.
--
-- This deep copy does not share any memory with the original value (or any other value in the program for that matter).
--
-- If you obtain such a copy in a linear context, you're able to mutate it in place, as you can be sure you're the only one holding a reference to it. 
-- 
-- Invariants:
-- - The first element of the returned pair might be the original value.
-- - The second element of the returned pair is a deep copy which shares no memory (directly nor indirectly) with any other values in the program.
-- - Both values should be equivalent (and equivalent to the original value), e.g. if there is an `Eq` instance, they should compare equal.
--
-- It is not usually necessary to implement this yourself;
-- use `deriving via Generically YourType instance DeepCopy YourType` to automatically derive it instead.
class DeepCopy a where
  deepCopy :: a %1 -> (a, a)

-- Primitives:
deriving via Generically Void instance DeepCopy Void
deriving via Generically () instance DeepCopy ()
deriving via Generically Prelude.Bool instance DeepCopy Prelude.Bool
deriving via Generically Prelude.Ordering instance DeepCopy Prelude.Ordering
deriving via Generically Prelude.Char instance DeepCopy Prelude.Char
deriving via Generically Prelude.Int instance DeepCopy Prelude.Int
deriving via Generically Prelude.Word instance DeepCopy Prelude.Word
deriving via Generically Prelude.Float instance DeepCopy Prelude.Float
deriving via Generically Prelude.Double instance DeepCopy Prelude.Double
-- Basic sum and product types:
deriving via Generically (Prelude.Maybe a) instance (DeepCopy a) => DeepCopy (Prelude.Maybe a)
deriving via Generically (Prelude.Either a b) instance (DeepCopy a, DeepCopy b) => DeepCopy (Prelude.Either a b)
deriving via Generically (Solo a) instance (DeepCopy a) => DeepCopy (Solo a)
deriving via Generically (a, b) instance (DeepCopy a, DeepCopy b) => DeepCopy (a, b)
deriving via Generically (a, b, c) instance (DeepCopy a, DeepCopy b, DeepCopy c) => DeepCopy (a, b, c)
deriving via Generically (a, b, c, d) instance (DeepCopy a, DeepCopy b, DeepCopy c, DeepCopy d) => DeepCopy (a, b, c, d)
deriving via Generically (a, b, c, d, e) instance (DeepCopy a, DeepCopy b, DeepCopy c, DeepCopy d, DeepCopy e) => DeepCopy (a, b, c, d, e)
deriving via Generically (a, b, c, d, e, f) instance (DeepCopy a, DeepCopy b, DeepCopy c, DeepCopy d, DeepCopy e, DeepCopy f) => DeepCopy (a, b, c, d, e, f)
deriving via Generically (a, b, c, d, e, f, g) instance (DeepCopy a, DeepCopy b, DeepCopy c, DeepCopy d, DeepCopy e, DeepCopy f, DeepCopy g) => DeepCopy (a, b, c, d, e, f, g)
-- Basic collections:
deriving via Generically [a] instance (DeepCopy a) => DeepCopy [a]
deriving via Generically (NonEmpty a) instance (DeepCopy a) => DeepCopy (NonEmpty a)

-- Semigroups
deriving newtype instance (DeepCopy a) => DeepCopy (Semigroup.Sum a)
deriving newtype instance (DeepCopy a) => DeepCopy (Semigroup.Product a)
deriving newtype instance DeepCopy Semigroup.All
deriving newtype instance DeepCopy Semigroup.Any

-- Other number types
instance DeepCopy Integer where
    deepCopy = Unsafe.toLinear $ \case
        orig@(IS i) -> (orig, IS i)
        orig@(IP i) -> (orig, IP i)
        orig@(IN i) -> (orig, IN i)

instance DeepCopy Natural where
    deepCopy = Unsafe.toLinear $ \case
      orig@(NS i) -> (orig, NS i)
      orig@(NB i) -> (orig, NB i)

instance (Generic a, GDeepCopy (Rep a)) => DeepCopy (Generically a) where
  deepCopy (Generically x) = x & genericDeepCopy & lBimap Generically

genericDeepCopy :: (Generic a, GDeepCopy (Rep a)) => a %1 -> (a, a)
genericDeepCopy val = val & from & gDeepCopy & lBimap to
{-# INLINEABLE genericDeepCopy #-}

class GDeepCopy f where
  gDeepCopy :: f a %1 -> (f a, f a)

instance GDeepCopy V1 where
  gDeepCopy = \case {}

instance GDeepCopy U1 where
  gDeepCopy U1 = (U1, U1)

instance (DeepCopy c) => GDeepCopy (K1 i c) where
  gDeepCopy (K1 x) = x & deepCopy & lBimap K1

instance GDeepCopy a => GDeepCopy (M1 i c a) where
  gDeepCopy (M1 x) = x & gDeepCopy & lBimap M1

instance GDeepCopy f => GDeepCopy (MP1 'One f) where
  gDeepCopy (MP1 x) = x & gDeepCopy & lBimap MP1

instance (GDeepCopy f, GDeepCopy g) => GDeepCopy (f :+: g) where
  gDeepCopy (L1 x) = x & gDeepCopy & lBimap L1
  gDeepCopy (R1 x) = x & gDeepCopy & lBimap R1

instance (GDeepCopy f, GDeepCopy g) => GDeepCopy (f :*: g) where
  gDeepCopy (x :*: y) =
    gDeepCopy x
      & \case
        (x1, x2) ->
          gDeepCopy y
            & \case
              (y1, y2) ->
                (x1 :*: y1, x2 :*: y2)

-- Helper function to apply a function to both elements of a pair linearly.
lBimap :: (a %1 -> b) -> (a, a) %1 -> (b, b)
lBimap f (x, y) = (f x, f y)

instance GDeepCopy UChar where
    gDeepCopy = Unsafe.toLinear (\orig@(UChar x) -> (orig, UChar x))

instance GDeepCopy UDouble where
    gDeepCopy = Unsafe.toLinear (\orig@(UDouble x) -> (orig, UDouble x))

instance GDeepCopy UFloat where
    gDeepCopy = Unsafe.toLinear (\orig@(UFloat x) -> (orig, UFloat x))

instance GDeepCopy UInt where
    gDeepCopy = Unsafe.toLinear (\orig@(UInt x) -> (orig, UInt x))

instance GDeepCopy UWord where
    gDeepCopy = Unsafe.toLinear (\orig@(UWord x) -> (orig, UWord x))
