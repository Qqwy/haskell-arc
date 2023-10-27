{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE RankNTypes #-}
module Unique (
    -- | = Class and combinator functions to work with unique values
    Unique,
    scoped,
    consuming,
    -- | = UniqueUnit: the zero-info unique witness type
    UniqueUnit, 
    unit, 
) where
import Prelude.Linear

-- | Implemented by types which can used only inside a scoped unique context.
--
-- Instances of this class can be used as 'uniqueness witnesses' to create more unique values.
--
-- = Invariants:
--
-- - A type can either implement @Unique@ or @Movable@ but never both.
-- - A `Unique` has no (safe) normal public constructor. Instead, they are created by type-specific 'unique constructor' functions.
--
-- = 'unique constructor' functions #unique_constructor#
--
-- A normal constructors has the type @... -> a@. 
--
-- A 'unique constuctor' on the other hand has the type @Unique witness => ... -> witness %1 -> (a, witness)@.
--
-- In other words: Only if you already have a Unique value `witness`, you can use it as to create an `a`.
--
-- Because linearity is 'infectious', the uniqueness of the witness is 'inherited' by the constructed value. 
-- This is how we can ensure that the constructed value can never be accidentally aliased.
--
-- With all but the last parameter filled in (courtesy of partial application), the type of a 'unique constructor' becomes @Unique witness => witness %1 -> (a, witness)@.
-- This can be passed to the @scoped@ or @consuming@ combinators to change the way you create a unique value:
--
-- - `scoped` is the only way to create the 'first' unique value if you don't have any yet. Because the unique value cannot escape the callback, this is safe.
-- - `consuming` is syntactic sugar to get rid of a no-longer useful unique value while creating a new one.
class Unique u where

-- | The zero-info unique unit type
-- This type is similar to @()@ except that the only way to obtain one is inside a scoped unique context.
--
-- To obtain one, use the `unit` constructor, in one of the following ways:
--
-- - If you do not have a uniqueness witness yet, you can start an outer scope using @scoped unit :: Movable r => (UniqueUnit %1 -> r) %1 -> r@.
-- - If you are already in a unique context and have a uniqueness witness, you can use unit directly @unit :: Unique witness => witness %1 -> (UniqueUnit, witness)@.
-- - If you have a uniqueness witness that you no longer need after this point, you can use @consuming unit :: (Unique witness, Consumable witness) => witness %1 -> UniqueUnit@
--
-- Using UniqueUnit directly is rarely useful in high-level code. (It is used internally in implementing the core of this library however!) 
-- Its main use-case in high-level code is if you have to delay the initial construction of any unique value until you're inside a linear scope for some reason.
data UniqueUnit = UniqueUnit

instance Unique UniqueUnit where

instance Consumable UniqueUnit where
    consume UniqueUnit = ()

instance Dupable UniqueUnit where
    dup2 UniqueUnit = (UniqueUnit, UniqueUnit)

-- | [Unique constructor]("Unique#unique_constructor") for `UniqueUnit`.
unit :: Unique witness => witness %1 -> (UniqueUnit, witness)
unit x = (UniqueUnit, x)
{-# INLINE unit #-}

-- | Helper instance which allows you to call many unique constructor functions in a row,
-- without having to explicitly pass around the uniqueness witnesses each time.
-- 
-- At the end, you'll have a type `(a, (b, (c, (d, ...))))` of unique values (with the latest constructor result as first element).
instance (Unique a, Unique b) => Unique (a, b)

-- | Combinator which turns a normal unique constructor function into a consuming constructor function: 
-- Given a `b` that you no longer need, consume it after using it as a uniqueness witness to create `a`.
consuming :: (Unique u, Unique witness, Consumable witness)  => (witness %1 -> (u, witness)) %1 -> witness %1 -> u
consuming f = (\(a, b) -> b `lseq` a) . f
{-# INLINE consuming #-}

-- | Combinator which allows you to use a unique constructor function to kickstart a unique scope.
--
-- Given a constructor and a callback, run the callback with the built unique value. 
-- By restricting the callback's return type to @Movable@, no built unique values can escape its scope.
--
-- >>> scoped unit (\tok -> tok `lseq` "hello world")
-- "hello world"
--
--
-- > >>> scoped unit (\tok -> tok) -- COMPILE ERROR (UniqueUnit is not Movable)
--
scoped :: (Unique u, Movable r) => 
    (forall witness. Unique witness => witness %1 -> (u, witness)) -- ^ constructor function which when given a uniqueness witness creates a new unique value
    %1 -> (u %1 -> r)  -- ^ Scoped callback function
    %1 -> r -- ^ Final, non-unique result.
scoped constructor callback = 
    UniqueUnit
    & consuming constructor
    & callback
{-# INLINE scoped #-}