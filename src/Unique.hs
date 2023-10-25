{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE RankNTypes #-}
module Unique (
    -- | Class and combinator functions to work with unique values
    Unique, 
    consuming, 
    scoped,
    -- | The zero-info unique unit type
    UniqueUnit, 
    unit, 
) where
import Prelude.Linear
import qualified Prelude


-- | Implemented by types which can used only inside a scoped unique context.
--
-- Instances of this class can be used as 'uniqueness witnesses' to create more unique values.
--
-- ## Invariants:
-- - A type can either implement @Unique@ or @Movable@ but never both.
-- - A `Unique` has no (safe) public constructor. Instead, they are created by type-specific 'unique builder' functions.
--
-- ## 'unique builder' functions
-- A 'unique builder' function is a function of the type `(forall b. Unique b => b %1 -> (a, b))`
-- In other words: If you already have a Unique value `b`, you can use it as 'uniqueness witness' to create an `a`.
class Unique a where

-- | The zero-info unique unit type
-- This type is similar to @()@ except that the only way to obtain one is inside a scoped unique context.
--
-- To obtain one, use the @unit@ constructor, in one of the following ways:
-- - If you do not have a uniqueness witness yet, you can start an outer scope using `scoped unit :: Movable r => (UniqueUnit %1 -> r) %1 -> r`.
-- - If you are already in a unique context and have a uniqueness witness, you can use unit directly `unit :: Unique b => b %1 -> (UniqueUnit, b)`.
-- - If you have a uniqueness witness that you no longer need after this point, you can use `consuming unit :: (Unique a, Unique b, Consumable b) => b %1 -> a`
--
-- Using UniqueUnit directly is rarely useful in high-level code. (It is used internally in implementing the core of this library however!) 
-- Its main use-case in high-level code is if you have to delay the initial construction of any unique value until you're inside a linear scope for some reason.
data UniqueUnit = UniqueUnit

instance Unique UniqueUnit where

instance Consumable UniqueUnit where
    consume UniqueUnit = ()

instance Dupable UniqueUnit where
    dup2 UniqueUnit = (UniqueUnit, UniqueUnit)

-- | Given a uniqueness witness, create an extra @UniqueUnit@.
unit :: Unique b => b %1 -> (UniqueUnit, b)
unit x = (UniqueUnit, x)

-- | Helper instance which allows you to call many builder functions in a row,
-- without having to explicitly pass around the uniqueness witnesses each time.
-- 
-- At the end, you'll have a type `(a, (b, (c, (d, ...))))` of unique values (with the latest builder result as first element).
instance (Unique a, Unique b) => Unique (a, b)

-- | Combinator which turns a normal unique builder function into a consuming builder function: 
-- Given a `b` that you no longer need, consume it after using it as a uniqueness witness to create `a`.
consuming :: (Unique a, Unique b, Consumable b)  => (b %1 -> (a, b)) %1 -> b %1 -> a
consuming f = (\(a, b) -> b `lseq` a) . f

-- | Combinator which allows you to use a unique builder function to kickstart a unique scope.
--
-- Given a builder and a callback, run the callback with the built unique value. 
-- By restricting the callback's return type to @Movable@, no built unique values can escape its scope.
-- >>> scoped unit (\tok -> tok `lseq` "hello world")
-- "hello world"
scoped :: (Unique a, Movable r) => 
    (forall b. Unique b => b %1 -> (a, b)) -- ^ Builder function which when given a uniqueness witness creates a new unique value
    %1 -> (a %1 -> r)  -- ^ Scoped callback function
    %1 -> r -- ^ Final, non-unique result.
scoped builder callback = 
    UniqueUnit
    & consuming builder
    & callback
