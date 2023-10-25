{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Linearly (Linearly, linearly, linearly', splitToken, LinearToken, unsafeGetLinearly) where
import Prelude.Linear
import qualified Unsafe.Linear as Unsafe

data Linearly = Linearly

-- | Run a linear function.
-- 
-- This is the main entry-point of working with linear functions and datastructures.
-- By providing this API, we can be sure that data structures which are not safe to alias
-- cannot be used accidentally outside of a linear context.
--
-- The `Movable` constraint on the return type ensures that the returned value *is* safe to alias/use outside of a linear context.
--
-- # Examples
--
-- >>> import Prelude hiding ((+))
-- >>> import Prelude.Linear
-- >>> let list = [1,2,3] in linearly (\() -> list & Array.fromList' & Array.arrOMap (+40) & Array.toList')
-- [41, 42, 43]
linearly :: Movable b => ((?lin :: () %1 -> Linearly) => () %1 -> b) %1 -> b
linearly f = let ?lin = Unsafe.toLinear (\_ -> Linearly) in f ()

linearly' :: (LinearToken s, Movable b) => (s %1 -> b) %1 -> b
linearly' f = f make

class LinearToken s where
    make :: s

instance LinearToken Linearly where
  make = Linearly

instance (LinearToken a, LinearToken b) => LinearToken (a, b) where
    make = (make, make)

splitToken :: LinearToken b => Linearly %1 -> b  
splitToken = Unsafe.toLinear (const make)

-- | UNSAFE: This is the 'back door' which allows you to run a linear function in a non-linear context.
-- The caller needs to be extremely careful to ensure that the returned result is really only used once.
--
-- Unless you're doing some low-level trickery, this is almost never what you want; use 'linearly' instead.
unsafeGetLinearly :: Linearly
unsafeGetLinearly = Linearly
