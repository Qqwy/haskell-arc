{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Lib where

import qualified Prelude
import Data.IORef
import System.IO.Unsafe
import Prelude.Linear
import qualified Unsafe.Linear
import qualified System.IO.Linear as Linear
-- import Control.Functor.Linear
import qualified Data.Vector.Generic
import Data.Array.Mutable.Linear (Array)
import Debug.Trace (traceShow)
import qualified Data.Vector.Mutable.Linear
import qualified Data.Vector

data StrictPair a b = StrictPair !a !b
  deriving (Prelude.Eq, Prelude.Ord, Show)

someFunc :: IO ()
someFunc = print "Hello"

example :: Int -> StrictPair (Arc Int) (Arc Int)
example x =
  x
  & unsafeNew
  & dup
  & \(x1, y1) -> StrictPair x1 (modify y1 (+ 1))
  -- & \(x2, y2) -> (modify x2 (\val -> val - 1), y2)
  -- & \(x3, y3) -> (x3, modify y3 (+ 1))

-- someFunc :: IO ()
-- someFunc = Linear.withLinearIO $ do
--   -- let x = new 1 :: Arc Int
--   -- let (x', y) = dup x
--   Linear.fromSystemIOU ( putStrLn "hello")
--   pure (Ur ())
--   -- Linear.fromSystemIOU ( putStrLn "arc")
--   -- Linear.fromSystemIO $ print y

-- NOTE: I want to use `Word` for the count
-- But it seems many of the typeclasses in Linear are not implemented for `Word` yet.
newtype Arc a = Arc (IORef (Int, a))

-- TODO Is this unsafe as multiple references to the same `a` might exist?
unsafeNew :: a %1 -> Arc a
unsafeNew = Unsafe.Linear.toLinear $
  \val ->
    (1, val)
    & newIORef
    & unsafePerformIO
    & Arc

-- | Puts a (deep copy of an) `a` into an Arc.
--
-- Because the values is copied, it is later OK to use `modify` on the Arc.
-- NOTE: Possibly unsafe? We depend on the fact that in the result of `Dupable.dup2`,
-- the second element of the pair is a true copy of the first element.
new :: Dupable a => a %1 -> Arc a
new val = dup2 val & \(val', val'') -> val' `lseq` unsafeNew val''

count :: Arc a %1 -> (Ur Int, Arc a)
count = Unsafe.Linear.toLinear $
  \arc@(Arc ref) ->
    let c =
          ref
          & readIORef
          & unsafePerformIO
          & fst
    in
      (Ur c, arc)

contents :: Arc a %1 -> a
contents = Unsafe.Linear.toLinear $
  \(Arc ref) ->
  ref
  & readIORef
  & unsafePerformIO
  & snd

isUnique :: Arc a %1 -> (Ur Bool, Arc a)
isUnique arc =
  arc
  & count
  & \(Ur c, arc') -> (Ur (c == 1), arc')

modify :: Arc a %1 -> (a %1 -> a) %1 -> Arc a
modify = Unsafe.Linear.toLinear2 $
  \arc@(Arc ref) f ->
    case unsafePerformIO (readIORef ref) of
      (1, val) -> unsafePerformIO $! do
        -- In this branch we know for certain that the Arcis not shared across threads
        -- so no need for atomic operations.
        writeIORef ref (1, f val)
        Prelude.pure (Arc ref)
      (_, val) -> unsafeDecCount arc `seq` unsafeNew (f val)

-- class Thawable a where
--   type family Thawed a
--   thaw :: a %1 -> Thawed a
--   freeze :: Thawed a %1 -> a

-- fromThawed :: Thawable a => Thawed a %1 -> Arc a
-- fromThawed thawed =
--   thawed
--   & freeze
--   & new


instance Show a => Show (Arc a) where
  show arc =
    let
      showCount = 
        arc
        & count
        & \(Ur c, _) -> show c
      showContents = 
        arc
        & contents
        & show
    in
      "Arc {count=" <> showCount <> ",contents=" <> showContents <> "}"

instance Prelude.Eq a => Prelude.Eq (Arc a) where
  lhs == rhs = contents lhs Prelude.== contents rhs

instance Prelude.Ord a => Prelude.Ord (Arc a) where
  compare lhs rhs = contents lhs `Prelude.compare` contents rhs

instance Eq a => Eq (Arc a) where
  lhs == rhs = contents lhs == contents rhs

instance Ord a => Ord (Arc a) where
  compare lhs rhs = contents lhs `compare` contents rhs

-- | Consuming an Arc is cheap; it just decrements the refcount.
-- If the last reference goes out of scope,
-- the contents of the Arc might be garbage collected during the next GC pass
instance Consumable (Arc a) where
  consume = Unsafe.Linear.toLinear $
    \arc -> unsafeDecCount arc `seq` ()

-- | Duplicating an Arc is cheap; only the reference count is incremented
instance Dupable (Arc a) where
  dup2 = Unsafe.Linear.toLinear $
    \arc -> unsafeIncCount arc `seq` (arc, arc)

-- TODO does this signature make sense?
-- Or does (the non-linear) `Arc a -> ()` make more sense?
unsafeIncCount :: Arc a %1 -> Arc a
unsafeIncCount = Unsafe.Linear.toLinear $
  \arc@(Arc ref) ->
    ref
    & flip atomicModifyIORef' (\(c, val) -> ((c + 1, val), arc))
    & unsafePerformIO
    -- & traceShow "unsafeIncCount"

-- TODO does this signature make sense?
-- Or does (the non-linear) `Arc a -> ()` make more sense?
unsafeDecCount :: Arc a %1 -> Arc a
unsafeDecCount = Unsafe.Linear.toLinear $
    \arc@(Arc ref) ->
      ref
      & flip atomicModifyIORef' (\(c, val) -> ((c - 1, val), arc))
      & unsafePerformIO
      -- & traceShow "unsafeDecCount"