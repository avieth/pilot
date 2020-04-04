{-|
Module      : Pilot.Types.Stream
Description : List-like type with a prefix size type parameter
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.Types.Stream
  ( Stream (..)

  , map

  , repeat
  , consPrefix
  , unconsPrefix
  , shift
  , index
  , ap
  , zip
  , toList

  , Prefix (..)
  , takeAt
  ) where

import Prelude hiding (map, repeat, zip)
import Data.Kind (Type)
import Pilot.Types.Nat

-- | An infinite list with a given number of "prefix" parts.
data Stream (n :: Nat) (t :: Type) where
  Prefix :: t -> Stream n t -> Stream (S n) t
  Suffix :: t -> Stream Z t -> Stream Z t

map :: (s -> t) -> Stream n s -> Stream n t
map f (Prefix t ts) = Prefix (f t) (map f ts)
map f (Suffix t ts) = Suffix (f t) (map f ts)

repeat :: t -> Stream Z t
repeat t = Suffix t (repeat t)

-- | Put a piece on the prefix.
consPrefix :: t -> Stream n t -> Stream (S n) t
consPrefix t p@(Prefix _ _) = Prefix t p
consPrefix t s@(Suffix _ _) = Prefix t s

-- | Take a piece off of the prefix.
unconsPrefix :: Stream (S n) t -> (t, Stream n t)
unconsPrefix (Prefix t rest) = (t, rest)

-- | Put the last prefix element into the suffix.
shift :: Stream (S n) t -> Stream n t
shift (Prefix t s@(Suffix _ _)) = Suffix t s
shift (Prefix t p@(Prefix _ _)) = Prefix t (shift p)

index :: Index n -> Stream n t -> t
index  Here       (Prefix t _)    = t
index (There idx) (Prefix _ next) = index idx next

data Prefix (n :: Nat) where
  Earliest :: Prefix n
  Later :: Prefix n -> Prefix (S n)

takeAt :: Prefix n -> Stream n t -> t
takeAt Earliest  (Suffix t _)  = t
takeAt Earliest  (Prefix t _)  = t
takeAt (Later p) (Prefix _ ts) = takeAt p ts

toList :: Stream n t -> [t]
toList (Prefix t rest) = t : toList rest
toList (Suffix t rest) = t : toList rest

-- | Like <*> for typical lists.
--
-- TODO is this preferable to zip?
-- We shall see which is easier to deal with.
ap :: Stream m (a -> b) -> Stream n a -> Stream (Min m n) b
ap (Prefix f fs) (Prefix x xs) = Prefix (f x) (ap fs xs)
ap (Suffix f fs) (Suffix x xs) = Suffix (f x) (ap fs xs)
ap (Prefix f fs) (Suffix x xs) = Suffix (f x) (ap fs xs)
ap (Suffix f fs) (Prefix x xs) = Suffix (f x) (ap fs xs)

-- | Like `zipWith` for typical lists.
zip :: (a -> b -> c) -> Stream m a -> Stream n b -> Stream (Min m n) c
zip f (Prefix a as) (Prefix b bs) = Prefix (f a b) (zip f as bs)
zip f (Suffix a as) (Suffix b bs) = Suffix (f a b) (zip f as bs)
zip f (Prefix a as) (Suffix b bs) = Suffix (f a b) (zip f as bs)
zip f (Suffix a as) (Prefix b bs) = Suffix (f a b) (zip f as bs)

-- Example to show that these are sufficiently lazy.
-- GHC does not know that `n ~ Min n (S n)` for arbitrary `n`, but it will
-- figure it out when `n` is known.
integral
  :: forall n .
     ( n ~ Min n (S n) )
  => Stream n Int
  -> Stream n Int
integral ds = next
  where
  sums :: Stream (S n) Int
  sums = Prefix 0 next
  next :: Stream n Int
  next = zip (+) ds sums
