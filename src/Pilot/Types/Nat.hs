{-|
Module      : Pilot.Types.Nat
Description : Typical inductive Nat type and related stuff.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.Types.Nat where

import Numeric.Natural
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty ((:|)))

import Pilot.Types.Represented

data Nat where
  S :: Nat -> Nat
  Z :: Nat

data NatRep (n :: Nat) where
  S_t :: NatRep t -> NatRep ('S t)
  Z_t :: NatRep 'Z

instance Represented Nat where
  type Rep Nat = NatRep

instance Auto 'Z where
  repVal _ = Z_t

instance Auto n => Auto ('S n) where
  repVal _ = S_t (repVal (Proxy :: Proxy n))

data SomeNatRep where
  SomeNatRep :: NatRep n -> SomeNatRep

instance Eq SomeNatRep where
  n == m = (n `compare` m) == EQ

instance Ord SomeNatRep where
  SomeNatRep Z_t     `compare` SomeNatRep Z_t     = EQ
  SomeNatRep Z_t     `compare` SomeNatRep _       = LT
  SomeNatRep _       `compare` SomeNatRep Z_t     = GT
  SomeNatRep (S_t n) `compare` SomeNatRep (S_t m) =
    SomeNatRep n `compare` SomeNatRep m

natVal :: SomeNatRep -> Natural
natVal (SomeNatRep Z_t) = 0
natVal (SomeNatRep (S_t n)) = 1 + natVal (SomeNatRep n)

class KnownNat (n :: Nat) where
  natRep :: proxy n -> NatRep n

instance KnownNat Z where
  natRep _ = Z_t

instance KnownNat n => KnownNat (S n) where
  natRep _ = S_t (natRep (Proxy :: Proxy n))

type family Plus (n :: Nat) (m :: Nat) :: Nat where
  Plus n Z = n
  Plus Z m = m
  Plus (S n) m = S (Plus n m)

type family Minus (n :: Nat) (m :: Nat) :: Nat where
  Minus n Z = n
  Minus (S n) (S m) = Minus n m

type family Min (n :: Nat) (m :: Nat) :: Nat where
  Min n      Z    = Z 
  Min Z      n    = Z
  Min (S n) (S m) = S (Min n m)

type family Minimum (ns :: [Nat]) :: Nat where
  Minimum (n ': ns) = Min n (Minimum ns)

-- | A number less than or equal to some number (see also 'Index').
data Offset (n :: Nat) where
  Current :: Offset n
  Next    :: Offset n -> Offset ('S n)

offsetToNatural :: Offset n -> Natural
offsetToNatural Current    = 0
offsetToNatural (Next off) = 1 + offsetToNatural off

-- | A function which expects a wider range of offsets can be made into one
-- which expects a smaller range, by calling the original with 1 + the given
-- offset.
withNextOffset :: (Offset (S n) -> t) -> Offset n -> t
withNextOffset k = \offset -> k (Next offset)

-- | A function which expects a wider range of offsets can be made into one
-- which expects a smaller range, by calling the original with the same offset,
-- because we know it always fits.
withSameOffset :: (Offset (S n) -> t) -> Offset n -> t
withSameOffset k = \offset -> k (smallerOffset offset)
  where
  -- proof that a smaller offset fits into a wider offset.
  smallerOffset :: Offset n -> Offset (S n)
  smallerOffset Current = Current
  smallerOffset (Next n) = Next (smallerOffset n)

-- | A number strictly less than some number (see also 'Offset').
data Index (n :: Nat) where
  Here  :: Index (S n)
  There :: Index n -> Index (S n)

offsetToIndex :: Offset ('S n) -> Index ('S n)
offsetToIndex Current             = Here
offsetToIndex (Next Current)      = Here
offsetToIndex (Next off@(Next _)) = There (offsetToIndex off)

-- | The same Index, but with a higher type parameter.
lowerIndex :: Index n -> Index (S n)
lowerIndex Here = Here
lowerIndex (There i) = There (lowerIndex i)

data Vec (n :: Nat) (t :: Type) where
  VNil  :: Vec Z t
  VCons :: t -> Vec n t -> Vec (S n) t

vecToList :: Vec n t -> [t]
vecToList VNil = []
vecToList (VCons t vs) = t : vecToList vs

vecToNonEmpty :: Vec (S n) t -> NonEmpty t
vecToNonEmpty (VCons t vs) = t :| vecToList vs

vecMap :: (s -> t) -> Vec n s -> Vec n t
vecMap _ VNil = VNil
vecMap f (VCons t vs) = VCons (f t) (vecMap f vs)

vecTraverse :: Applicative f => (s -> f t) -> Vec n s -> f (Vec n t)
vecTraverse f VNil = pure VNil
vecTraverse f (VCons t ts) = VCons <$> f t <*> vecTraverse f ts

vecLength :: Vec n t -> Natural
vecLength VNil = 0
vecLength (VCons _ vs) = 1 + vecLength vs

vecReverse :: Vec n t -> Vec n t
vecReverse VNil = VNil
vecReverse (VCons t ts) = vecSnoc (vecReverse ts) t

vecSnoc :: Vec n t -> t -> Vec (S n) t
vecSnoc VNil t = VCons t VNil
vecSnoc (VCons t ts) t' = VCons t (vecSnoc ts t')

vecDropLast :: Vec (S n) t -> Vec n t
vecDropLast (VCons _ VNil)           = VNil
vecDropLast (VCons v vs@(VCons _ _)) = VCons v (vecDropLast vs)

vecReplicate :: NatRep n -> t -> Vec n t
vecReplicate Z_t     _ = VNil
vecReplicate (S_t n) t = VCons t (vecReplicate n t)

index :: Index n -> Vec n t -> t
index Here (VCons t _) = t
index (There idx) (VCons _ vs) = index idx vs

-- | Get an index into a 0-indexed array.
indexToNat :: Index n -> Natural
indexToNat Here = 0
indexToNat (There here) = 1 + indexToNat here
