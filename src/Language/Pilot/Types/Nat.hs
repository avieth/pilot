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
{-# LANGUAGE PatternSynonyms #-}

module Language.Pilot.Types.Nat where

import Numeric.Natural
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty ((:|)))

import qualified GHC.TypeLits as GHC

import Language.Pilot.Types.Represented

data Nat where
  S :: Nat -> Nat
  Z :: Nat

-- | Useful for writing Nat types: Decimal 42 expands to something you would not
-- want to write out directly.
type family Decimal (n :: GHC.Nat) :: Nat where
  Decimal 0 = 'Z
  Decimal n = 'S (Decimal (n GHC.- 1))

-- | Inverts 'Decimal'
type family Unary (n :: Nat) :: GHC.Nat where
  Unary 'Z = 0
  Unary ('S n) = 1 GHC.+ Unary n

data NatRep (n :: Nat) where
  S_Rep :: NatRep t -> NatRep ('S t)
  Z_Rep :: NatRep 'Z

-- Is it possible to give a user-friendly way of writing NatRep? Or writing
-- Nats? Without explicitly writing out each synonym?
-- We might hope to get a base-10 or base-16 representation.

pattern Zero = Z_Rep
pattern One = S_Rep Zero
pattern Two = S_Rep One
pattern Three = S_Rep Two
pattern Four = S_Rep Three
pattern Five = S_Rep Four
pattern Six = S_Rep Five
pattern Seven = S_Rep Six
pattern Eight = S_Rep Seven
pattern Nine = S_Rep Eight

instance Represented Nat where
  type Rep Nat = NatRep

instance Known 'Z where
  known _ = Z_Rep

instance Known n => Known ('S n) where
  known _ = S_Rep (known (Proxy :: Proxy n))

data SomeNatRep where
  SomeNatRep :: NatRep n -> SomeNatRep

instance Eq SomeNatRep where
  n == m = (n `compare` m) == EQ

instance Ord SomeNatRep where
  SomeNatRep Z_Rep     `compare` SomeNatRep Z_Rep     = EQ
  SomeNatRep Z_Rep     `compare` SomeNatRep _         = LT
  SomeNatRep _         `compare` SomeNatRep Z_Rep     = GT
  SomeNatRep (S_Rep n) `compare` SomeNatRep (S_Rep m) =
    SomeNatRep n `compare` SomeNatRep m

natVal :: SomeNatRep -> Natural
natVal (SomeNatRep Z_Rep) = 0
natVal (SomeNatRep (S_Rep n)) = 1 + natVal (SomeNatRep n)

natToIntegral :: Integral a => NatRep n -> a
natToIntegral nrep = fromIntegral (natVal (SomeNatRep nrep))

class KnownNat (n :: Nat) where
  natRep :: proxy n -> NatRep n

instance KnownNat Z where
  natRep _ = Z_Rep

instance KnownNat n => KnownNat (S n) where
  natRep _ = S_Rep (natRep (Proxy :: Proxy n))

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

vecLength :: Vec n t -> NatRep n
vecLength VNil         = Z_Rep
vecLength (VCons _ vs) = S_Rep (vecLength vs)

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
vecReplicate Z_Rep     _ = VNil
vecReplicate (S_Rep n) t = VCons t (vecReplicate n t)

-- | If we can make a t for any offset up to a given number (including 0)
-- then we can make a vector of size 1 larger: if n ~ 'Z then we can use
-- the 0th offset to generate the sole element.
vecGenerateWithOffset
  :: forall n t .
     NatRep n
  -> (Offset n -> t)
  -> Vec ('S n) t
vecGenerateWithOffset Z_Rep     k = VCons (k Current) VNil
vecGenerateWithOffset (S_Rep n) k = VCons (k Current) (vecGenerateWithOffset n (k . Next))

index :: Index n -> Vec n t -> t
index Here (VCons t _) = t
index (There idx) (VCons _ vs) = index idx vs

-- | Get an index into a 0-indexed array.
indexToNat :: Index n -> Natural
indexToNat Here = 0
indexToNat (There here) = 1 + indexToNat here
