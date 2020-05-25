{-|
Module      : Pilot.Types.Stream
Description : Type for an infinite stream with finite "prefix" section
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.Types.Stream
  ( Stream (..)
  , streamFromInitVec
  , streamFromInitVec'
  , streamToList
  , streamRepeat
  , streamDrop
  , streamShift
  , streamZip
  , streamMap
  , streamArgs
  , streamApply
  ) where

import qualified Data.Kind as Haskell (Type)
import Pilot.Types.Fun
import Pilot.Types.Nat

-- | Pure Haskell streams. A target for stream expressions which gives pure
-- in-Haskell evaluation (suitable for simulation, for example, of an
-- expression which may also target C).
--
-- This also serves as a reference definition/implementation for any other
-- stream target. There must be a coherence with this idea. TODO explain
-- exactly what that coherence must be.
--
-- These are infinite lists with a prefix of size determined by the Nat type
-- parameter. Elements of the list are in 'Pilot.Types.Pilot.Point', so that
-- the kind of the final type parameter is 'Pilot.Types.Pilot.Kind'.
data Stream (f :: k -> Haskell.Type) (n :: Nat) (p :: k) where
  Prefix :: f t -> Stream f  n t -> Stream f ('S n) t
  Suffix :: f t -> Stream f 'Z t -> Stream f  'Z    t

streamToList :: Stream f n t -> [f t]
streamToList (Prefix ft next) = ft : streamToList next
streamToList (Suffix ft next) = ft : streamToList next

streamRepeat :: NatRep n -> f t -> Stream f n t
streamRepeat Z_t     pt = Suffix pt (streamRepeat Z_t pt)
streamRepeat (S_t n) pt = Prefix pt (streamRepeat n   pt)

streamDrop :: Stream f ('S n) t -> Stream f n t
streamDrop (Prefix _ s) = s

-- TODO
-- this is not sufficiently lazy.
-- Can we improve it?
-- It's a _requirement_ that shifting the stream does not force anything
-- other than the prefix... But apparently we need to match on the suffix.
streamShift :: Stream f ('S n) t -> Stream f n t
--streamShift (Prefix t ts) = 
streamShift (Prefix t (Suffix t' ts))  = Suffix t (Suffix t' ts)
streamShift (Prefix t ts@(Prefix _ _)) = Prefix t (streamShift ts)

streamFromInitVec :: Vec n (f t) -> Stream f 'Z t -> Stream f n t
streamFromInitVec VNil         suffix = suffix
streamFromInitVec (VCons t ts) suffix = Prefix t (streamFromInitVec ts suffix)

streamFromInitVec' :: Vec (S n) (f t) -> Stream f 'Z t -> Stream f n t
streamFromInitVec' (VCons t VNil)           suffix = Suffix t suffix
streamFromInitVec' (VCons t ts@(VCons _ _)) suffix = Prefix t (streamFromInitVec' ts suffix)

streamMap :: (f s -> g t) -> Stream f n s -> Stream g n t
streamMap f (Prefix a as) = Prefix (f a) (streamMap f as)
streamMap f (Suffix a as) = Suffix (f a) (streamMap f as)

streamZip
  :: (f s -> g t -> h u)
  -> Stream f n s
  -> Stream g n t
  -> Stream h n u
streamZip f (Prefix a as) (Prefix b bs) = Prefix (f a b) (streamZip f as bs)
streamZip f (Suffix a as) (Suffix b bs) = Suffix (f a b) (streamZip f as bs)

-- One way to do this is to create an Args over streams using streamZip...
--
--   Args (Stream f n) args -> Stream (Args f) n args
--

-- | Arguments in `Stream f n` can be zipped together into one stream of
-- arguments. Analagous to zipping a list from a tuple of lists
--
--   ([a], [b]) -> [(a, b)]
--
streamArgs :: NatRep n -> Args (Stream f n) args -> Stream (Args f) n args
streamArgs nrep Args         = streamRepeat nrep Args
streamArgs nrep (Arg s args) = streamZip Arg s (streamArgs nrep args)

-- | A function on `f` arguments can be made into a function over streams over
-- `f`, but zipping the arguments and applying.
streamApply
  :: NatRep n
  -> (Args f args -> f r)
  -> Args (Stream f n) args
  -> Stream f n r
streamApply nrep k args = streamMap k (streamArgs nrep args)
