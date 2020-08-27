{-|
Module      : Language.Pilot.Examples.Copilot.Voting
Description : Boyer-Moore voting algorithm in pilot
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

-- Inspired by the copilot voting example below:
--
-- > {-# LANGUAGE RebindableSyntax #-}
-- > 
-- > module Copilot.Library.Voting 
-- >   ( majority, aMajority ) where
-- > 
-- > import Copilot.Language
-- > import qualified Prelude as P
-- > 
-- > -- | Majority vote first pass: choosing a candidate.
-- > majority :: (P.Eq a, Typed a) =>
-- >             [Stream a] -- ^ Vote streams
-- >             -> Stream a -- ^ Candidate stream
-- > majority []     = badUsage "majority: empty list not allowed"
-- > majority (x:xs) = majority' xs x 1
-- > 
-- > -- Alternate syntax of local bindings.
-- > majority' :: (P.Eq a, Typed a)
-- >    => [Stream a] -> Stream a -> Stream Word32 -> Stream a
-- > majority' []     can _   = can
-- > majority' (x:xs) can cnt =
-- >   local (cnt == 0) inZero
-- >   where 
-- >   inZero zero    = local (if zero then x else can) inCan
-- >     where       
-- >     inCan can'   = local (if zero || x == can then cnt+1 else cnt-1) inCnt
-- >       where 
-- >       inCnt cnt' = majority' xs can' cnt'
-- > 
-- > -- | Majority vote second pass: checking that a candidate indeed has more than
-- > -- half the votes.
-- > aMajority :: (P.Eq a, Typed a) =>
-- >              [Stream a] -- ^ Vote streams
-- >              -> Stream a -- ^ Candidate stream
-- >              -> Stream Bool -- ^ True if candidate holds majority
-- > aMajority [] _ = badUsage "aMajority: empty list not allowed"
-- > aMajority xs can =
-- >   let
-- >     cnt = aMajority' 0 xs can
-- >   in
-- >     (cnt * 2) > fromIntegral (length xs)
-- > 
-- > aMajority' :: (P.Eq a, Typed a)
-- >   => Stream Word32 -> [Stream a] -> Stream a -> Stream Word32
-- > aMajority' cnt []     _   = cnt
-- > aMajority' cnt (x:xs) can =
-- >   local (if x == can then cnt+1 else cnt) $ \ cnt' ->
-- >     aMajority' cnt' xs can
--
--
-- This is a very interesting one because it shows a recursive definition of
-- an EDSL expression: you can do the voting algorithm for arbitrarily-many
-- data points. In copilot that's fine: just recurse on the list of streams
-- and combine them into a bigger stream. We could do the same thing in pilot
-- but it seems weird: do we recurse on constants or on varyings? The latter,
-- because ultimately we want to give varyings to the voting algorithm, but
-- also the former, because the voting algorithm itself must be defined
-- pointwise and then lifted/mapped over varyings, as is the general
-- programming style in this EDSL.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pilot.Examples.Copilot.Voting where

import qualified Prelude
import Language.Pilot

-- To start, let's look at two different notions of foldr/foldl
--
-- First, the "vanilla" folds, which are the typical folds but they use
-- the EDSL's meta-language functions. They're written out explicitly, but
-- really are just the Prelude foldl/foldr, with conversion to the <@>
-- application of the EDSL Repr.
--
-- > foldr_vanilla f = Prelude.foldr (\x y -> f <@> x <@> y)
--
-- > foldl_vanilla f = Prelude.foldl (\x y -> f <@> x <@> y)

foldr_vanilla :: forall f val a b .
     ( Monad f )
  => Repr f val (a :-> b :-> b)
  -> Repr f val b
  -> [Repr f val a]
  -> Repr f val b
foldr_vanilla _ b []     = b
foldr_vanilla f b (a:as) = f <@> a <@> foldr_vanilla f b as

foldl_vanilla :: forall f val a b .
     ( Monad f )
  => Repr f val (b :-> a :-> b)
  -> Repr f val b
  -> [Repr f val a]
  -> Repr f val b
foldl_vanilla _ b [] = b
foldl_vanilla f b (a:as) = foldl_vanilla f (f <@> b <@> a) as

-- These are legitimately useful definitions, but the problem is that we
-- cannot lift/map them, because the `[Repr f val a]` type cannot be "brought
-- in" to the EDSL as functions and binary products can. And even if they
-- could, we still wouldn't be able to map them: the correspondence between
-- `Constant` and `Varying n` works only over arrows and products, not sums or
-- recursive datatypes like lists.
--
-- What we're really after here is something that does not involve lists at
-- all, but rather some finite product of a _known_ yet _variable_ size.
-- That's to say, our recursion scheme should be defined for any size of
-- product, but that size should be known statically, so that what we get is
-- just a plain old product, and so the resulting function fits into the
-- `Constant`/`Varying n` applicative functor.

foldr :: forall f val a b n . NatRep n -> E f val
  (   (a :-> b :-> b)
  :-> b
  :-> Vector n a
  :-> b
  )
foldr nrep = fun $ \f -> fun $ \b -> fun $ \as -> case nrep of
  Z_Rep                -> b
  S_Rep Z_Rep          -> f <@> as <@> b
  S_Rep nrep@(S_Rep _) -> f <@> fst as <@> (foldr nrep <@> f <@> b <@> snd as)

foldl :: forall f val a b n . NatRep n -> E f val
  (   (b :-> a :-> b)
  :-> b
  :-> Vector n a
  :-> b
  )
foldl nrep = fun $ \f -> fun $ \b -> fun $ \as -> case nrep of
  Z_Rep                -> b
  S_Rep Z_Rep          -> f <@> b <@> as
  S_Rep nrep@(S_Rep _) -> foldl nrep <@> f <@> (f <@> b <@> fst as) <@> snd as

-- Here are uncurried versions, which can be used in a map from `Constant` to
-- `Varying n`. Notice that the function argument is not put into the product.
-- Once that has been given, the result is a mappable function. NB: the function
-- would be over `Constant`s, giving a fold over `Constants`, which can be
-- lifted to a fold over `Varying n`s, which (I think) should correspond in some
-- sane way to the fold applied to a mapped function.
-- TODO elaborate on this.

foldr_ :: forall f val a b n . NatRep n -> E f val
  (   (a :-> b :-> b)
  :-> (b :* Vector n a)
  :-> b
  )
foldr_ nrep = fun $ \f -> fun $ \args -> foldr nrep <@> f <@> (fst args) <@> (snd args)

foldl_ :: forall f val a b n . NatRep n -> E f val
  (   (b :-> a :-> b)
  :-> (b :* Vector n a)
  :-> b
  )
foldl_ nrep = fun $ \f -> fun $ \args -> foldl nrep <@> f <@> (fst args) <@> (snd args)

-- Let's move on to the Boyer-Moore voting algorithm, so that we have something
-- to fold.

-- | First pass of the Boyer-Moore algorithm: fold this over a list of UInt8s
-- and it will give the candidate. If there is a majority, then this is
-- definitely the majority element.
boyerMooreCandidateStep :: forall f val . E f val
  (   (Obj (Constant UInt8) :* Obj (Constant UInt8))
  :->  Obj (Constant UInt8)
  :-> (Obj (Constant UInt8) :* Obj (Constant UInt8))
  )
boyerMooreCandidateStep = fun $ \acc -> fun $ \cur ->
  let maj = fst acc -- The current majority candidate
      cnt = snd acc -- The count so far
  in  ifThenElse (cnt == u8 0) (cur &> u8 1) $
        ifThenElse (cur == maj) (cur &> (cnt + u8 1)) $
          (maj &> (cnt - u8 1))

-- | Second pass of the Boyer-Moore algorithm: when used in a fold, it counts
-- the occurrences of the number given as the first parameter.
boyerMooreCountStep :: forall f val . E f val
  (   Obj (Constant UInt8) -- candidate
  :-> Obj (Constant UInt8) -- count so far
  :-> Obj (Constant UInt8) -- current element
  :-> Obj (Constant UInt8)
  )
boyerMooreCountStep = fun $ \candidate -> fun $ \count -> fun $ \current ->
  ifThenElse (current == candidate) (count + u8 1) count

boyerMoore :: forall n f val . NatRep n -> E f val
  (   Vector n (Obj (Constant UInt8))
  :-> Obj (Constant (Maybe UInt8))
  )
boyerMoore numElements = fun $ \elements ->
  local_auto (foldl_ numElements <@> boyerMooreCandidateStep <@> ((u8 0 <& u8 0) <& elements)) $ \result ->
    local_auto (foldl_ numElements <@> (boyerMooreCountStep <@> fst result) <@> (u8 0 <& elements)) $ \totalCount ->
      -- Would check for overflow or use a wider integer type.
      ifThenElse ((u8 2 * totalCount) > listSize) (just (fst result)) nothing
  where
  listSize = u8 (natToIntegral numElements)

{-
let a = constant_auto Zero <@> u8 1
    b = constant_auto Zero <@> u8 2
    c = Repr.object (varying (Language.Pilot.Interp.Pure.cycle [constantToPoint (u8 1), constantToPoint (u8 2)]))
in  showPureStream (Just 10) boyerMooreVarying Zero Three <@> (a &> b &> c)
-}

-- | To map boyerMoore up to varying, we can't use map_auto, because GHC cannot
-- reduce Vector (m is unknown) and therefore cannot figure out what the type
-- should be. That's alright though, because we can do it manually.
boyerMooreVarying :: forall n m f val . NatRep n -> NatRep m -> E f val
  (   Vector m (Obj (Varying n UInt8))
  :-> Obj (Varying n (Maybe UInt8))
  )
boyerMooreVarying numPrefix numElements =
  -- Use of map requires type reps for s, t, q, r, and then the rep for the
  -- prefix size (for each different n, Varying n is a different functor).
  -- See the where clause for explanation of what these are
  (map srep trep qrep rrep numPrefix
    -- Characterizes the LHS of the arrow being mapped. This is the part that
    -- GHC can't figure out automatically, because it uses the Vector type
    -- family, but we can help it by using the NatReps that the caller provides.
    (vectorMapImage (Proxy :: Proxy UInt8) numPrefix numElements)
    -- Characterizes the RHS of the arrow being mapped: it's just an object (the
    -- maybe majority element).
    MapObject
  ) <@> boyerMoore numElements
  where
  -- s and t are the LHS and RHS respectively of the arrow being mapped.
  -- The types are obvious: just look at the type of 'boyerMoore' and read
  -- them off.
  srep = vector_t numElements (object_t (constant_t uint8_t))
  trep = object_t (constant_t (maybe_t uint8_t))
  -- q and r are the LHS and RHS of the mapped arrow. They look just like s
  -- and t except that constants become varyings of the given prefix size.
  qrep = vector_t numElements (object_t (varying_t numPrefix uint8_t))
  rrep = object_t (varying_t numPrefix (maybe_t uint8_t))

-- Something to think about: under what conditions are qqq and qqq' the same?

qq :: E f val
  (   ((Obj (Constant UInt8) :* Obj (Constant UInt8)) :* Vector (Decimal 2) (Obj (Constant UInt8)))
  :->  (Obj (Constant UInt8) :* Obj (Constant UInt8))
  )
qq = foldl_ Two <@> boyerMooreCandidateStep

qqq :: E f val
  (   ((Obj (Varying 'Z UInt8) :* Obj (Varying 'Z UInt8)) :* Vector (Decimal 2) (Obj (Varying 'Z UInt8)))
  :->  (Obj (Varying 'Z UInt8) :* Obj (Varying 'Z UInt8))
  )
qqq = map_auto Zero <@> qq

qqq' :: E f val
  (   ((Obj (Varying 'Z UInt8) :* Obj (Varying 'Z UInt8)) :* Vector (Decimal 2) (Obj (Varying 'Z UInt8)))
  :->  (Obj (Varying 'Z UInt8) :* Obj (Varying 'Z UInt8))
  )
qqq' = foldl_ Two <@> (curry <@> (map_auto Zero <@> (uncurry <@> boyerMooreCandidateStep)))
