{-|
Module      : Examples
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Examples where

import qualified Data.Kind as Haskell (Type)
import Data.Proxy (Proxy (..))
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Pilot.EDSL.Expr
import Pilot.EDSL.Point (Type (..), All (..), Any (..), Case (..), ExprF (..),
  Selector (..))
import qualified Pilot.EDSL.Point as Point
import Pilot.EDSL.Stream
import qualified Pilot.EDSL.Stream as Stream
import Pilot.EDSL.Lifted
import Pilot.Types.Fun
import Pilot.Types.Nat
import Pilot.Types.Represented

import qualified Pilot.C as C

-- |
-- = Examples of streamwise expressions
--
-- TODO some examples of streams and lifting.
-- - Start with some applicative style of constant streams
-- - Show an integral using hold
-- - Show a rising edge detector using hold and drop, as in
--     and (not stream) (drop stream)
--

type Streamwise n t = forall f g . Expr (Stream.ExprF Point.ExprF g) f ('Stream n t)

-- NB: for these constant streams we do not choose a particular index on their
-- prefix size. It's not clear whether we can get away with using Haskell's
-- universal quantification to get quantification in the object language...
-- should maybe look into that later, but for now, each constant stream must
-- be given a particular explicit prefix size (but it can be anything).

constant_42 :: forall n . NatRep n -> Streamwise n Point.UInt8
constant_42 nrep = Stream.constant auto nrep (Point.uint8 42)

constant_true :: forall n . NatRep n -> Streamwise n Point.Boolean
constant_true nrep = Stream.constant auto nrep Point.true

mk_pair :: Fun (Expr Point.ExprF f) (Point.UInt8 :-> Point.Boolean :-> V (Point.Pair Point.UInt8 Point.Boolean))
mk_pair = fun $ \a -> fun $ \b -> val $ Point.pair auto auto a b

-- Here's an unfortunate thing: we have to give a NatRep in order to lift a
-- function over, but we want it to be forall n.
-- Solution could be to not use a typical Nat, but rather Nat with infinity.
-- This way we have
--   Inf for pure streams
--   Z for no-memory impure streams
--   S n for memory impure streams
constant_pair :: forall n . NatRep n -> Streamwise n (Point.Pair Point.UInt8 Point.Boolean)
constant_pair nrep = unval $ Stream.liftF nrep argsrep mk_pair
  `at` constant_42 nrep `at` constant_true nrep
  where
  argsrep = Arg auto $ Arg auto $ Args

-- | Lifts (+) specialized to UInt8 over 2 streams. Analog of fmap (+) for
-- an applicative.
lifted_plus
  :: forall g f n .
     NatRep n
  -> Fun (Expr (Stream.ExprF Point.ExprF g) f)
     ('Stream n Point.UInt8 :-> 'Stream n Point.UInt8 :-> V ('Stream n Point.UInt8))
lifted_plus nrep = Stream.liftF nrep argsrep point_add
  where
  point_add = fun $ \a -> fun $ \b -> val $ Point.add auto a b
  argsrep = Arg auto $ Arg auto $ Args

-- | The integral of constant_42 (yes it's in UInt8 and will overflow fast but
-- whatever). This is a stream with memory (1 cell). That makes sense: the
-- first value is known to be 0, and this memory is essential for the
-- definition. At any given point one can drop from the stream to get the
-- latest value, which will depend upon the latest value of constant_42.
--
-- Also notice how we can use `auto` for the natural number representations,
-- since giving the top level 'S 'Z is enough to infer them all.
mono_integral :: Streamwise ('S 'Z) Point.UInt8
mono_integral = Stream.memory auto auto (VCons (Point.uint8 0) VNil) $ \sums ->
  -- We have the stream of sums, seeded with the value 0. To get the next
  -- values in this stream, we want to add those very partial sums to the
  -- constant_42 stream. In order to do this lifted addition, both streams must
  -- have the same nat index, and in this case they already do: in the
  -- continuation of Stream.memory, the parameter (`sums` in this case) is
  -- given a memory index 1 less than it actually has, to ensure that circular
  -- definitions cannot happen (you can't drop the whole known memory segment).
  unval $ lifted_plus auto `at` constant_42 auto `at` sums

-- | Lifts (&&) over streams.
lifted_and
  :: forall g f n .
     NatRep n
  -> Fun (Expr (Stream.ExprF Point.ExprF g) f)
     ('Stream n Point.Boolean :-> 'Stream n Point.Boolean :-> V ('Stream n Point.Boolean))
lifted_and nrep = Stream.liftF nrep argsrep point_and
  where
  point_and = fun $ \a -> fun $ \b -> val $ Point.and a b
  argsrep = Arg auto $ Arg auto $ Args

lifted_not
  :: forall g f n .
     NatRep n
  -> Fun (Expr (Stream.ExprF Point.ExprF g) f)
     ('Stream n Point.Boolean :-> V ('Stream n Point.Boolean))
lifted_not nrep = Stream.liftF nrep argsrep point_not
  where
  point_not = fun $ \a -> val $ Point.not a
  argsrep = Arg auto Args

-- | A rising edge stream. Given a stream of boolean, this stream is true
-- whenever that stream changes from false to true.
--
-- It's defined by making a 1-cell memory stream that holds the previous
-- value, and starting with true. The rising edge is then defined as "NOT
-- the first value AND the second value".
--
-- Notice how shift and drop are both used, so that the memory stream can
-- be reconciled with itself.
--
-- Also, we can use `auto` for all of the natural number representations, since
-- the top-level signature is enough for GHC to figure it out.
rising_edge :: Streamwise 'Z Point.Boolean -> Streamwise 'Z Point.Boolean
rising_edge bs =
  -- Ideally it would look like this
  --   and <$> shift (not <$> mem) <*> drop 1 mem
  unval $ lifted_and auto `at` Stream.shift auto auto (unval $ lifted_not auto `at` mem)
                          `at` Stream.drop  auto auto mem
  where
  mem = Stream.memory auto auto (VCons Point.true VNil) $ \_ -> bs

-- |
-- = Examples of lifted pointwise expressions
--
-- Orphans could be avoided by defining these in the module where Point.Type
-- is defined. Embed instances for application-specific data types would be
-- defined where those types are defined.

instance Embed Point.Type Haskell.Word8 where
  type EmbedT Point.Type Haskell.Word8 = Point.UInt8
  embedT _ _ = Point.uint8_t

instance Embed Point.Type Haskell.Int8 where
  type EmbedT Point.Type Haskell.Int8 = Point.Int8
  embedT _ _ = Point.int8_t

uint8 :: Haskell.Word8 -> Lifted Point.ExprF f Haskell.Word8
uint8 = lift . Point.uint8

int8 :: Haskell.Int8 -> Lifted Point.ExprF f Haskell.Int8
int8 = lift . Point.int8

instance Embed Point.Type () where
  type EmbedT Point.Type () = Point.Unit
  embedT _ _ = Point.unit_t

unit :: Lifted Point.ExprF f ()
unit = lift Point.unit

instance Embed Point.Type Bool where
  type EmbedT Point.Type Bool = Point.Boolean
  embedT _ _ = Point.boolean_t

true :: Lifted Point.ExprF f Bool
true = lift Point.true

false :: Lifted Point.ExprF f Bool
false = lift Point.false

if_else
  :: forall f r .
     (Embed Point.Type r)
  => Lifted Point.ExprF f Bool
  -> Lifted Point.ExprF f r
  -> Lifted Point.ExprF f r
  -> Lifted Point.ExprF f r
if_else vb cTrue cFalse = lift $ Point.if_else
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift vb)
  (unlift cTrue)
  (unlift cFalse)

instance Embed Point.Type t => Embed Point.Type (Prelude.Maybe t) where
  type EmbedT Point.Type (Prelude.Maybe t) = Point.Maybe (EmbedT Point.Type t)
  embedT _ _ = Point.maybe_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

nothing
  :: forall f t .
     ( Embed Point.Type t )
  => Lifted Point.ExprF f (Prelude.Maybe t)
nothing = lift $ Point.nothing
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

just
  :: forall f t .
     ( Embed Point.Type t )
  => Lifted Point.ExprF f t
  -> Lifted Point.ExprF f (Prelude.Maybe t)
just vt = lift $ Point.just
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (unlift vt)

maybe
  :: forall f t r .
     ( Embed Point.Type t, Embed Point.Type r )
  => Lifted Point.ExprF f (Prelude.Maybe t)
  -> Lifted Point.ExprF f r
  -> (Lifted Point.ExprF f t -> Lifted Point.ExprF f r)
  -> Lifted Point.ExprF f r
maybe mx cNothing cJust = lift $ Point.elim_maybe
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift mx)
  (const (unlift cNothing))
  (unlift . cJust . lift)

instance (Embed Point.Type s, Embed Point.Type t) => Embed Point.Type (s, t) where
  type EmbedT Point.Type (s, t) = Point.Pair (EmbedT Point.Type s) (EmbedT Point.Type t)
  embedT _ _ = Point.pair_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy s))
                            (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

pair
  :: forall f a b .
     ( Embed Point.Type a, Embed Point.Type b )
  => Lifted Point.ExprF f a
  -> Lifted Point.ExprF f b
  -> Lifted Point.ExprF f (a, b)
pair ea eb = lift $ Point.pair arep brep (unlift ea) (unlift eb)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

fst
  :: forall f a b .
     ( Embed Point.Type a, Embed Point.Type b )
  => Lifted Point.ExprF f (a, b)
  -> Lifted Point.ExprF f a
fst p = lift $ Point.fst arep brep (unlift p)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

-- | Suppose we wanted a custom enum like this
--
--   data MyEnum = A | B | C | D
--
-- We would just define a new nominal type and then give the representation in
-- the Embed instance.
data ApplicationSpecificType

instance Embed Point.Type ApplicationSpecificType where
  -- The embedding is defined by way the embedding of (). We could just as well
  -- have used Point.Unit instead but this shows how a more complex thing might
  -- be defined.
  type EmbedT Point.Type ApplicationSpecificType = 'Sum
    '[ EmbedT Point.Type ()   -- A
     , EmbedT Point.Type ()   -- B
     , EmbedT Point.Type ()   -- C
     , EmbedT Point.Type () ] -- D
  embedT _ _ = Point.Sum_t (And urep $ And urep $ And urep $ And urep $ All)
    where
    urep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ())

variant_A :: Lifted Point.ExprF f ApplicationSpecificType
variant_A = lift $ Point.exprF $ \interp -> Point.IntroSum trep Point.unit_t
  (Any Selector) (interp Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_B :: Lifted Point.ExprF f ApplicationSpecificType
variant_B = lift $ Point.exprF $ \interp -> Point.IntroSum trep Point.unit_t
  (Or $ Any Selector) (interp Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_C :: Lifted Point.ExprF f ApplicationSpecificType
variant_C = lift $ Point.exprF $ \interp -> Point.IntroSum trep Point.unit_t
  (Or $ Or $ Any Selector) (interp Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_D :: Lifted Point.ExprF f ApplicationSpecificType
variant_D = lift $ Point.exprF $ \interp -> Point.IntroSum trep Point.unit_t
  (Or $ Or $ Or $ Any Selector) (interp Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

-- | Case match to eliminate an ApplicationSpecificType
variant
  :: forall f r .
     ( Embed Point.Type r )
  => Lifted Point.ExprF f ApplicationSpecificType
  -> Lifted Point.ExprF f r -- if A
  -> Lifted Point.ExprF f r -- if B
  -> Lifted Point.ExprF f r -- if C
  -> Lifted Point.ExprF f r -- if D
  -> Lifted Point.ExprF f r
variant vv cA cB cC cD = lift $ Point.exprF $ \interp -> Point.ElimSum srep rrep
  (And (Case urep (const (interp (unlift cA)))) $
   And (Case urep (const (interp (unlift cB)))) $
   And (Case urep (const (interp (unlift cC)))) $
   And (Case urep (const (interp (unlift cD)))) $
   All)
  (interp (unlift vv))
  where
  -- The lower-level representation requires type annotations everywhere, but
  -- we can just grab those from the embed instances.
  srep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)
  rrep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r)
  urep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ())

{-
write_lifted :: String -> Lifted ExprF C.CodeGen C.Val s x -> IO ()
write_lifted fpath = C.write_example fpath . unlift
-}
