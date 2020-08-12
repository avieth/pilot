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
{-# LANGUAGE RebindableSyntax #-}

module Examples where

import Prelude hiding ((>>=), (>>))
import Pilot.EDSL.Expr.Bind

import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Pilot.EDSL.Point
import qualified Pilot.EDSL.Point as Point
import Pilot.EDSL.Stream
import qualified Pilot.EDSL.Stream as Stream
import Pilot.EDSL.Lifted
import Pilot.Types.Fun
import Pilot.Types.Logic
import Pilot.Types.Nat
import Pilot.Types.Represented

import Pilot.Interp.Exec
import qualified Pilot.Interp.Pure as Pure (Point)
import qualified Pilot.Interp.C as C

-- (42, -42) :: (UInt8, Int8)
example_1 :: Expr Point.ExprF f (Pair UInt8 Int8)
example_1 = Point.pair uint8_t int8_t (Point.uint8 42) (Point.int8 (-42))

-- Right (-42) :: Either (UInt8, Int8)
--
-- Shows how we can use `auto` to fill in type information for the variants.
-- The top-level type signature ensures that GHC can figure it out (everything
-- is a known monotype).
example_2 :: Expr Point.ExprF f (Point.Either UInt8 Int8)
example_2 = Point.right auto auto (Point.int8 (-42))

-- Just (-42) :: Maybe Int8
example_3 :: Expr Point.ExprF f (Point.Maybe Int8)
example_3 = Point.just auto (Point.int8 (-42))

-- case example_3 of
--   Nothing -> -1
--   Just t  -> t
example_4 :: Expr Point.ExprF f Int8
example_4 = elim_maybe auto auto example_3
  (\_ -> Point.int8 (-1))
  (\t -> t)

-- case example_2 of
--   Left  -> -1
--   Right -> 2
example_4_1 :: Expr Point.ExprF f Int8
example_4_1 = elim_either uint8_t int8_t int8_t example_2
  (\_ -> Point.int8 (-1))
  (\_ -> Point.int8 2)

-- fst example_1
example_5 :: Expr Point.ExprF f UInt8
example_5 = Point.fst auto auto example_1

-- 2 + 2
example_6 :: Expr Point.ExprF f UInt8
example_6 = Point.add auto (Point.uint8 2) (Point.uint8 2)

-- example_6 + example_5
-- = (2 + 2) + fst example_1
-- = (2 + 2) + fst (42, -42)
example_7 :: Expr Point.ExprF f UInt8
example_7 = Point.add auto example_6 example_5

example_8 :: Expr Point.ExprF f UInt8
example_8 = Point.add auto (Point.fst auto auto example_1) example_6

-- Expressions can of course be constructed with Haskell where/let bindings...
example_9 :: Expr Point.ExprF f UInt8
example_9 = notB auto f
  where
  a = Point.uint8 0
  b = Point.uint8 1
  c = Point.uint8 2
  d = Point.add auto a b
  e = Point.add auto d c
  f = Point.shiftR auto e a
  -- The above is
  --   ~(((0 + 1) + 2) >> 0)
  -- i.e. ~3 in 8 bits, or 252 in decimal.

-- ... but they may also be constructed with "object-language" let bindings.
--
-- A Monad constraint appears on the interpreter because it must come up with
-- a name and be flexible enough to do substitution.
--
-- NB: the Haskell let binding does not actually appear in the object-language,
-- but the `local` induces a name/subst structure that _may_ appear in the
-- object-language (depending on the interpreter).
example_10 :: Expr Point.ExprF f UInt8
example_10 = local example_9 $ \x ->
  let y = Point.uint8 42
  in  Point.orB auto x y

-- We can also use a monadic style for bindings, but NB: this is not actually
-- a monad, it's just rebindable syntax. It's not clear whether this is a good
-- idea at all, but some people may find it makes things more readable.
--
-- This one is equivalent to
--
--   example_11 =
--     local example_9 $ \x ->
--     local (Point.orB auto x (Point.uint8 42)) $ \y ->
--       Point.cmp auto auto x y lt eq gt
--
example_11 :: Expr Point.ExprF f Point.Ordering
example_11 = do
  x <- example_9
  y <- Point.orB auto x (Point.uint8 42)
  Point.cmp auto auto x y lt eq gt

-- | Contains a nested product in a sum.
example_12 :: Expr Point.ExprF f UInt8
example_12 = do
  p <- example_1
  s <- Point.just auto p
  elim_maybe auto auto s
    (\_ -> Point.uint8 1)
    (\x -> Point.fst auto auto x)

-- | Monadic bind for maybe.
maybe_bind
  :: forall val s t .
     Point.TypeRep s
  -> Point.TypeRep t
  -> Expr Point.ExprF val (Point.Maybe s)
  -> (Expr Point.ExprF val s -> Expr Point.ExprF val (Point.Maybe t))
  -> Expr Point.ExprF val (Point.Maybe t)
maybe_bind srep trep mx k = Point.elim_maybe srep (Point.maybe_t trep) mx
  (\_ -> Point.nothing trep)
  k

-- The type variables represent what we know about the point, static, and
-- stream _interpreter_ values respectively.
type StreamExpr constf staticf streamf = Expr
  (Stream.ExprF
    (Expr Point.ExprF constf)
    (Expr Point.ExprF staticf)
  )
  streamf

-- example_13 and example_14 show how to crate constant streams from points.
-- Any prefix size index can be chosen.

example_13 :: NatRep n -> StreamExpr cf sf f ('Prefix n UInt8)
example_13 nrep = Stream.constant auto nrep example_12

example_14 :: StreamExpr cf sf f ('Prefix 'Z (Pair UInt8 Int8))
example_14 = Stream.constant auto auto p
  where
  p = Point.pair auto auto d e
  a = Point.uint8 1
  b = Point.int8 2
  c = Point.uint8 3
  d = Point.add auto a c
  e = Point.mul auto b b

-- We could also do example_14 with binders in the point expression.
-- Notice that we use Haskell let/where bindings for a b and c, but we use
-- a different notion of binding for d and e: it's not recursive (imposes an
-- ordering) and the interpreter may actually observe and use it.

example_14_1 :: StreamExpr cf sf f ('Prefix 'Z (Pair UInt8 Int8))
example_14_1 = Stream.constant auto auto $ 
  local (Point.add auto a c) $ \d ->
  local (Point.mul auto b b) $ \e ->
    Point.pair auto auto d e
  where
  a = Point.uint8 1
  b = Point.int8  2
  c = Point.uint8 3

-- The same as example_14_1 but we use the rebindable syntax do notation, to
-- show how it may look when nested within a stream expression. It also works
-- for streams directly, but that isn't shown here.
example_14_2 :: StreamExpr cf sf f ('Prefix 'Z (Pair UInt8 Int8))
example_14_2 = Stream.constant auto auto $ do
  d <- Point.add auto a c
  e <- Point.mul auto b b
  Point.pair auto auto d e
  where
  a = Point.uint8 1
  b = Point.int8  2
  c = Point.uint8 3

-- A memory stream. This one is just the value of example_12 forever.
--
-- You wouldn't actually do it this way, because Stream.constant can be used
-- to make example_12 into a stream of any prefix size.
--
-- Note that a constraint on sf appears, since the vector of initial values
-- uses the static value and interpreter parameters. The Monad constraint
-- therefore comes from example_12.
example_15 :: StreamExpr cf sf f ('Prefix ('S 'Z) UInt8)
example_15 = Stream.memory auto auto inits $ \_ ->
  -- The _ parameter is the resulting stream, so that we can make 
  Stream.constant auto auto example_12

  where

  inits :: forall f . Vec ('S 'Z) (Expr Point.ExprF f UInt8)
  inits = VCons example_12 VNil

-- The flagship example: define an integral using a memory stream of prefix
-- size 1 and a lifted pointwise function.
integral
  :: forall cf sf f .
     Expr Point.ExprF sf Int32
  -> StreamExpr cf sf f ('Prefix 'Z Int32)
  -> StreamExpr cf sf f ('Prefix ('S 'Z) Int32)
integral c f = Stream.memory auto auto (VCons c VNil) $ \sums ->
  -- Here `sums` is the stream itself, but with a prefix of size zero (one less
  -- than the prefix) so that only values which have already been computed may
  -- be used.
  unlit $ Stream.liftF autoArgs auto auto plus `at` f `at` sums
  where
  plus :: Fun (Expr Point.ExprF cf) (Int32 :-> Int32 :-> V Int32)
  plus = fun $ \a -> fun $ \b -> lit $ Point.add auto a b

-- The integral of constant 3.
example_16 :: StreamExpr cf sf f ('Prefix ('S 'Z) Int32)
example_16 = integral c f

  where

  -- Type signatures are not needed, but are here for illustration.

  c :: Expr Point.ExprF f Int32
  c = Point.int32 0

  f :: StreamExpr cf sf f ('Prefix 'Z Int32)
  f = Stream.constant auto auto (Point.int32 3)

-- Here are some examples of integrating a particular interpreter, namely the
-- C backend. This shows how we introduce the 'Exec' type and things become
-- monadic, because when it comes to C, we actually do require an ordering and
-- some benign side effects, in ordert to declare externs for example.
--
-- Uses Stream.drop so that the value of the integral returned is
-- the latest, not the most recent sum.
--
-- Note the clever (abusive? evil?) overloading of do notation: it still works
-- here for Exec which is a typical Haskell monad.
example_17
  :: Exec (Expr (Stream.ExprF (Expr Point.ExprF (C.Point s)) (Expr Point.ExprF Pure.Point)))
          (C.Stream s)
          (C.CodeGen s)
          (C.Stream s ('Prefix 'Z Int32))
example_17 = do
  i <- C.externInput "input" Point.int32_t
  o <- expr (Stream.drop auto auto (integral (Point.int32 0) (value i)))
  C.externOutput "output" o
  expr (value o)

-- To define the rising edge of a boolean stream, we first define a stream which
-- gives the last value of that stream, then we take the exclusive or where
-- the older one is false.
rising_edge
  :: forall cval sval val .
     StreamExpr cval sval val ('Prefix 'Z Boolean)
  -> StreamExpr cval sval val ('Prefix 'Z Boolean)
rising_edge bs = do
  ms <- Stream.memory auto auto inits $ \_ -> bs
  -- We have to "shift" the stream to match the nat indices. What we get is
  -- a stream bs' which at any instant is the value of bs at the last instant.
  let bs' = Stream.shift auto auto ms
      f = fun $ \x -> fun $ \y -> lit (Point.and (Point.not x) y)
  unlit $ Stream.liftF autoArgs auto auto f `at` bs' `at` bs
  where
  inits = VCons Point.false VNil

example_18 :: StreamExpr cval sval val ('Prefix 'Z Boolean)
-- NB: if local is not used here, the memory stream in `signal` will be
-- duplicated by `rising_edge`. You'll get the same results but the C program
-- will take twice as much space and time.
-- This is unfortunate, but I'm not sure how to do it better.
example_18 = local signal rising_edge
  where

  -- To use our signal on rising edge, we have to make its prefix 'Z. We do
  -- that by "shifting" rather than "dropping". This means the prefix values
  -- all remain but appear closer to the suffix.
  signal :: StreamExpr cval sval val ('Prefix 'Z Boolean)
  signal =
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.shift auto auto $
    Stream.memory auto auto inits $ \_ -> Stream.constant auto auto Point.true

  -- The type signature for this is tedious to write, but GHC can infer it.
  --
  --inits :: Vec <some long Nat type> (Expr Point.ExprF val f Boolean)
  inits =
    VCons Point.true  $
    VCons Point.true  $
    VCons Point.false $
    VCons Point.false $
    VCons Point.true  $
    VCons Point.true  $
    VCons Point.true  $
    VCons Point.false $
    VCons Point.true  $
    VCons Point.false $
    VNil

example_19
  :: Exec (Expr (Stream.ExprF (Expr Point.ExprF (C.Point s)) (Expr Point.ExprF Pure.Point)))
          (C.Stream s)
          (C.CodeGen s)
          (C.Stream s ('Prefix 'Z Unit))
example_19 = do
  -- Use the C backend to get inputs.
  inputA <- C.externInput "inputA" (Point.maybe_t Point.int32_t)
  inputB <- C.externInput "inputB" (Point.maybe_t Point.int32_t)
  inputC <- C.externInput "inputC" (Point.maybe_t Point.int32_t)
  -- Apply a pointwise function over those inputs.
  ret <- expr (ap f <@> arg (value inputA) <&> arg (value inputB) <&> arg (value inputC))
  () <- C.externOutput "output" ret
  expr $ Stream.constant auto auto Point.unit
  where

  -- TODO can we use overloaded do notation even here?
  -- Would require using the "lifted" notion, so that we could define the
  -- monad on the Maybe proxy type (structurally, we can have different monads
  -- for the same structure).
  -- More generally: can we get an overloaded, poly-kinded
  -- Functor/Applicative/Monad stack, so that in a single module we could use
  -- typical Hask do notation but also use do, <$>, <*> etc. inside a lifted
  -- Expr context?
  f = fun $ \mx -> fun $ \my -> fun $ \mz -> lit $
        maybe_bind auto auto mx $ \x ->
        maybe_bind auto auto my $ \y ->
        maybe_bind auto auto mz $ \z -> Point.just auto $
          Point.add auto x (Point.add auto y z)

-- | Use a memory stream to make a counter with some modulus.
--
-- That modulus can be varying, but should probably be constant or you may
-- get some really hard to understand behaviour.
--
-- TODO see if we can make it polymorphic over integral types.
counter
  :: Expr Point.ExprF sval Point.UInt32
  -> StreamExpr cval sval val ('Prefix 'Z Point.UInt32)
  -> StreamExpr cval sval val ('Prefix 'Z Point.UInt32)
counter initial modulus = Stream.shift auto auto $ Stream.memory auto auto inits $ \self ->
  ap incrModulo <@> arg self <&> arg modulus
  where
  inits = VCons initial VNil

  incrModulo :: Fun (Expr Point.ExprF sval)
    (Point.UInt32 :-> Point.UInt32 :-> V Point.UInt32)
  incrModulo = fun $ \x -> fun $ \m -> lit $
    Point.mod auto (Point.add auto (Point.uint32 1) x) m

-- | Use 'counter' to generate a clock with a given phase and period.
--
-- It will be true once every period, and the phase determines on which tick
-- it will be true.
--
-- If the phase is n, it will be true on the n+1th tick of the phase. If the
-- phase is greater than or equal to the period, it will never be true, unless
-- the period is 0.
--
-- Here's a plain language overview of how it's done:
-- 1. Define the counter using the period as its modulus and 0 as its inital
--    value.
-- 2. Define a first-order function over points which compares some point to
--    the phase and gives true if they are equal.
-- 3. Lift that function over the counter stream.
clock
  :: forall cval sval val .
     Expr Point.ExprF cval Point.UInt32 -- ^ Period
  -> Expr Point.ExprF cval Point.UInt32 -- ^ Phase
  -> StreamExpr cval sval val ('Prefix 'Z Boolean)
clock period phase = unlit $ Stream.liftF autoArgs auto auto f `at` cnt

  where

  f :: Fun (Expr Point.ExprF cval) (Point.UInt32 :-> V Point.Boolean)
  f = fun $ \x -> lit $ cmp auto auto x phase
        Point.false -- If LT
        Point.true  -- If EQ
        Point.false -- If GT

  cnt = counter (Point.uint32 0) (Stream.constant auto auto period)

-- |
-- = Examples of lifted pointwise expressions
--
-- Orphans could be avoided by defining these in the module where Point.Type
-- is defined. Embed instances for application-specific data types would be
-- defined where those types are defined.

data Period
data Phase

instance Embed Point.Type Period where
  type EmbedT Point.Type Period = Point.UInt32
  embedT _ _ = Point.uint32_t

instance Embed Point.Type Phase where
  type EmbedT Point.Type Phase = Point.UInt32
  embedT _ _ = Point.uint32_t

clock_lifted
  :: forall cval sval val .
     Lifted (Expr Point.ExprF cval) Period
  -> Lifted (Expr Point.ExprF cval) Phase
  -> StreamExpr cval sval val ('Prefix 'Z Boolean)
clock_lifted period phase = clock (unlift period) (unlift phase)

instance Embed Point.Type Haskell.Word8 where
  type EmbedT Point.Type Haskell.Word8 = Point.UInt8
  embedT _ _ = Point.uint8_t

instance Embed Point.Type Haskell.Int8 where
  type EmbedT Point.Type Haskell.Int8 = Point.Int8
  embedT _ _ = Point.int8_t

uint8 :: Haskell.Word8 -> Lifted (Expr Point.ExprF f) Haskell.Word8
uint8 = lift . Point.uint8

int8 :: Haskell.Int8 -> Lifted (Expr Point.ExprF f) Haskell.Int8
int8 = lift . Point.int8

instance Embed Point.Type () where
  type EmbedT Point.Type () = Point.Unit
  embedT _ _ = Point.unit_t

unit :: Lifted (Expr Point.ExprF f) ()
unit = lift Point.unit

instance Embed Point.Type Bool where
  type EmbedT Point.Type Bool = Point.Boolean
  embedT _ _ = Point.boolean_t

true :: Lifted (Expr Point.ExprF f) Bool
true = lift Point.true

false :: Lifted (Expr Point.ExprF f) Bool
false = lift Point.false

if_else
  :: forall f r .
     (Embed Point.Type r)
  => Lifted (Expr Point.ExprF f) Bool
  -> Lifted (Expr Point.ExprF f) r
  -> Lifted (Expr Point.ExprF f) r
  -> Lifted (Expr Point.ExprF f) r
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
     (Embed Point.Type t)
  => Lifted (Expr Point.ExprF f) (Prelude.Maybe t)
nothing = lift $ Point.nothing
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

just
  :: forall f t .
     (Embed Point.Type t)
  => Lifted (Expr Point.ExprF f) t
  -> Lifted (Expr Point.ExprF f) (Prelude.Maybe t)
just vt = lift $ Point.just
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (unlift vt)

maybe
  :: forall f t r .
     (Embed Point.Type t, Embed Point.Type r)
  => Lifted (Expr Point.ExprF f) (Prelude.Maybe t)
  -> Lifted (Expr Point.ExprF f) r
  -> (Lifted (Expr Point.ExprF f) t -> Lifted (Expr Point.ExprF f) r)
  -> Lifted (Expr Point.ExprF f) r
maybe mx cNothing cJust = lift $ Point.elim_maybe
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift mx)
  (const (unlift cNothing))
  (unlift . cJust . lift)

-- | Monadic bind for Maybe.
maybe_bind_lifted
  :: forall f s t .
     (Embed Point.Type s, Embed Point.Type t)
  => Lifted (Expr Point.ExprF f) (Prelude.Maybe s)
  -> (Lifted (Expr Point.ExprF f) s -> Lifted (Expr Point.ExprF f) (Prelude.Maybe t))
  -> Lifted (Expr Point.ExprF f) (Prelude.Maybe t)
maybe_bind_lifted mx k = lift $ Point.elim_maybe
  srep
  mrep
  (unlift mx)
  (\_ -> Point.nothing trep)
  (unlift . k . lift)
  where
  srep :: Point.TypeRep (EmbedT Point.Type s)
  srep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy s)
  mrep :: Point.TypeRep (EmbedT Point.Type (Prelude.Maybe t))
  mrep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy (Prelude.Maybe t))
  trep :: Point.TypeRep (EmbedT Point.Type t)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t)

instance (Embed Point.Type s, Embed Point.Type t) => Embed Point.Type (s, t) where
  type EmbedT Point.Type (s, t) = Point.Pair (EmbedT Point.Type s) (EmbedT Point.Type t)
  embedT _ _ = Point.pair_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy s))
                            (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

pair
  :: forall f a b .
     (Embed Point.Type a, Embed Point.Type b)
  => Lifted (Expr Point.ExprF f) a
  -> Lifted (Expr Point.ExprF f) b
  -> Lifted (Expr Point.ExprF f) (a, b)
pair ea eb = lift $ Point.pair arep brep (unlift ea) (unlift eb)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

fst
  :: forall f a b .
     (Embed Point.Type a, Embed Point.Type b)
  => Lifted (Expr Point.ExprF f) (a, b)
  -> Lifted (Expr Point.ExprF f) a
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

variant_A :: Lifted (Expr Point.ExprF f) ApplicationSpecificType
variant_A = lift $ edsl $ Point.IntroSum trep
  (Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_B :: Lifted (Expr Point.ExprF f) ApplicationSpecificType
variant_B = lift $ edsl $ Point.IntroSum trep
  (Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_C :: Lifted (Expr Point.ExprF f) ApplicationSpecificType
variant_C = lift $ edsl $ Point.IntroSum trep
  (Or $ Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_D :: Lifted (Expr Point.ExprF f) ApplicationSpecificType
variant_D = lift $ edsl $ Point.IntroSum trep
  (Or $ Or $ Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

-- | Case match to eliminate an ApplicationSpecificType
case_variant
  :: forall f r .
     (Embed Point.Type r)
  => Lifted (Expr Point.ExprF f) ApplicationSpecificType
  -> Lifted (Expr Point.ExprF f) r -- if A
  -> Lifted (Expr Point.ExprF f) r -- if B
  -> Lifted (Expr Point.ExprF f) r -- if C
  -> Lifted (Expr Point.ExprF f) r -- if D
  -> Lifted (Expr Point.ExprF f) r
case_variant vv cA cB cC cD = lift $ edsl $ Point.ElimSum srep rrep
  (unlift vv)
  (And (Case urep (const (unlift cA))) $
   And (Case urep (const (unlift cB))) $
   And (Case urep (const (unlift cC))) $
   And (Case urep (const (unlift cD))) $
   All)
  where
  -- The lower-level representation requires type annotations everywhere, but
  -- we can just grab those from the embed instances.
  srep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)
  rrep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r)
  urep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ())
