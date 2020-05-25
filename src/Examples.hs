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
import Pilot.EDSL.Point
import qualified Pilot.EDSL.Point as Point
import Pilot.EDSL.Stream
import qualified Pilot.EDSL.Stream as Stream
import Pilot.EDSL.Lifted
import Pilot.Types.Fun
import Pilot.Types.Nat
import Pilot.Types.Represented

-- (42, -42) :: (UInt8, Int8)
example_1 :: Expr Point.ExprF expr f (Pair UInt8 Int8)
example_1 = Point.pair uint8_t int8_t (Point.uint8 42) (Point.int8 (-42))

-- Right (-42) :: Either (UInt8, Int8)
--
-- Shows how we can use `auto` to fill in type information for the variants.
-- The top-level type signature ensures that GHC can figure it out (everything
-- is a known monotype).
example_2 :: Expr Point.ExprF expr f (Point.Either UInt8 Int8)
example_2 = Point.right auto auto (Point.int8 (-42))

-- Just (-42) :: Maybe Int8
example_3 :: Expr Point.ExprF expr f (Point.Maybe Int8)
example_3 = Point.just auto (Point.int8 (-42))


-- NB: even for simple pointwise expressions there is really a difference
-- between it and a value that we need to maintain
--   let y = let x = 2 in x + x
--   in  y + y
-- would make 2 bindings to 2, one for each of the y terms in the outer sum.
--   y <- let x = 2 in x + x
--   y + y
-- would only make 1 binding to 2. The value y would be x + x and we'd get
--   (x + x) + (x + x)
-- as opposed to
--   x0 = 2
--   x1 = 2
--   (x0 + x0) + (x1 + x1)
--
-- So, remember why we wanted to bring back the notion of `val`? The memory
-- stream: 
--
--   a <- cosntant ...
--   y <- memory [a] as
--
-- here y is fundamentally different from `memory [a] as`. 
--
--

-- case example_3 of
--   Nothing -> -1
--   Just t  -> t
example_4 :: Expr Point.ExprF expr f Int8
example_4 = elim_maybe auto auto example_3
  (\_ -> Point.int8 (-1))
  (\t -> t)

-- case example_2 of
--   Left  -> -1
--   Right -> 2
example_4_1 :: Expr Point.ExprF expr f Int8
example_4_1 = elim_either uint8_t int8_t int8_t example_2
  (\_ -> Point.int8 (-1))
  (\_ -> Point.int8 2)

-- fst example_1
example_5 :: Expr Point.ExprF expr f UInt8
example_5 = Point.fst auto auto example_1

-- 2 + 2
example_6 :: Expr Point.ExprF expr f UInt8
example_6 = Point.add auto (Point.uint8 2) (Point.uint8 2)

-- example_6 + example_5
-- = (2 + 2) + fst example_1
-- = (2 + 2) + fst (42, -42)
example_7 :: Expr Point.ExprF expr f UInt8
example_7 = Point.add auto example_6 example_5

example_8 :: Expr Point.ExprF expr f UInt8
example_8 = Point.add auto (Point.fst auto auto example_1) example_6

-- Expressions can of course be constructed with Haskell where/let bindings...
example_9 :: Expr Point.ExprF val f UInt8
example_9 = notB auto f
  where
  a = Point.uint8 0
  b = Point.uint8 1
  c = Point.uint8 2
  d = Point.add auto a b
  e = Point.add auto d c
  f = Point.shiftR auto e a

-- ... but they may also be constructed with "object-language" let bindings.
--
-- A Monad constraint appears on the interpreter because it must come up with
-- a name and be flexible enough to do substitution.
--
-- NB: the Haskell let binding does not actually appear in the object-language,
-- but the `local` induces a name/subst structure that _may_ appear in the
-- object-language (depending on the interpreter).
example_10 :: Monad f => Expr Point.ExprF val f UInt8
example_10 = local example_9 $ \x ->
  let y = Point.uint8 42
  in  Point.orB auto x y

-- We can also use a monadic style to do bindings (`local` uses this in its
-- definition). Since `Expr` does not have the _kind_ of a Haskell monad, we
-- use `ExprM` instead.
example_11 :: Monad f => Expr Point.ExprF val f Point.Ordering
example_11 = Expr $ do
  x <- bind example_9
  y <- bind $ Point.orB auto x (Point.uint8 42)
  expr $ Point.cmp auto auto x y lt eq gt

-- | Contains a nested product in a sum.
example_12 :: Monad f => Expr Point.ExprF val f UInt8
example_12 = Expr $ do
  p <- bind $ example_1
  s <- bind $ Point.just auto p
  expr $ elim_maybe auto auto s
    (\_ -> Point.uint8 1)
    (\x -> Point.fst auto auto x)

-- It should suffice here to make a type that is point expressions _free in
-- val_, no?
-- Concern is that, if it's free in val, it must be free in f, but will we
-- always be free in f? What if the point uses some interpreter specific stuff?
-- We should still be able to use it in a stream which uses the same interpreter.
--
-- Think about what the type will be in the interpreter type signature for C
--
--   eval_point
--     :: Point.ExprF (Expr Point.ExprF (Compose Val 'Point) CodeGen) x
--     -> CodeGen (Compose Val 'Point x)
--
--   eval_stream
--     :: Stream.ExprF ? (Expr (Stream.ExprF ?) Val CodeGen) x
--     -> CodeGen (Val x)
--
--
-- Well... just let them be different?


example_13 :: (Monad f) => Expr (Stream.ExprF (Expr Point.ExprF pval f)) val f ('Constant UInt8)
example_13 = Stream.point uint8_t example_12

type StreamExpr pval val f = Expr (Stream.ExprF (Expr Point.ExprF pval f)) val f

-- Here a point is expressed and then "lifted" into a stream of a given
-- prefix size (zero).
example_14 :: (Monad f) => StreamExpr pval val f ('Stream 'Z (Pair UInt8 Int8))
example_14 = Stream.constant auto auto p
  where
  p = Stream.point auto $ Point.pair auto auto d e
  a = Point.uint8 1
  b = Point.int8 2
  c = Point.uint8 3
  d = Point.add auto a c
  e = Point.mul auto b b

-- A memory stream. This one is just the value of example_13 forever.
-- You wouldn't actually do it this way, because Steram.constant can be used
-- to make example_13 into a stream of any prefix size.
example_15 :: (Monad f) => StreamExpr pval val f ('Stream ('S 'Z) UInt8)
example_15 = Stream.memory auto auto inits $ \_ ->
  Stream.constant auto auto example_13
  where
  inits :: (Monad f) => Vec ('S 'Z) (StreamExpr pval val f ('Constant UInt8))
  inits = VCons example_13 VNil

-- The flagship example: define an integral using a memory stream of prefix
-- size 1 and a lifted pointwise function.
integral
  :: forall pval val f .
     (Monad f)
  => StreamExpr pval val f ('Constant Int32)
  -> StreamExpr pval val f ('Stream 'Z Int32)
  -> StreamExpr pval val f ('Stream ('S 'Z) Int32)
integral c f = Stream.memory auto auto (VCons c VNil) $ \sums ->
  -- Here `sums` is the stream itself, but with a prefix of size zero (one less
  -- than the prefix) so that only values which have already been computed may
  -- be used.
  unlit $ Stream.liftF autoArgs auto auto plus `at` f `at` sums
  where
  plus :: Fun (Expr Point.ExprF pval f) (Int32 :-> Int32 :-> V Int32)
  plus = fun $ \a -> fun $ \b -> lit $ Point.add auto a b

example_16 :: (Monad f) => StreamExpr pval val f ('Stream ('S 'Z) Int32)
example_16 = integral c f
  where
  c :: (Monad f) => StreamExpr pval val f ('Constant Int32)
  c = Stream.point auto (Point.int32 0)
  f :: (Monad f) => StreamExpr pval val f ('Stream 'Z Int32)
  f = Stream.constant auto auto (Stream.point auto (Point.int32 3))

-- |
-- = Examples of streamwise expressions
--
-- TODO some examples of streams and lifting.
-- - Show a rising edge detector using hold and drop, as in
--     and (not stream) (drop stream)
--

-- To define the rising edge of a boolean stream, we first define a stream which
-- gives the last value of that stream, then we take the exclusive or where
-- the older one is false.
rising_edge
  :: forall pval val f .
     (Monad f)
  => StreamExpr pval val f ('Stream 'Z Boolean)
  -> StreamExpr pval val f ('Stream 'Z Boolean)
rising_edge bs = Expr $ do
  ms <- bind $ Stream.memory auto auto inits $ \_ -> bs
  -- We have to "shift" the stream to match the nat indices. What we get is
  -- a stream bs' which at any instant is the value of bs at the last instant.
  let bs' = Stream.shift auto auto ms
      f = fun $ \x -> fun $ \y -> lit (Point.and (Point.not x) y)
  expr $ unlit $ Stream.liftF autoArgs auto auto f `at` bs' `at` bs
  where
  inits = VCons (Stream.point auto Point.false) VNil

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

uint8 :: Haskell.Word8 -> Lifted (Expr Point.ExprF val f) Haskell.Word8
uint8 = lift . Point.uint8

int8 :: Haskell.Int8 -> Lifted (Expr Point.ExprF val f) Haskell.Int8
int8 = lift . Point.int8

instance Embed Point.Type () where
  type EmbedT Point.Type () = Point.Unit
  embedT _ _ = Point.unit_t

unit :: Lifted (Expr Point.ExprF val f) ()
unit = lift Point.unit

instance Embed Point.Type Bool where
  type EmbedT Point.Type Bool = Point.Boolean
  embedT _ _ = Point.boolean_t

true :: Lifted (Expr Point.ExprF val f) Bool
true = lift Point.true

false :: Lifted (Expr Point.ExprF val f) Bool
false = lift Point.false

if_else
  :: forall val f r .
     (Embed Point.Type r)
  => Lifted (Expr Point.ExprF val f) Bool
  -> Lifted (Expr Point.ExprF val f) r
  -> Lifted (Expr Point.ExprF val f) r
  -> Lifted (Expr Point.ExprF val f) r
if_else vb cTrue cFalse = lift $ Point.if_else
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift vb)
  (unlift cTrue)
  (unlift cFalse)

instance Embed Point.Type t => Embed Point.Type (Prelude.Maybe t) where
  type EmbedT Point.Type (Prelude.Maybe t) = Point.Maybe (EmbedT Point.Type t)
  embedT _ _ = Point.maybe_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

nothing
  :: forall val f t .
     (Embed Point.Type t)
  => Lifted (Expr Point.ExprF val f) (Prelude.Maybe t)
nothing = lift $ Point.nothing
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

just
  :: forall val f t .
     (Embed Point.Type t)
  => Lifted (Expr Point.ExprF val f) t
  -> Lifted (Expr Point.ExprF val f) (Prelude.Maybe t)
just vt = lift $ Point.just
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (unlift vt)

maybe
  :: forall val f t r .
     (Embed Point.Type t, Embed Point.Type r)
  => Lifted (Expr Point.ExprF val f) (Prelude.Maybe t)
  -> Lifted (Expr Point.ExprF val f) r
  -> (Lifted (Expr Point.ExprF val f) t -> Lifted (Expr Point.ExprF val f) r)
  -> Lifted (Expr Point.ExprF val f) r
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
  :: forall val f a b .
     (Embed Point.Type a, Embed Point.Type b)
  => Lifted (Expr Point.ExprF val f) a
  -> Lifted (Expr Point.ExprF val f) b
  -> Lifted (Expr Point.ExprF val f) (a, b)
pair ea eb = lift $ Point.pair arep brep (unlift ea) (unlift eb)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

fst
  :: forall val f a b .
     (Embed Point.Type a, Embed Point.Type b)
  => Lifted (Expr Point.ExprF val f) (a, b)
  -> Lifted (Expr Point.ExprF val f) a
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

variant_A :: Lifted (Expr Point.ExprF val f) ApplicationSpecificType
variant_A = lift $ Point.exprF $ Point.IntroSum trep Point.unit_t
  (Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_B :: Lifted (Expr Point.ExprF val f) ApplicationSpecificType
variant_B = lift $ Point.exprF $ Point.IntroSum trep Point.unit_t
  (Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_C :: Lifted (Expr Point.ExprF val f) ApplicationSpecificType
variant_C = lift $ Point.exprF $ Point.IntroSum trep Point.unit_t
  (Or $ Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_D :: Lifted (Expr Point.ExprF val f) ApplicationSpecificType
variant_D = lift $ Point.exprF $ Point.IntroSum trep Point.unit_t
  (Or $ Or $ Or $ Any Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

-- | Case match to eliminate an ApplicationSpecificType
case_variant
  :: forall val f r .
     (Embed Point.Type r)
  => Lifted (Expr Point.ExprF val f) ApplicationSpecificType
  -> Lifted (Expr Point.ExprF val f) r -- if A
  -> Lifted (Expr Point.ExprF val f) r -- if B
  -> Lifted (Expr Point.ExprF val f) r -- if C
  -> Lifted (Expr Point.ExprF val f) r -- if D
  -> Lifted (Expr Point.ExprF val f) r
case_variant vv cA cB cC cD = lift $ Point.exprF $ Point.ElimSum srep rrep
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
