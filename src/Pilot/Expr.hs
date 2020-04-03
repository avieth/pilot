{-|
Module      : Pilot.Expr
Description : Definition of expressions for the EDSL
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE EmptyCase #-}


module Pilot.Expr
{-
  ( Expr
  , ExprF (..)
  , ExprK (..)

  , constant
  , hold
  , next
  , apply

  , evalStream
  )-} where

import Pilot.Types.Nat
import Pilot.Types.Stream (Stream)
import qualified Pilot.Types.Stream as Stream
import Data.Kind (Type)

data Args (f :: Nat -> Type -> Type) (args :: [Type]) (n :: Nat) where
  OneArg   :: f n ty -> Args f '[ty] n
  MoreArgs :: f n ty -> Args f tys m -> Args f (ty ': tys) (Min n m)

mapArgs
  :: (forall m t . f m t -> g m t)
  -> Args f args n
  -> Args g args n
mapArgs nat (OneArg f)        = OneArg (nat f)
mapArgs nat (MoreArgs f args) = MoreArgs (nat f) (mapArgs nat args)

-- | TODO document.
data ExprF (op :: [Type] -> Type -> Type) (f :: Nat -> Type -> Type) (n :: Nat) (t :: Type) where

  -- | Self-explanatory.
  Constant :: t -> ExprF op f Z t
  -- | Holds a known value in front of the stream.
  Hold :: t -> f m t -> ExprF op f (S m) t
  -- | Drops a value from the front of the stream, undoing a 'Hold'.
  Next :: f (S m) t -> ExprF op f m t

  -- | Some operation. ExprF is parametric what what that means. It is a
  -- GADT which expresses variadic functions with a given return value.
  -- By definition of the 'Args' GADT, operations with no arguments (empty
  -- list parameter) cannot be put here.
  Op :: op args r -> Args f args n -> ExprF op f n r



-- | Type for constructing compound 'ExprF's.
newtype ExprK f g n t = ExprK
  { getExprK :: (forall m r . f m r -> g m r) -> g n t }

type Expr op f = ExprK (ExprF op f) f

constant :: t -> Expr op f Z t
constant t = ExprK $ \eval -> eval (Constant t)

hold :: t -> Expr op f m t -> Expr op f (S m) t
hold t xs = ExprK $ \eval -> eval (Hold t (getExprK xs eval))

next :: Expr op f (S n) t -> Expr op f n t
next xs = ExprK $ \eval -> eval (Next (getExprK xs eval))

-- Note on what we're doing here: the 'Args' are 'ExprK's, but we must evaluate
-- them all before we can construct the 'Op' variant, so we 'mapArgs'. It's
-- the same motif as for the others ('hold', 'next', 'constant') just quite a
-- bit more complicated at a glance.
op :: op args r -> Args (Expr op f) args n -> Expr op f n r
op op args = ExprK $ \eval -> eval (Op op (mapArgs (\e -> getExprK e eval) args))

data SimpleOp (args :: [Type]) (r :: Type) where
  Add :: SimpleOp '[Int, Int] Int

-- | Evaluate an expression as a stream.
-- This basically amounts to constants and zips, i.e. the applicative style
-- interface on streams.
--
-- TODO generalize over op.
evalStream :: ExprF SimpleOp Stream n t -> Stream n t
evalStream (Constant t)  = Stream.repeat t
evalStream (Hold x xs) = Stream.Prefix x xs
evalStream (Next (Stream.Prefix _ xs)) = xs
evalStream (Op Add (MoreArgs xs (OneArg ys))) = Stream.zip (+) xs ys
-- GHC can't figure this out on its own? :O
evalStream (Op Add (MoreArgs _ (MoreArgs _ x))) = case x of {}

add :: Expr SimpleOp f m Int -> Expr SimpleOp f n Int -> Expr SimpleOp f (Min m n) Int
add xs ys = op Add (MoreArgs xs $ OneArg ys)

example_1 :: Expr SimpleOp f Z Int
example_1 = add (constant 1) (constant 2)

example_2 :: Expr SimpleOp f Z Int
example_2 = next
  where
  sums = hold 0 next
  next = add example_1 sums

-- Slight hiccup here:
-- 1. The op type needs to have the expression as a parameter, so that we can
--    implement sum elimination (you give an `expr ty -> expr r` for each
--    variant).
-- 2. Given 1, the evaluated type for the pure stream variant needs to be a
--    single thing, rather than a stream, because sum elimination would not
--    be possible if each expr represented directly a whole stream of things:
--    a stream of `Either a b`, for instance, does not give a stream of `a` and
--    `b`.
-- So what we want to say is, if you can evaluate each expression to a single
-- point, then we can evaluate each expression to a stream of points.

{-
  Add  :: f m Int -> f n Int -> ExprF f (Min m n) Int
  Apply :: f m (a -> b) -> f n a -> ExprF f (Min m n) b


apply :: Expr f m (a -> b) -> Expr f n a -> Expr f (Min m n) b
apply xf xx = ExprK $ \eval -> 
  eval (Apply (getExprK xf eval) (getExprK xx eval))

example_3 :: Expr f Z (Int, Int)
example_3 = apply (apply (constant (,)) (example_2)) (example_1)

-- Average each pair of adjacent stream elements.
--
-- In order to do this, we need to hold onto the most recent value from the
-- inhold stream (here it's set to example_2).
--
-- By doing so, we are able to use `next` in the average comholdation, to get
-- the current thing (without nextping, we get the previous value).
--
-- The composite thing has Z as its parameter because there is only ever
-- one thing available (this stream itself does not hold on to more than one
-- value at an instant).
example_4 :: Expr f Z Double
example_4 = avg
  where
  stream :: Expr f (S Z) Int
  stream = hold 0 example_2
  avg :: Expr f Z Double
  avg = apply (constant (\x -> fromIntegral x / 2)) (add stream (next stream))
  -}
