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
{-# LANGUAGE RankNTypes #-}

module Pilot.Expr
  ( Expr
  , ExprF (..)
  , ExprK (..)

  , constant
  , hold
  , next
  , apply

  , evalStream
  ) where

import Pilot.Types.Nat
import Pilot.Types.Stream (Stream)
import qualified Pilot.Types.Stream as Stream
import Data.Kind (Type)

-- | TODO document.
data ExprF (f :: Nat -> Type -> Type) (n :: Nat) (t :: Type) where
  Constant :: t -> ExprF f Z t
  -- | Holds a known value in front of the stream.
  Hold :: t -> f m t -> ExprF f (S m) t
  -- | Drops a value from the front of the stream, undoing a 'Hold'.
  Next :: f (S m) t -> ExprF f m t

  Add  :: f m Int -> f n Int -> ExprF f (Min m n) Int
  Apply :: f m (a -> b) -> f n a -> ExprF f (Min m n) b

-- | Evaluate an expression as a stream.
-- This basically amounts to constants and zips, i.e. the applicative style
-- interface on streams.
evalStream :: ExprF Stream n t -> Stream n t
evalStream (Constant t)  = Stream.repeat t
evalStream (Hold x xs) = Stream.Prefix x xs
evalStream (Next (Stream.Prefix _ xs)) = xs
evalStream (Add xs ys) = Stream.zip (+) xs ys
evalStream (Apply xf xx) = Stream.ap xf xx

-- | Type for constructing compound 'ExprF's.
newtype ExprK f g n t = ExprK
  { getExprK :: (forall m r . f m r -> g m r) -> g n t }

type Expr f n = ExprK (ExprF f) f n

constant :: t -> Expr f Z t
constant t = ExprK $ \eval -> eval (Constant t)

hold :: t -> Expr f m t -> Expr f (S m) t
hold t xs = ExprK $ \eval -> eval (Hold t (getExprK xs eval))

next :: Expr f (S n) t -> Expr f n t
next xs = ExprK $ \eval -> eval (Next (getExprK xs eval))

add :: Expr f m Int -> Expr f n Int -> Expr f (Min m n) Int
add x y = ExprK $ \eval ->
  eval (Add (getExprK x eval) (getExprK y eval))

apply :: Expr f m (a -> b) -> Expr f n a -> Expr f (Min m n) b
apply xf xx = ExprK $ \eval -> 
  eval (Apply (getExprK xf eval) (getExprK xx eval))

example_1 :: Expr f Z Int
example_1 = add (constant 1) (constant 2)

example_2 :: Expr f Z Int
example_2 = next
  where
  sums = hold 0 next
  next = add example_1 sums

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
