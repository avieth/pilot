{-|
Module      : Pilot.Expr
Description : Definition of pointwise and streamwise EDSL parts.
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

module Pilot.Expr
  ( PointF (..)
  , PointKind (..)
  , Point (..)
  , Pointwise (..)
  , Args (..)
  , mapArgs

  , apply
  , val
  , lit
  , point
  , op
  , fun
  , at

  , StreamF (..)
  , Streamwise (..)
  , hold
  , next
  , constant
  , ap

  , evalStream
  ) where

import Pilot.Types.Nat
import Pilot.Types.Stream (Stream)
import qualified Pilot.Types.Stream as Stream
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)

-- | Arguments, used to saturate a variadic operator (see 'PointF').
data Args (f :: ty -> Type) (args :: [ty]) where
  ArgNone :: Args f '[]
  ArgMore :: f arg -> Args f args -> Args f (arg ': args)

mapArgs :: (forall t . f t -> g t) -> Args f args -> Args g args
mapArgs _    ArgNone         = ArgNone
mapArgs nat (ArgMore f args) = ArgMore (nat f) (mapArgs nat args)

-- | Definition of the pointwise EDSL.
--
-- This is the most basic piece of the overall stream EDSL.
--
-- It's parameterized on the type of points `ty`, the representation of these
-- points `point :: ty -> Type`, and the operations which can be done on these
-- points `op :: [ty] -> ty -> Type`.
data PointF (point :: ty -> Type) (op :: (ty -> Type) -> [ty] -> ty -> Type) (t :: ty) where
  -- | An atomic value, as determined by the `point` type.
  LitF :: point ty -> PointF point op ty
  -- | A variadic operation (parameteric) over `point`s.
  --
  -- The arguments must be `point`s, no higher-order function arguments here,
  -- although it is possible for the `op` constructor itself to have functions
  -- in it (of type `Point point (a :-> b)`)
  OpF  :: op point args t -> Args point args -> PointF point op t

-- | Just like the Haskell 98 kind definition
--
--   K = * | K -> K
--
-- This is used to give a kind to 'Point', the type for points with higher-order
-- functions over points.
data PointKind ty where
  Arrow   :: PointKind ty -> PointKind ty -> PointKind ty
  Literal :: ty -> PointKind ty

infixr 0 :->
type (:->) = Arrow

type T = Literal

-- | Points (`point`) in some domain (`ty`) with higher-order functions.
data Point (point :: ty -> Type) (k :: PointKind ty) where
  Fun :: (Point point s -> Point point t) -> Point point (Arrow s t)
  Lit :: point t -> Point point (Literal t)

apply :: Point point (Arrow s t) -> Point point s -> Point point t
apply (Fun f) = f

val :: Point point (Literal t) -> point t
val (Lit x) = x

lit :: point t -> Point point (Literal t)
lit = Lit

-- | Assuming a way to deal with primitive points given the `point` and
-- `op` types, get a 'Point' i.e. primitive points with higher-order functions.
newtype Pointwise point op t = Pointwise
  { runPointwise :: (forall r . PointF point op r -> point r) -> Point point t
  }

point :: point t -> Pointwise point op (Literal t)
point x = Pointwise $ \evalPoint -> Lit (evalPoint (LitF x))

op :: op point args t -> Args point args -> Pointwise point op (Literal t)
op op args = Pointwise $ \evalPoint -> Lit $ evalPoint $ OpF op args

fun :: (Point point s -> Pointwise point op t) -> Pointwise point op (Arrow s t)
fun f = Pointwise $ \evalPoint -> Fun (\pval -> runPointwise (f pval) evalPoint)

at :: Pointwise point op (a :-> b)
   -> Pointwise point op a
   -> Pointwise point op b
at pf px = Pointwise $ \evalPoint -> apply (runPointwise pf evalPoint) (runPointwise px evalPoint)

-- | Definition of the stream EDSL.
--
-- These are expressed pointwise in an applicative style: you can one point to
-- get a constant stream (like `pure`), map a pointwise function over a stream
-- (like `fmap`), and apply pointwise functions through streams (like `<*>`).
--
-- In addition, points may be placed in front of streams, giving a way to
-- express memory. The `Nat` parameter indicates how many of these were
-- prepended to the stream.
data StreamF (stream :: Nat -> Type -> Type) (point :: ty -> Type) (n :: Nat) (t :: PointKind ty) where

  -- | Put a point expression before a stream.
  HoldF :: Point point t -> stream n (Point point t) -> StreamF stream point (S n) t
  -- | Drop the head of the stream, undoing a 'HoldF'
  DropF :: stream (S n) (Point point t) -> StreamF stream point n t

  -- | Constant; called pure by analogy to the Applicative style.
  PureF :: Point point t -> StreamF stream point Z t

  -- | Combine streams applicatively.
  ApF :: stream m (Point point (Arrow s t))
      -> stream n (Point point s)
      -> StreamF stream point (Min m n) t

-- | Given a way to evaluate streams and points, get a final stream.
newtype Streamwise stream point op n t = Streamwise
  { runStreamwise :: (forall m r . StreamF stream point m r -> stream m (Point point r))
                  -> (forall r . PointF point op r -> point r)
                  -> stream n (Point point t)
  }

hold :: Pointwise         point op       t
     -> Streamwise stream point op n     t
     -> Streamwise stream point op (S n) t
hold pt st = Streamwise $ \evalStream evalPoint -> evalStream $
  HoldF (runPointwise pt evalPoint) (runStreamwise st evalStream evalPoint)

next :: Streamwise stream point op (S n) t
     -> Streamwise stream point op    n  t
next st = Streamwise $ \evalStream evalPoint -> evalStream $
  DropF (runStreamwise st evalStream evalPoint)

constant :: Pointwise         point op   t
         -> Streamwise stream point op Z t
constant pt = Streamwise $ \evalStream evalPoint -> evalStream $
  PureF (runPointwise pt evalPoint)

ap :: Streamwise stream point op m         (Arrow s t)
   -> Streamwise stream point op n         s
   -> Streamwise stream point op (Min m n) t
ap fs xs = Streamwise $ \evalStream evalPoint -> evalStream $
  ApF (runStreamwise fs evalStream evalPoint) (runStreamwise xs evalStream evalPoint)


-- | An example evaluator where
--
--   - `ty ~ Type` and `point ~ Identity`: we use typical Haskell types as the
--      domain.
--   - `stream ~ Stream`: we have prefix-indexed infinite streams as our
--     target.
--
-- This is intended to demonstrate the intended semantics of the EDSL:
-- points and pointwise functions can be made into constant streams, and
-- streams may be combined applicatively according to the pointwise functions
-- they carry. Yet the representation is general enough to allow for code
-- generation rather than only for execution within a Haskell runtime.
evalStream :: StreamF Stream Identity n t -> Stream n (Point Identity t)
evalStream (HoldF x xs)                 = Stream.Prefix x xs
evalStream (DropF (Stream.Prefix _ xs)) = xs
evalStream (PureF pt)                   = Stream.repeat pt
evalStream (ApF fs xs)                  = Stream.zip apply fs xs

-- Examples follow

-- This will be useful for writing examples.
data SimpleOp (point :: Type -> Type) (args :: [Type]) (r :: Type) where
  Add   :: SimpleOp point '[Int, Int] Int
  Tuple :: SimpleOp point '[a, b] (a, b)
  IntroLeft  :: SimpleOp point '[a] (Either a b)
  IntroRight :: SimpleOp point '[b] (Either a b)
  -- Example of how to higher-order functions in the operator type.
  ElimEither :: (Point point (T a :-> T t))
             -> (Point point (T b :-> T t))
             -> SimpleOp point '[Either a b] t

-- Pure evaluation can be done by choosing Identity for points, and
-- Stream for streams, and some suitable operation type, like so:
evalPoint :: PointF Identity SimpleOp t -> Identity t
evalPoint (LitF t)         = t
evalPoint (OpF op args)    = case op of
  Add -> case args of
    ArgMore x (ArgMore y ArgNone) -> (+) <$> x <*> y
  Tuple -> case args of
    ArgMore x (ArgMore y ArgNone) -> (,) <$> x <*> y
  IntroLeft -> case args of
    ArgMore x ArgNone -> Left <$> x
  IntroRight -> case args of
    ArgMore y ArgNone -> Right <$> y
  ElimEither left right -> case args of
    ArgMore either ArgNone -> case runIdentity either of
      Left x  -> val (apply left (lit (Identity x)))
      Right y -> val (apply right (lit (Identity y)))

runExample :: Streamwise Stream Identity SimpleOp n (T t) -> [t]
runExample it = fmap (runIdentity . val) (Stream.toList (runStreamwise it evalStream evalPoint))

example_1 :: Pointwise Identity SimpleOp (a :-> T Int)
example_1 = fun $ \pval -> point (Identity 42)

example_2 :: Pointwise Identity SimpleOp (T Int :-> T Int)
example_2 = fun $ \pval -> op Add (ArgMore (val pval) $ ArgMore (Identity 42) $ ArgNone)

-- A higher-order function...
--
--   ex :: (a -> Int) -> a -> Int
--   ex f a = (f a) + 42
--
-- This higher-order function does not appear within the object language, rather
-- it's used in the meta language (Haskell) to construct terms in the object
-- language.
--
-- This is HOAS in some sense?
example_3 :: Pointwise Identity SimpleOp ((a :-> T Int) :-> (a :-> T Int))
example_3 = fun $ \f -> fun $ \a -> op Add (ArgMore (val (apply f a)) $ ArgMore (Identity 42) $ ArgNone)

add :: Pointwise point SimpleOp (T Int :-> T Int :-> T Int)
add = fun $ \x -> fun $ \y -> op Add (ArgMore (val x) $ ArgMore (val y) $ ArgNone)

tuple :: Pointwise point SimpleOp (T a :-> T b :-> T (a, b))
tuple = fun $ \a -> fun $ \b -> op Tuple (ArgMore (val a) $ ArgMore (val b) $ ArgNone)

-- | Constant stream of 3.
--
-- How do we apply pointwise before streamwise??
-- Do we have that alraedy?
example_4 :: Streamwise stream Identity SimpleOp Z (T Int)
example_4 = constant (add `at` (point (pure 1)) `at` (point (pure 2)))

-- | Same as 4 but with streamwise combination.
example_5 :: Streamwise stream Identity SimpleOp Z (T Int)
example_5 = constant add `ap` constant (point (pure 1)) `ap` constant (point (pure 2))

-- | An integral.
example_6 :: forall stream . Streamwise stream Identity SimpleOp Z (T Int)
example_6 = next
  where
  sums :: Streamwise stream Identity SimpleOp (S Z) (T Int)
  sums = hold (point (pure 0)) next
  next :: Streamwise stream Identity SimpleOp Z (T Int)
  next = constant add `ap` example_4 `ap` sums
