{-|
Module      : Pilot.Domain.Hask
Description : Hask as a domain for the pointwise and streamwise EDSLs.
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

module Pilot.Domain.Hask
  ( type Type
  , type Point
  , type Function
  , Op (..)
  , Target (..)
  , val
  , evalPoint
  , evalLet
  , evalOp
  , evalFun
  , evalAp

  , Stream (..)
  , streamToList
  , evalStreamHold
  , evalStreamDrop
  , evalStreamPure
  , evalStreamAp
  , evalStreamLet
  ) where

import qualified Data.Kind as Kind (Type)
import Data.Functor.Identity

import Pilot.Types.Args (Args (..))
import Pilot.Types.Nat
import Pilot.Types.Point (type (:->), type T)
import qualified Pilot.Types.Point as Pilot

-- | Types in this domain are Haskell types.
type Type = Kind.Type

-- | Points in this domain are Haskell values (with Haskell types).
type Point = Identity

-- | Operations in this domain are Haskell functions.
data Op (target :: Pilot.Kind Type -> Kind.Type) (args :: [Type]) (return :: Type) where
  Op :: Function args return -> Op target args return

-- | Make a typical Haskell function from an argument list and return type.
-- Elements of the argument list can of course also be Haskell functions so
-- really this is 1-to-1 with Haskell functions.
type family Function (args :: [Type]) (return :: Type) :: Type where
  Function '[] return = return
  Function (arg ': args) return = arg -> Function args return

data Target (t :: Pilot.Kind Type) where
  Fun :: (Target s -> Target t) -> Target (s :-> t)
  Val :: t -> Target (T t)

val :: Target (T t) -> t
val (Val t) = t

evalPoint :: Point t -> Target (T t)
evalPoint (Identity t) = Val t

-- | This is trivial because Haskell already gives sharing.
-- Other targets might have to do something special here.
evalLet :: Target (T s) -> (Target (T s) -> Target t) -> Target t
evalLet (Val s) k = k (Val s)

evalOp :: Op Target args r -> Args Target args -> Target (T r)
evalOp (Op f) ArgNone                = Val f
evalOp (Op f) (ArgMore (Val x) args) = let g = f x in evalOp (Op g) args

evalFun :: (Target q -> Target r) -> Target (q :-> r)
evalFun = Fun

evalAp :: Target (s :-> t) -> Target s -> Target t
evalAp (Fun f) = f

example_1 :: Op target '[ a ] a
example_1 = Op id

example_2 :: Op target '[ a, b ] a
example_2 = Op const

example_3 :: Op target '[ Int, Int ] Int
example_3 = Op (+)

example_4 :: Op target '[ Maybe Int ] Int
example_4 = Op $ maybe 0 ((+) 1)

-- | Pure Haskell streams. A target for stream expressions which gives pure
-- in-Haskell evaluation (suitable for simulation, for example, of an
-- expression which may also target C99).
--
-- This also serves as a reference definition/implementation for any other
-- stream target. There must be a coherence with this idea. TODO explain
-- exactly what that coherence must be.
--
-- These are infinite lists with a prefix of size determined by the Nat type
-- parameter. Elements of the list are in 'Pilot.Types.Pilot.Point', so that
-- the kind of the final type parameter is 'Pilot.Types.Pilot.Kind'.
data Stream (target :: Pilot.Kind t -> Kind.Type) (n :: Nat) (p :: Pilot.Kind t) where
  Prefix :: target t -> Stream target n t -> Stream target (S n) t
  Suffix :: target t -> Stream target Z t -> Stream target  Z    t

streamToList :: Stream Target n (Pilot.T t) -> [t]
streamToList (Prefix (Val pt) next) = pt : streamToList next
streamToList (Suffix (Val pt) next) = pt : streamToList next

streamRepeat :: target t -> Stream target Z t
streamRepeat pt = Suffix pt (streamRepeat pt)

streamZip
  :: (target s -> target t -> target u)
  -> Stream target m s
  -> Stream target n t
  -> Stream target (Min m n) u
streamZip f (Prefix a as) (Prefix b bs) = Prefix (f a b) (streamZip f as bs)
streamZip f (Suffix a as) (Suffix b bs) = Suffix (f a b) (streamZip f as bs)
streamZip f (Prefix a as) (Suffix b bs) = Suffix (f a b) (streamZip f as bs)
streamZip f (Suffix a as) (Prefix b bs) = Suffix (f a b) (streamZip f as bs)

evalStreamHold
  :: Vec (S n) (target (T t))
  -> (Stream target n (T t) -> Stream target Z (T t))
  -> Stream target (S n) (T t)
evalStreamHold vs k =
  -- Must be sufficiently lazy in computing the `prefix`: it cannot force
  -- anything to do with the suffix of `result`. So instead of taking
  -- `result` and moving the final prefix into the suffix, which would require
  -- matching on the suffix, we do a similar "from vector" computation but
  -- which leaves out the last vector element.
  let result = streamFromVec vs suffix
      prefix = prefixFromVec vs suffix
      suffix = k prefix
  in  result

  where

  streamFromVec
    :: Vec n (target t)
    -> Stream target Z t
    -> Stream target n t
  streamFromVec VNil         suffix = suffix
  streamFromVec (VCons v vs) suffix = Prefix v (streamFromVec vs suffix)

  prefixFromVec
    :: Vec (S n) (target t)
    -> Stream target Z t
    -> Stream target n t
  prefixFromVec (VCons t VNil)           stream = Suffix t stream
  prefixFromVec (VCons t vs@(VCons _ _)) stream = Prefix t (prefixFromVec vs stream)

evalStreamDrop :: Stream target (S n) r -> Stream target n r
evalStreamDrop (Prefix _ xs) = xs

evalStreamPure :: target r -> Stream target Z r
evalStreamPure = streamRepeat

evalStreamAp :: Stream Target m (s :-> t) -> Stream Target n s -> Stream Target (Min m n) t
evalStreamAp = streamZip evalAp

-- | This is trivial because Haskell already gives sharing.
-- Other targets might have to do something special here.
evalStreamLet
  :: Stream target m (T q)
  -> (Stream target m (T q) -> Stream target n s)
  -> Stream target n s
evalStreamLet q k = k q

-- | This integral expression is just as fast as the pure list variant
--
--   let sums = 0 : zipWith (+) (repeat 42) sums in drop 1 sums
--
example_stream_1 :: Stream Target Z (T Int)
example_stream_1 = next
  where
  sums = Prefix (Val 0) next
  next = evalStreamAp (evalStreamAp (streamRepeat plus) (streamRepeat (Val  42))) sums
  plus :: Target (T Int :-> T Int :-> T Int)
  plus = Fun $ \(Val x) -> Fun $ \(Val y) -> Val (x + y)
