{-|
Module      : Pilot.EDSL.Pointwise
Description : Pointwise portion of the EDSL.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.EDSL.Pointwise where

import qualified Data.Kind as Kind (Type)
import Pilot.Types.Args
import Pilot.Types.Point (type (:->), type T)
import qualified Pilot.Types.Point as Pilot

-- | Assuming a way to deal with primitive points given the `point` and
-- `op` types, get a 'Point' in some `target` type. That is, higher-order
-- functions over the target type.
--
-- This is essentially a `target t` but abstracted over the 5 combinators:
-- - injection of a domain-specific point
-- - evaluation of a domain-specific fully-saturated operator
-- - let bindigns
-- - lambda abstraction
-- - lambda application
--
-- TODO if we had a generic Point type
--
--   Fun :: (Point target a -> Point target b) -> Point target (a :-> b)
--   Val :: target a -> Point target (T a)
--
-- and we used that as the result of runPointwise, then we would have a generic
-- abstraction and application implementation and would only need 3 continuations
-- here.
newtype Pointwise (point :: ty -> Kind.Type) (op :: (Pilot.Kind ty -> Kind.Type) -> [ty] -> ty -> Kind.Type) target t = Pointwise
  { runPointwise :: (forall r . point r -> target (T r))
                 -- ^ Domain-specific literals
                 -> (forall args r . op target args r -> Args target args -> target (T r))
                 -- ^ Domain-specific operators
                 -> (forall q r . target (T q) -> (target (T q) -> target (T r)) -> target (T r))
                 -- ^ Let bindings
                 -> (forall q r . (target q -> target r) -> target (q :-> r))
                 -- ^ Abstraction
                 -> (forall q r . target (q :-> r) -> target q -> target r)
                 -- ^ Application
                 -> target t
  }

-- | A point literal.
point :: point t -> Pointwise point op target (T t)
point pt = Pointwise $ \evalPoint _ _ _ _ -> evalPoint pt

-- NB: `fun` and `at` give a correspondance between Haskell functions and
-- pointwise functions. The Haskell arrow between `Pointwise` expressions
-- becomes a `Pointwise` arrow expression.

-- | Lambda abstraction.
fun :: (Pointwise point op target s -> Pointwise point op target t)
    -> Pointwise point op target (s :-> t)
fun f = Pointwise $ \evalPoint evalOp evalLet evalFun evalAp -> evalFun $ \target ->
  let y = f (Pointwise $ \_ _ _ _ _ -> target)
  in  runPointwise y evalPoint evalOp evalLet evalFun evalAp

-- | Apply a pointwise function to a pointwise argument (see 'fun' for how
-- a function may be created).
at :: Pointwise point op target (a :-> b)
   -> Pointwise point op target a
   -> Pointwise point op target b
at pf px = Pointwise $ \evalPoint evalOp evalLet evalFun evalAp -> evalAp
  (runPointwise pf evalPoint evalOp evalLet evalFun evalAp)
  (runPointwise px evalPoint evalOp evalLet evalFun evalAp)

-- | An operation with given arguments (see 'fun' for how you can get those
-- arguments).
op :: op target args t
   -> Args (Pointwise point op target) args
   -> Pointwise point op target (T t)
op o args = Pointwise $ \evalPoint evalOp evalLet evalFun evalAp -> evalOp o
  (mapArgs (\arg -> runPointwise arg evalPoint evalOp evalLet evalFun evalAp) args)

-- | Let binding. Allows expression of sharing.
plet :: Pointwise point op target (T q)
     -> (Pointwise point op target (T q) -> Pointwise point op target (T r))
     -> Pointwise point op target (T r)
plet q k = Pointwise $ \evalPoint evalOp evalLet evalFun evalAp ->
  evalLet (runPointwise q evalPoint evalOp evalLet evalFun evalAp) $ \q' ->
    runPointwise (k (Pointwise $ \_ _ _ _ _ -> q')) evalPoint evalOp evalLet evalFun evalAp