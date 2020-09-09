{-|
Module      : Language.Pilot.Examples
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Pilot.Examples
  ( module Language.Pilot.Examples
  , module Pilot
  , module Examples
  ) where

import qualified Prelude
import Prelude (String, Int)
import Data.Functor.Identity
import Data.Proxy
import Language.Pilot as Pilot
import Language.Pilot.Repr (evalObject, fromObject, getRepr)
import Language.Pilot.Interp.Pure as Pure
import qualified Language.Pilot.Interp.C as C
import qualified Language.Pilot.Interp.Pure.PrefixList as PrefixList
import qualified Language.Pilot.Interp.Pure.Point as Point

import Language.Pilot.Examples.Copilot as Examples

showPureStream :: Prelude.Maybe Int -> E Identity Pure.Value (Obj (Varying n t)) -> String
showPureStream n e = case runIdentity (evalObject e) of
  Pure.Varying pl -> PrefixList.prettyPrint n Point.prettyPrint pl

showPureStreamProgram
  :: Prelude.Maybe Int
  -> E Identity Pure.Value (Obj (Program (Obj (Varying n t))))
  -> String
showPureStreamProgram n e = case runIdentity (evalObject e) of
  Pure.Program p -> case runIdentity (evalObject p) of
    Pure.Varying pl -> PrefixList.prettyPrint n Point.prettyPrint pl

showPurePoint :: E Identity Pure.Value (Obj (Constant t)) -> String
showPurePoint e = case runIdentity (evalObject e) of
  Pure.Constant p -> Point.prettyPrint p

example_0_0 :: E f val (Obj (Constant UInt8))
example_0_0 = u8 42

example_0_1 :: E f val (Obj (Constant UInt8))
example_0_1 = example_0_0 Pilot.+ example_0_0

example_0_2 :: E f val (Obj (Constant UInt8))
example_0_2 = local_auto example_0_0 $ \x -> x Pilot.+ x

example_0_3 :: E f val (Obj (Constant UInt8))
example_0_3 = local_auto example_0_2 $ \x -> x Pilot.* x

example_0_4 :: E f val (Obj (Constant UInt16))
example_0_4 = local_auto example_0_3 $ \x -> local_auto example_0_2 $ \y ->
  (Pilot.cast (Pilot.UpCastInteger Pilot.TwoWiderOne) <@> x)
  Pilot.+
  (Pilot.cast (Pilot.UpCastInteger Pilot.TwoWiderOne) <@> y)

example_0_5 :: E f val (Obj (Varying Z UInt8))
example_0_5 =
  Pilot.map_auto Z_Rep <@> (Pilot.uncurry <@> Pilot.add) <@>
    (  (Pilot.constant_auto Z_Rep <@> example_0_1)
    <& (Pilot.constant_auto Z_Rep <@> example_0_0)
    )

-- | Example of a simple product, whose normal form is the same as itself.
example_1_0 :: E f val (Obj (Constant (Pair UInt8 Int16)))
example_1_0 = pair_auto <@> u8 42 <@> i16 (-42)

-- | Example of a product whose normal form is smaller than itself.
example_1_1 :: E f val (Obj (Constant (Pair UInt8 (Pair Unit Int16))))
example_1_1 = pair_auto <@> u8 42 <@> (pair_auto <@> unit <@> i16 (-42))

-- | Example of a product which normalizes to a non-product.
example_1_2 :: E f val (Obj (Constant (Pair Unit UInt8)))
example_1_2 = pair_auto <@> unit <@> u8 42

-- | Example of a product which normalizes to unit.
example_1_3 :: E f val (Obj (Constant (Pair Unit (Pair Unit Unit))))
example_1_3 = pair_auto <@> unit <@> (pair_auto <@> unit <@> unit)

-- | Example of a product which remains nested when normalized.
example_1_4 :: E f val (Obj (Constant (Pair UInt8 (Pair UInt16 UInt32))))
example_1_4 = pair_auto <@> u8 0 <@> (pair_auto <@> u16 1 <@> u32 2)

example_1_5 :: E f val (Obj (Constant UInt8))
example_1_5 = Pilot.fst_auto <@> example_1_4

example_1_6 :: E f val (Obj (Constant (Pair UInt16 UInt8)))
example_1_6 = local_auto example_1_4 $ \it ->
  pair_auto <@> ((Pilot.fst_auto <.> Pilot.snd_auto) <@> it) <@> (Pilot.fst_auto <@> it)

-- | Example using compare, which is our first example where the C interpreter
-- must do nontrivial things with compound statements.
example_2_0 :: E f val (Obj (Constant Int8))
example_2_0 = local_auto example_0_3 $ \x ->
  local_auto example_0_4 $ \y ->
    compare_auto <@> i8 (-1) <@> i8 0 <@> i8 1 <@> (cast (UpCastInteger TwoWiderOne) <@> x) <@> y

example_2_1 :: E f val (Obj (Varying ('S 'Z) UInt8))
example_2_1 = Pilot.constant_auto (S_Rep Z_Rep) <@> u8 42

-- This is like
--
--   (\x y -> flip maybe ((+) 1) <$> x <*> y) :: Stream Int -> Stream (Maybe Int) -> Stream Int
--
-- The similarity is more clear when it's written like this
--
--   \x y -> pure f <*> x <*> y
--     where
--     f = flip maybe ((+) 1)
--
example_3 :: forall f val n . ( Known n ) => E f val
  (Obj (Varying n UInt8) :-> Obj (Varying n (Pilot.Maybe UInt8)) :-> Obj (Varying n UInt8))
example_3 = fun $ \x -> fun $ \y ->
  map_auto (known (Proxy :: Proxy n)) <@> (Pilot.uncurry <@> f) <@> (x <& y)
  where
  f = Pilot.flip <@> Pilot.maybe <@> (add <@> u8 1)

-- Notice that we can't lift maybe itself, since one of its arguments is
-- a function, and we cannot have varying functions. But this doesn't mean that
-- we can't use the value of another varying within the "just" case for the
-- maybe eliminator; we just have to juggle the definition so that the just
-- case always appear fully-applied, like this example, which adds the
-- value in the second varying rather than always 1 as in example_3.
--
--   \x y z -> pure f <*> x <*> y <*> z
--     where
--     f x y z = maybe x ((+) y) z
--
example_4 :: forall f val n . ( Known n ) => E f val
  (   Obj (Varying n UInt8)
  :-> Obj (Varying n UInt8)
  :-> Obj (Varying n (Pilot.Maybe UInt8))
  :-> Obj (Varying n UInt8)
  )
example_4 = fun $ \x -> fun $ \y -> fun $ \z ->
  map_auto nrep <@> (Pilot.uncurry <@> (Pilot.uncurry <@> f)) <@> (x <& y <& z)
  where
  nrep = known (Proxy :: Proxy n)
  f = fun $ \x -> fun $ \y -> fun $ \z ->
        -- Here will fully apply the just case eliminator, so that the function
        -- f--which we shall lift--is first-order over constants.
        Pilot.maybe <@> x <@> (add <@> y) <@> z

-- | This is one of the simplest examples of a memory stream recursive knot.
-- It creates a memory stream of size 1, and each step uses the previous value
-- as its current value, i.e. it's a constant stream. The argument is the
-- initial value of this stream. So this is essentially the same thing as
-- `lift` specialized to `'S 'Z` prefix size and `Constant UInt8` type.
example_5 :: E f val
  (Obj (Constant UInt8) :-> Obj (Program (Obj (Varying ('S 'Z) UInt8))))
example_5 = knot_auto (Tied (S_Rep Z_Rep) auto) <@> loop
  where
  loop :: E f val (Obj (Varying 'Z UInt8) :-> Obj (Varying 'Z UInt8))
  loop = Pilot.identity

-- | Here's an integral.
example_6 :: E f val
  (Obj (Constant UInt8) :-> Obj (Varying 'Z UInt8) :-> Obj (Program (Obj (Varying ('S 'Z) UInt8))))
example_6 = fun $ \c -> fun $ \f ->
  let loop = fun $ \pre -> map_auto Z_Rep <@> (Pilot.uncurry <@> add) <@> (f <& pre)
  in  knot_auto (Tied (S_Rep Z_Rep) auto) <@> loop <@> c

example_6_c_0 :: E C.ValueM C.Value (Obj (Program (Obj (Varying 'Z UInt8))))
example_6_c_0 = C.externInput "blargh" uint8_t C.integerIsInhabited >>= \inp ->
  (example_6 <@> u8 0 <@> inp) >>= \result ->
    prog_pure auto <@> (drop_auto <@> result)

example_6_c_1 :: E C.ValueM C.Value (Obj (Program (Obj (Varying 'Z UInt8))))
example_6_c_1 = example_6_c_0 >>= \stream ->
  (C.externOutput "blorgh" uint8_t <@> stream) >>= \_ ->
    -- We have to give a stream in order to make a translation unit.
    prog_pure auto <@> (Pilot.constant_auto Z_Rep <@> u8 42)

-- | [42, 42 ..]
example_7 :: E f val (Obj (Varying 'Z UInt8))
example_7 = Pilot.constant_auto Z_Rep <@> u8 42

example_8 :: Known n => NatRep n -> E f val
  (Obj (Varying n UInt8) :-> Obj (Varying n UInt8) :-> Obj (Varying n UInt8))
example_8 nrep = Pilot.curry <@> (map_auto nrep <@> (Pilot.uncurry <@> add))

example_9 :: E f val (Obj (Program (Obj (Varying Z Int32))))
example_9 = prog_map auto auto <@> shift_auto <@>
  (counter <@> (Pilot.constant_auto Z_Rep <@> true) <@> (Pilot.constant_auto Z_Rep <@> false))
