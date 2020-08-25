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

module Language.Pilot.Examples
  ( module Language.Pilot.Examples
  , module Pilot
  ) where

import Data.Functor.Identity
import Data.Proxy
import Language.Pilot as Pilot
import Language.Pilot.Repr (evalObject)
import Language.Pilot.Interp.Pure as Pure
import qualified Language.Pilot.Interp.Pure.PrefixList as PrefixList
import qualified Language.Pilot.Interp.Pure.Point as Point

import Language.Pilot.Examples.Counter

showPureStream :: Prelude.Maybe Int -> E Identity Pure.Value (Obj (Varying n t)) -> String
showPureStream n e = case runIdentity (evalObject e) of
  Pure.Varying pl -> PrefixList.prettyPrint n Point.prettyPrint pl

showPurePoint :: E Identity Pure.Value (Obj (Constant t)) -> String
showPurePoint e = case runIdentity (evalObject e) of
  Pure.Constant p -> Point.prettyPrint p

example_1 :: E f val (Obj (Constant (Pair Pilot.Bool Pilot.Bool)))
example_1 = pair <@> true <@> false

example_2 :: E f val (Obj (Varying ('S 'Z) UInt8))
example_2 = Pilot.constant (S_Rep Z_Rep) <@> u8 42

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
  map_ (known (Proxy :: Proxy n)) <@> (Pilot.uncurry <@> f) <@> (x <& y)
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
  map_ nrep <@> (Pilot.uncurry <@> (Pilot.uncurry <@> f)) <@> (x <& y <& z)
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
  (Obj (Constant UInt8) :-> Obj (Varying ('S 'Z) UInt8))
example_5 = knot (Tied (S_Rep Z_Rep)) <@> loop <@> k
  where
  loop :: E f val (Obj (Varying 'Z UInt8) :-> Obj (Varying 'Z UInt8))
  loop = Pilot.identity
  k :: E f val (Obj (Varying ('S 'Z) UInt8) :-> Obj (Varying ('S 'Z) UInt8))
  k = Pilot.identity

-- | Here's an integral.
example_6 :: E f val
  (Obj (Constant UInt8) :-> Obj (Varying 'Z UInt8) :-> Obj (Varying ('S 'Z) UInt8))
example_6 = fun $ \c -> fun $ \f ->
  let loop = fun $ \pre -> map_ Z_Rep <@> (Pilot.uncurry <@> add) <@> (f <& pre)
  in  knot (Tied (S_Rep Z_Rep)) <@> loop <@> Pilot.identity <@> c

-- | [42, 42 ..]
example_7 :: E f val (Obj (Varying 'Z UInt8))
example_7 = Pilot.constant Z_Rep <@> u8 42

example_8 :: Known n => NatRep n -> E f val
  (Obj (Varying n UInt8) :-> Obj (Varying n UInt8) :-> Obj (Varying n UInt8))
example_8 nrep = Pilot.curry <@> (map_ nrep <@> (Pilot.uncurry <@> add))

example_9 = showPureStream (Just 100) $
  counter <@> (Pilot.constant Z_Rep <@> true) <@> (Pilot.constant Z_Rep <@> false)
