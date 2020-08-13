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

module Language.Pilot.Examples
  ( module Language.Pilot.Examples
  , module Pilot
  , Pure.interp_pure
  , Meta.metaInterp
  ) where

import Data.Proxy
import Language.Pilot as Pilot
import Language.Pilot.Expr (runExpr)
import Language.Pilot.Meta as Meta
import Language.Pilot.Interp.Pure as Pure
import qualified Language.Pilot.Interp.Pure.PrefixList as PrefixList
import qualified Language.Pilot.Interp.Pure.Point as Point

showPureStream :: Prelude.Maybe Int -> E Pure.Repr (Obj (Varying n t)) -> String
showPureStream n e = Meta.withObject (runExpr (metaInterp interp_pure) e) $ \t -> case t of
  Pure.Varying_r pl -> PrefixList.prettyPrint n Point.prettyPrint pl

showPurePoint :: E Pure.Repr (Obj (Constant t)) -> String
showPurePoint e = Meta.withObject (runExpr (metaInterp interp_pure) e) $ \t -> case t of
  Pure.Constant_r p -> Point.prettyPrint p

example_1 :: E repr (Obj (Constant (Pair Pilot.Bool Pilot.Bool)))
example_1 = pair <@> true <@> false

example_2 :: E repr (Obj (Varying ('S 'Z) UInt8))
example_2 = lift (S_Rep Z_Rep) <@> u8 42


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
example_3 :: forall repr n . ( Auto n ) => E repr
  (Obj (Varying n UInt8) :-> Obj (Varying n (Pilot.Maybe UInt8)) :-> Obj (Varying n UInt8))
example_3 = fun $ \x -> fun $ \y ->
  lift (repVal (Proxy :: Proxy n)) <@> f <@> x <@> y
  where
  f = Pilot.flip Pilot.maybe <@> (plus <@> u8 1)

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
example_4 :: forall repr n . ( Auto n ) => E repr
  (   Obj (Varying n UInt8)
  :-> Obj (Varying n UInt8)
  :-> Obj (Varying n (Pilot.Maybe UInt8))
  :-> Obj (Varying n UInt8)
  )
example_4 = fun $ \x -> fun $ \y -> fun $ \z ->
  lift (repVal (Proxy :: Proxy n)) <@> f <@> x <@> y <@> z
  where
  f = fun $ \x -> fun $ \y -> fun $ \z ->
        -- Here will fully apply the just case eliminator, so that the function
        -- f--which we shall lift--is first-order over constants.
        Pilot.maybe <@> x <@> (plus_u8 <@> y) <@> z

-- | This is one of the simplest examples of a memory stream recursive knot.
-- It creates a memory stream of size 1, and each step uses the previous value
-- as its current value, i.e. it's a constant stream. The argument is the
-- initial value of this stream. So this is essentially the same thing as
-- `lift` specialized to `'S 'Z` prefix size and `Constant UInt8` type.
example_5 :: E repr
  (Obj (Constant UInt8) :-> Obj (Varying ('S 'Z) UInt8))
example_5 = knot (Tied (S_Rep Z_Rep)) <@> loop <@> k
  where
  loop :: E repr (Obj (Varying 'Z UInt8) :-> Obj (Varying 'Z UInt8))
  loop = Pilot.id
  k :: E repr (Obj (Varying ('S 'Z) UInt8) :-> Obj (Varying ('S 'Z) UInt8))
  k = Pilot.id

-- | Here's an integral.
example_6 :: E repr
  (Obj (Constant UInt8) :-> Obj (Varying 'Z UInt8) :-> Obj (Varying ('S 'Z) UInt8))
example_6 = fun $ \c -> fun $ \f ->
  let loop = lift Z_Rep <@> plus_u8 <@> f
  in  knot (Tied (S_Rep Z_Rep)) <@> loop <@> Pilot.id <@> c

-- | [42, 42 ..]
example_7 :: E repr (Obj (Varying 'Z UInt8))
example_7 = lift Z_Rep <@> u8 42

example_8 :: NatRep n -> E repr
  (Obj (Varying n UInt8) :-> Obj (Varying n UInt8) :-> Obj (Varying n UInt8))
example_8 nrep = lift nrep <@> plus_u8
