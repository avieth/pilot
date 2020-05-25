{-|
Module      : Pilot.Types.Fun
Description : Type for first-order functions.
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Pilot.Types.Fun
  ( Sig (..)
  , type (:->)
  , type V
  , type Lift
  , type MapArgs
  , Fun (..)
  , lit
  , unlit
  , fun
  , at
  , Args (..)
  , KnownArgs (..)
  , autoArgs
  , mapArgs
  , traverseArgs
  , apply
  , unapply
  , Saturated (..)
  , saturate
  , eliminate
  ) where

import Prelude hiding (curry, uncurry)
import qualified Data.Kind as Haskell (Type)
import Pilot.Types.Represented

-- We're interested in functions of the form
--
--   expr a_1 -> expr a_2 -> ... -> expr a_n -> expr r
--
-- i.e. first-order functions where all types are in some expr type (types
-- can be of any kind) and where we always know the result type r.
--
-- For an EDSL which does not have function types, Haskell functions of this
-- form are actually still useful, because it's possible to express a full
-- application of such a function using terms in the EDSL.
--
-- This could be represented with a list of types and a result type, but
-- we prefer to use one just data kind, called Sig.

data Sig t where
  Sig :: [t] -> t -> Sig t

type family Lift (f :: a -> b) (sig :: Sig a) :: Sig b where
  Lift f ('Sig ts r) = 'Sig (MapArgs f ts) (f r)

type family MapArgs (f :: a -> b) (args :: [a]) :: [b] where
  MapArgs f '[]       = '[]
  MapArgs f (a ': as) = f a ': MapArgs f as

infixr 0 :->

type family (:->) (x :: t) (sig :: Sig t) :: Sig t where
  (:->) t ('Sig ts r) = 'Sig (t ': ts) r

type V x = 'Sig '[] x

-- Using Sig, Lift, :->, and V, we can write first-order functions in a somewhat
-- reasonable/ergonomic way
--
--     Lift Maybe (Bool :-> Char :-> () :-> V Int)
--   ~ 'Sig '[Maybe Bool, Maybe Char, Maybe ()] (Maybe Int)
--
-- corresponding to the first order Haskell function `Bool -> Char -> () -> Int`

data Fun expr sig where
  Lit :: expr r -> Fun expr ('Sig '[] r)
  Fun :: (expr t -> Fun expr ('Sig ts r)) -> Fun expr ('Sig (t ': ts) r)

lit :: expr r -> Fun expr ('Sig '[] r)
lit = Lit

unlit :: Fun expr ('Sig '[] r) -> expr r
unlit (Lit r) = r

fun :: (expr t -> Fun expr ('Sig ts r)) -> Fun expr ('Sig (t ': ts) r)
fun = Fun

at :: Fun expr ('Sig (t ': ts) r) -> expr t -> Fun expr ('Sig ts r)
at (Fun k) t = k t

data Args (expr :: domain -> Haskell.Type) (ts :: [domain]) where
  Args :: Args expr '[]
  Arg  :: expr t -> Args expr ts -> Args expr (t ': ts)

class KnownArgs (args :: [k]) where
  inferArgs :: proxy args -> Args (Rep k) args

instance KnownArgs '[] where
  inferArgs _ = Args

instance (Auto arg, KnownArgs args) => KnownArgs (arg ': args) where
  inferArgs _ = Arg auto (inferArgs (Proxy :: Proxy args))

autoArgs :: forall (args :: [k]) . KnownArgs args => Args (Rep k) args
autoArgs = inferArgs (Proxy :: Proxy args)

mapArgs :: (forall x . f x -> g x) -> Args f ts -> Args g ts
mapArgs _ Args         = Args
mapArgs h (Arg t args) = Arg (h t) (mapArgs h args)

traverseArgs
  :: (Applicative m)
  => (forall t . f t -> m (g t))
  -> Args f ts
  -> m (Args g ts)
traverseArgs h Args         = pure Args
traverseArgs h (Arg t args) = Arg <$> h t <*> traverseArgs h args

-- | Full application (all arguments)
apply :: Fun expr ('Sig ts r) -> Args expr ts -> expr r
apply (Lit r) Args         = r
apply (Fun f) (Arg t args) = apply (f t) args

-- | Needs a better name. It's sort of like the inverse of 'apply', except
-- that you must give a proxy for the arguments, so that we have something to
-- match on to reveal the structure.
unapply :: Args proxy ts -> (Args expr ts -> expr r) -> Fun expr ('Sig ts r)
unapply Args         k = Lit (k Args)
unapply (Arg _ args) k = Fun $ \a -> unapply args (\args' -> k (Arg a args'))

data Saturated expr r where
  Saturated :: Fun expr ('Sig ts r) -> Args expr ts -> Saturated expr r

saturate :: Fun expr ('Sig ts r) -> Args expr ts -> Saturated expr r
saturate = Saturated

eliminate :: Saturated expr r -> expr r
eliminate (Saturated f args) = apply f args
