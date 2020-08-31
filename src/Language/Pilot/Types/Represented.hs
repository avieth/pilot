{-|
Module      : Pilot.Types.Represented
Description : Type family for "represented" kinds.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Language.Pilot.Types.Represented
  ( Represented (..)

  , Known (..)
  , auto

  , DecEq
  , (:~:)(Refl)
  , TestEquality (..)

  , Proxy (..)
  ) where

import Data.Type.Equality ((:~:)(Refl), TestEquality (..))
import qualified Data.Kind as Haskell (Type)
import Data.Functor.Identity (Identity)

import Data.Proxy (Proxy (..))

-- | A kind is "represented" if there is a GADT parameterized on it giving its
-- singleton type. For example
--
-- > data BoolRep (b :: Bool) where
-- >   True_t  :: BoolRep 'True
-- >   False_t :: BoolRep 'False
--
-- There is in theory one and only one such representation for any given type,
-- so a class/type family definition like this makes sense.
class Represented (k :: Haskell.Type) where
  type Rep k :: k -> Haskell.Type

instance Represented Haskell.Type where
  type Rep Haskell.Type = Identity

class Represented k => Known (t :: k) where
  known :: proxy t -> Rep k t

auto :: forall k (t :: k) . Known t => Rep k t
auto = known (Proxy :: Proxy t)

-- | Decidable equality that GHC can be made aware of. Useful for the
-- value-level representations of the type data kind of an EDSL.
type DecEq (f :: k -> Haskell.Type) = forall x y . f x -> f y -> Maybe (x :~: y)
