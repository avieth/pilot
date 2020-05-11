{-|
Module      : Pilot.EDSL.Lifted
Description : The point EDSL, "lifted" to Haskell types.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Pilot.EDSL.Lifted
  ( Lifted (..)
  , Embed (..)
  , lift
  , unlift
  ) where

import qualified Data.Kind as Haskell (Type)
import Pilot.EDSL.Point (Expr (..))
import Pilot.Types.Represented

-- | "Lift" an EDSL's domain into "Hask". This is any expression in some EDSL
-- with a `Haskell.Type` standing in for the type in the underlying domain, by
-- way of the 'EmbedT' family of the 'Embed' typeclass.
--
-- This is one way to give nominal types to an otherwise structurally-typed
-- EDSL. Even if two different `Haskell.Type`s have the same representation in
-- the underlying domain (defined by the 'Embed' class), they are nevertheless
-- distinct types in the 'Lifted' variant.
--
-- this is sort of analagous to Haskell's notion of "lifted" types but doesn't
-- carry the same _|_ semantics. Maybe a better name is needed?
newtype Lifted
  (exprF)
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> domain -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Haskell.Type) = Lifted
  { getLifted :: Expr exprF f val s (EmbedT domain t) }

lift :: Expr exprF f val s (EmbedT domain t) -> Lifted exprF f val s t
lift = Lifted

unlift :: Lifted exprF f val s t -> Expr exprF f val s (EmbedT domain t)
unlift = getLifted

-- | Gives a representation in `domain` for a Haskell type.
class ( Represented domain ) => Embed (domain :: Haskell.Type) (t :: Haskell.Type) where
  type EmbedT domain t :: domain
  embedT :: proxy domain -> proxy t -> Rep domain (EmbedT domain t)
