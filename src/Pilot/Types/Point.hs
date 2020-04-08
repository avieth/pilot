{-|
Module      : Pilot.Types.Point
Description : Definition of the point kind.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Pilot.Types.Point where

import qualified Data.Kind as Kind (Type)

data Kind (ty :: k) where
  Arrow :: Kind ty -> Kind ty -> Kind ty
  Value :: ty -> Kind ty

infixr 0 :->
type (:->) = Arrow

type T = Value

-- | Those members of a
data Val (target :: Kind ty -> Kind.Type) (t :: ty) where
  Val :: target (T t) -> Val target t

data Fun (target :: Kind ty -> Kind.Type) s t where
  Fun :: target (s :-> t) -> Fun target s t
