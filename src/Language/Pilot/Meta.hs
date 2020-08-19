{-|
Module      : Language.Pilot.Meta
Description : Definition of meta-language types.
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

module Language.Pilot.Meta
  ( Type (..)
  , Obj
  , Terminal
  , type (:->)
  , type (:*)
  ) where

import Language.Pilot.Types

-- | This data kind adds--to some other kind--products, exponentials, and a
-- terminal object. Suggestive of Cartesian closed category.
data Type (t :: Hask) where
  Object_t   :: t -> Type t
  Arrow_t    :: Type t -> Type t -> Type t
  Product_t  :: Type t -> Type t -> Type t
  Terminal_t :: Type t

type Obj = 'Object_t

type Terminal = 'Terminal_t

type (:->) = Arrow_t
infixr 0 :->

type (:*) = Product_t
infixr 2 :*
