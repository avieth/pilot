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
{-# LANGUAGE TypeFamilies #-}

module Language.Pilot.Meta
  ( Type (..)
  , Obj
  , Terminal
  , type (:->)
  , type (:*)

  , TypeRep (..)
  , object_t
  , arrow_t
  , product_t
  , terminal_t
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

data TypeRep (rep :: obj -> Hask) (t :: Type obj) where
  Object_r   :: rep t -> TypeRep rep ('Object_t t)
  Arrow_r    :: TypeRep rep s -> TypeRep rep t -> TypeRep rep ('Arrow_t s t)
  Product_r  :: TypeRep rep s -> TypeRep rep t -> TypeRep rep ('Product_t s t)
  Terminal_r :: TypeRep rep 'Terminal_t

instance Represented t => Represented (Type t) where
  type Rep (Type t) = TypeRep (Rep t)

object_t :: rep t -> TypeRep rep ('Object_t t)
object_t orep = Object_r orep

terminal_t :: TypeRep rep 'Terminal_t
terminal_t = Terminal_r

arrow_t :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :-> t)
arrow_t = Arrow_r

product_t :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :* t)
product_t = Product_r
