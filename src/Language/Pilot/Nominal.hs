{-|
Module      : Language.Pilot.Nominal
Description : Nominal types over an EDSL
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

An EDSL in the style used in pilot has structural sum and product types. This
module defines a kind of superstructure over such an EDSL in which any Haskell
(nominal) type may be used as a type in the EDSL, by way of a type family which
defines its structure. This gives a style which is essentially the same as--but
certainly more cumbersome than--typical Haskell type definitions. Instead of
defining

> data T = A | B | C Int

we would define

> data T
> instance Nominal T (Meta.Type Object.Type) where
>   type Structure T (Meta.Type Object.Type) = Obj (Constant (Sum '[ Unit, Unit, Int ]))

The empty data declaration defines the new nominal type, and the definition of
its structure is in a separate clause.

One key drawback of this style is that there is no way to hide the structure of
a type--as we would normally do by way of carefully chosen module exports--for
if it can be used/typechecked, then the programmer must have access to its
  structural definition.

-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Pilot.Nominal
  ( Nominal (..)
  , In (..)
  , nominal
  , structural
  ) where

import Language.Pilot.Types

class ( Represented domain ) => Nominal (domain :: Hask) (t :: Hask) where
  type Structure domain t :: domain
  nominalRep :: proxy domain -> proxy t -> Rep domain (Structure domain t)

data In (f :: domain -> Hask) (t :: Hask) where
  In :: f (Structure domain t) -> In f t

nominal :: f (Structure domain t) -> In f t
nominal = In

structural :: In f t -> f (Structure domain t)
structural (In f) = f
