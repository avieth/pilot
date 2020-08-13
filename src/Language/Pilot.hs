{-|
Module      : Language.Pilot
Description :
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Pilot
  ( Point
  , Stream
  , E
  , formal_e
  , F
  , formal_f
  , from_e

  , Meta_k
  , Object_k
  , Meta.Obj
  , Meta.Terminal
  , type (Meta.:->)
  , type (Meta.:*)
  , Meta.fun
  , Meta.app
  , (Meta.<@>)
  , Meta.id
  , Meta.compose
  , (Meta.<.>)
  , Meta.const
  , Meta.flip
  , Meta.curry
  , Meta.uncurry

  , Meta.product
  , Meta.tuple
  , Meta.terminal
  , Meta.fst
  , Meta.snd
  , (Meta.<&)
  , (Meta.&>)

  , Point_k
  , Object.Constant
  , Object.Varying

  , Object.UInt8
  , Object.UInt16
  , Object.UInt32
  , Object.UInt64
  , Object.Int8
  , Object.Int16
  , Object.Int32
  , Object.Int64
  , Object.Word8
  , Object.Word16
  , Object.Word32
  , Object.Word64
  , Object.Product
  , Object.Sum
  , Object.Unit
  , Object.Void
  , Object.Bool
  , Object.Cmp
  , Object.Maybe
  , Object.Pair
  , Object.Either

  , Object.Width (..)
  , Object.Signedness (..)

  , Object.shift
  , Object.drop
  , Object.lift
  , Object.lift_
  , Object.knot
  , Object.Knot (..)
  , Object.Lift (..)
  , Object.Fields (..)
  , Object.Variant (..)
  , Object.Selector (..)
  , Object.Cases (..)

  , Object.unit
  , Object.absurd
  , Object.pair
  , Object.true
  , Object.false
  , Object.if_then_else
  , Object.maybe
  , Object.just
  , Object.nothing

  , Object.u8
  , Object.i8
  , Object.plus
  , Object.plus_u8

  , Object.AutoLift
  , Nat (..)
  , Auto
  , repVal
  , NatRep (..)

  ) where

import Language.Pilot.Expr
import qualified Language.Pilot.Meta as Meta
import qualified Language.Pilot.Object as Object
import Language.Pilot.Types

type Point t = Meta.Obj (Object.Constant t)
type Stream n t = Meta.Obj (Object.Varying n t)

type E repr = Expr (Meta.Form Object.Form) repr

type Meta_k = Meta.Type
type Object_k = Object.Type
type Point_k = Object.Point


