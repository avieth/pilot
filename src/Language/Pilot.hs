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
  , Form
  , E
  , Repr.Repr
  , Repr.Interprets

  -- * Meta-language constructions
  , Meta_k
  , Object_k
  , Meta.Obj
  , Meta.Terminal
  , type (Meta.:->)
  , type (Meta.:*)
  , Repr.fun
  , Repr.app
  , (Repr.<@>)
  , Repr.identity
  , Repr.compose
  , (Repr.<.>)
  , Repr.const
  , Repr.flip
  , Repr.curry
  , Repr.uncurry

  , Repr.product
  , Repr.terminal
  , (Repr.<&)
  , (Repr.&>)
  , metafst
  , metasnd

  -- * Object-language constructions
  , Point_k
  , Object.Constant
  , Object.Varying
  , Object.Program

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

  , Meta.object_t
  , (Meta..->)
  , (Meta..*)
  , Meta.arrow_t
  , Meta.product_t
  , Meta.terminal_t
  , Object.varying_t
  , Object.constant_t
  , Object.uint8_t
  , Object.uint16_t
  , Object.uint32_t
  , Object.uint64_t
  , Object.int8_t
  , Object.int16_t
  , Object.int32_t
  , Object.int64_t
  , Object.cmp_t
  , Object.maybe_t
  , Object.either_t
  , Object.pair_t
  , Object.bool_t
  , Object.void_t
  , Object.unit_t

  , Object.Width (..)
  , Object.Signedness (..)

  , Object.let_
  , Object.local
  , Object.let_auto
  , Object.local_auto

  , Object.u8
  , Object.u16
  , Object.u32
  , Object.u64
  , Object.i8
  , Object.i16
  , Object.i32
  , Object.i64
  , Object.add
  , (Object.+)
  , Object.subtract
  , (Object.-)
  , Object.multiply
  , (Object.*)
  , Object.divide
  , Object.div
  , Object.modulo
  , Object.mod
  , Object.negate
  , Object.neg
  , Object.abs
  , Object.compare_auto
  , Object.cmp
  , Object.and
  , Object.or
  , Object.xor
  , Object.complement
  , Object.shiftl
  , Object.shiftr

  , (Object.>)
  , (Object.>=)
  , (Object.<)
  , (Object.<=)
  , (Object.==)
  , (Object./=)

  , Object.Cast (..)
  , Object.cast
  , Object.Wider (..)

  , Object.bundle
  , Object.project
  , Object.choose
  , Object.match

  , Object.shift
  , Object.drop
  , Object.shift_auto
  , Object.drop_auto
  , Object.map
  , Object.map_auto
  , Object.constant
  , Object.constant_auto
  , Object.knot
  , Object.knot_auto
  , Object.Knot (..)
  , Object.Fields (..)
  , Object.Variant (..)
  , Object.Selector (..)
  , Object.Cases (..)

  , Object.unit
  , Object.absurd
  , Object.pair
  , Object.pair_auto
  , Object.fst
  , Object.fst_auto
  , Object.snd
  , Object.snd_auto
  , Object.true
  , Object.false
  , Object.if_then_else
  , ifThenElse
  , Object.land
  , (Object.&&)
  , Object.lor
  , (Object.||)
  , Object.lnot
  , Object.implies
  , (Object.==>)
  , Object.maybe
  , Object.just
  , Object.nothing
  , Object.isJust
  , Object.isNothing

  -- ** Object-language IO
  , Object.prog_map
  , Object.prog_pure
  , Object.prog_ap
  , Object.prog_join
  , Object.prog_bind
  , (Object.>>=)

  -- * General-purpose types
  , module Types
  , Nat (..)
  , Known (..)
  , auto
  , NatRep (..)

  , type Object.Vector
  , Object.MapImage (..)
  , Object.KnownMapPreImage (..)
  , Object.vectorMapImage
  , Object.vector_t

  -- * Prelude re-exports
  , (Category..)
  , Category.id
  , Category.Category
  , Prelude.Functor
  , Prelude.Applicative
  , Prelude.Monad
  -- So that when using RebindableSyntax, importing Language.Pilot will make
  -- integer literals work.
  , Prelude.fromInteger
  , (Prelude.$)
  , Prelude.undefined

  ) where

import Control.Category as Category (Category, (.), id)
import qualified Language.Pilot.Repr as Repr
import qualified Language.Pilot.Meta as Meta
import qualified Language.Pilot.Object as Object
import qualified Language.Pilot.Object.Point as Object.Point
import Language.Pilot.Types as Types

type Point t = Meta.Obj (Object.Constant t)
type Stream n t = Meta.Obj (Object.Varying n t)
type Form = Object.Form

type E f val t = Repr.E Form f val t

type Meta_k = Meta.Type
type Object_k = Object.Type
type Point_k = Object.Point.Type

-- | meta-language fst
metafst :: Monad f => Repr.Repr f val (s Meta.:* t) -> Repr.Repr f val s
metafst = Repr.fst

-- | Meta-langauge snd
metasnd :: Monad f => Repr.Repr f val (s Meta.:* t) -> Repr.Repr f val t
metasnd = Repr.snd

-- | For rebindable syntax
ifThenElse :: Known r
           => E f val (Point Object.Bool)
           -> E f val (Point r)
           -> E f val (Point r)
           -> E f val (Point r)
ifThenElse = Object.if_then_else
