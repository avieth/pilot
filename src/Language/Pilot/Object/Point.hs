{-|
Module      : Language.Pilot.Object.Point
Description : Definition of point types in the object language.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Pilot.Object.Point
  ( Type (..)
  , TypeRep (..)

  , Product
  , Sum

  , UInt8
  , UInt16
  , UInt32
  , UInt64
  , uint8_t
  , uint16_t
  , uint32_t
  , uint64_t
  , Int8
  , Int16
  , Int32
  , Int64
  , int8_t
  , int16_t
  , int32_t
  , int64_t
  , Word8
  , Word16
  , Word32
  , Word64
  , word8_t
  , word16_t
  , word32_t
  , word64_t
  , Unit
  , unit_t
  , Void
  , void_t
  , Bool
  , bool_t
  , Pair
  , pair_t
  , Either
  , either_t
  , Maybe
  , maybe_t
  , Cmp
  , cmp_t

  , Width (..)
  , WidthRep (..)
  , Signedness (..)
  , SignednessRep (..)

  ) where

import Prelude hiding (Bool, Either, Maybe)

import Language.Pilot.Types

data Width where
  W_One_t   :: Width
  W_Two_t   :: Width
  W_Four_t  :: Width
  W_Eight_t :: Width

data WidthRep (w :: Width) where
  W_One_r   :: WidthRep 'W_One_t
  W_Two_r   :: WidthRep 'W_Two_t
  W_Four_r  :: WidthRep 'W_Four_t
  W_Eight_r :: WidthRep 'W_Eight_t

instance Represented Width where
  type Rep Width = WidthRep

data Signedness where
  Signed_t   :: Signedness
  Unsigned_t :: Signedness

data SignednessRep (s :: Signedness) where
  Signed_r   :: SignednessRep 'Signed_t
  Unsigned_r :: SignednessRep 'Unsigned_t

instance Represented Signedness where
  type Rep Signedness = SignednessRep

-- | This data kind gives all of the "point" types: finite sums and products,
-- along with numeric and bitwise base types.
data Type where

  -- TODO may want to include fractional numbers.
  Integer_t :: Signedness -> Width -> Type
  Bytes_t :: Width -> Type

  -- The empty product is unit, the empty sum is void.

  Product_t :: [Type] -> Type
  Sum_t     :: [Type] -> Type

data TypeRep (t :: Type) where
  Integer_r :: SignednessRep s -> WidthRep w -> TypeRep ('Integer_t s w)
  Bytes_r   :: WidthRep w -> TypeRep ('Bytes_t w)
  Product_r :: All TypeRep fields -> TypeRep ('Product_t fields)
  Sum_r     :: All TypeRep fields -> TypeRep ('Sum_t fields)

instance Represented Type where
  type Rep Type = TypeRep

type Product ts = 'Product_t ts
type Sum ts = 'Sum_t ts

type UInt8  = 'Integer_t 'Unsigned_t 'W_One_t
type UInt16 = 'Integer_t 'Unsigned_t 'W_Two_t
type UInt32 = 'Integer_t 'Unsigned_t 'W_Four_t
type UInt64 = 'Integer_t 'Unsigned_t 'W_Eight_t

uint8_t :: TypeRep UInt8
uint8_t = Integer_r Unsigned_r W_One_r

uint16_t :: TypeRep UInt16
uint16_t = Integer_r Unsigned_r W_Two_r

uint32_t :: TypeRep UInt32
uint32_t = Integer_r Unsigned_r W_Four_r

uint64_t :: TypeRep UInt64
uint64_t = Integer_r Unsigned_r W_Eight_r

type Int8  = 'Integer_t 'Signed_t 'W_One_t
type Int16 = 'Integer_t 'Signed_t 'W_Two_t
type Int32 = 'Integer_t 'Signed_t 'W_Four_t
type Int64 = 'Integer_t 'Signed_t 'W_Eight_t

int8_t :: TypeRep Int8
int8_t = Integer_r Signed_r W_One_r

int16_t :: TypeRep Int16
int16_t = Integer_r Signed_r W_Two_r

int32_t :: TypeRep Int32
int32_t = Integer_r Signed_r W_Four_r

int64_t :: TypeRep Int64
int64_t = Integer_r Signed_r W_Eight_r

type Word8  = 'Bytes_t 'W_One_t
type Word16 = 'Bytes_t 'W_Two_t
type Word32 = 'Bytes_t 'W_Four_t
type Word64 = 'Bytes_t 'W_Eight_t

word8_t :: TypeRep Word8
word8_t = Bytes_r W_One_r

word16_t :: TypeRep Word16
word16_t = Bytes_r W_Two_r

word32_t :: TypeRep Word32
word32_t = Bytes_r W_Four_r

word64_t :: TypeRep Word64
word64_t = Bytes_r W_Eight_r

type Unit = 'Product_t '[]
type Void = 'Sum_t '[]

unit_t :: TypeRep Unit
unit_t = Product_r All

void_t :: TypeRep Void
void_t = Sum_r All

type Pair a b = 'Product_t '[ a, b ]

pair_t :: TypeRep a -> TypeRep b -> TypeRep (Pair a b)
pair_t arep brep = Product_r (And arep (And brep All))

type Bool = 'Sum_t '[ Unit, Unit ]

bool_t :: TypeRep Bool
bool_t = Sum_r (And unit_t (And unit_t All))

-- | Comparison type, to replace the classic -1, 0, 1 motif with a proper
-- algebraic type.
--
-- Cmp = LT | EQ | GT
type Cmp = 'Sum_t '[ Unit, Unit, Unit ]

cmp_t :: TypeRep Cmp
cmp_t = Sum_r (And unit_t (And unit_t (And unit_t All)))

type Maybe a = 'Sum_t '[ Unit, a ]
type Either a b = 'Sum_t '[ a, b ]

maybe_t :: TypeRep a -> TypeRep (Maybe a)
maybe_t arep = Sum_r (And unit_t (And arep All))

either_t :: TypeRep a -> TypeRep b -> TypeRep (Either a b)
either_t arep brep = Sum_r (And arep (And brep All))
