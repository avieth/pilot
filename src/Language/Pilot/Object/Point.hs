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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Object.Point
  ( Type (..)
  , TypeRep (..)
  , decEq

  , SomeSignednessRep (..)
  , SomeWidthRep (..)
  , SomeTypeRep (..)

  , integer_t
  , bytes_t
  , product_t
  , sum_t

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

  , signed_t
  , unsigned_t

  ) where

import Prelude hiding (Bool, Either, Maybe)
import Data.List (intercalate)

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

instance TestEquality WidthRep where
  testEquality W_One_r   W_One_r   = Just Refl
  testEquality W_Two_r   W_Two_r   = Just Refl
  testEquality W_Four_r  W_Four_r  = Just Refl
  testEquality W_Eight_r W_Eight_r = Just Refl
  testEquality _         _         = Nothing

instance Represented Width where
  type Rep Width = WidthRep

instance Known 'W_One_t where
  known _ = W_One_r

instance Known 'W_Two_t where
  known _ = W_Two_r

instance Known 'W_Four_t where
  known _ = W_Four_r

instance Known 'W_Eight_t where
  known _ = W_Eight_r

data SomeWidthRep where
  SomeWidthRep :: WidthRep w -> SomeWidthRep

-- | Useful for defining Eq and Ord instances on SomeWidthRep
widthRepInt :: forall w . WidthRep w -> Prelude.Int
widthRepInt W_One_r = 1
widthRepInt W_Two_r = 2
widthRepInt W_Four_r = 4
widthRepInt W_Eight_r = 8

instance Eq SomeWidthRep where
  SomeWidthRep w1 == SomeWidthRep w2 = widthRepInt w1 == widthRepInt w2

instance Ord SomeWidthRep where
  SomeWidthRep w1 `compare` SomeWidthRep w2 = widthRepInt w1 `compare` widthRepInt w2

instance Show SomeWidthRep where
  show (SomeWidthRep W_One_r) = "1 byte"
  show (SomeWidthRep W_Two_r) = "2 bytes"
  show (SomeWidthRep W_Four_r) = "4 bytes"
  show (SomeWidthRep W_Eight_r) = "8 bytes"

data Signedness where
  Signed_t   :: Signedness
  Unsigned_t :: Signedness

data SignednessRep (s :: Signedness) where
  Signed_r   :: SignednessRep 'Signed_t
  Unsigned_r :: SignednessRep 'Unsigned_t

instance TestEquality SignednessRep where
  testEquality Signed_r   Signed_r   = Just Refl
  testEquality Unsigned_r Unsigned_r = Just Refl
  testEquality _          _          = Nothing

signed_t :: SignednessRep 'Signed_t
signed_t = Signed_r

unsigned_t :: SignednessRep 'Unsigned_t
unsigned_t = Unsigned_r

instance Represented Signedness where
  type Rep Signedness = SignednessRep

instance Known 'Signed_t where
  known _ = Signed_r

instance Known 'Unsigned_t where
  known _ = Unsigned_r

data SomeSignednessRep where
  SomeSignednessRep :: SignednessRep s -> SomeSignednessRep

instance Eq SomeSignednessRep where
  SomeSignednessRep Unsigned_r == SomeSignednessRep Unsigned_r = True
  SomeSignednessRep Signed_r   == SomeSignednessRep Signed_r   = True
  SomeSignednessRep _          == SomeSignednessRep _          = False

instance Ord SomeSignednessRep where
  SomeSignednessRep Unsigned_r `compare` SomeSignednessRep Unsigned_r = EQ
  SomeSignednessRep Signed_r   `compare` SomeSignednessRep Signed_r   = EQ
  SomeSignednessRep Signed_r   `compare` SomeSignednessRep Unsigned_r = LT
  SomeSignednessRep Unsigned_r `compare` SomeSignednessRep Signed_r   = GT

instance Show SomeSignednessRep where
  show (SomeSignednessRep Unsigned_r) = "unsigned"
  show (SomeSignednessRep Signed_r)   = "signed"

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

decEq :: DecEq TypeRep

decEq (Integer_r s w) (Integer_r s' w') = case testEquality s s' of
  Nothing -> Nothing
  Just Refl -> case testEquality w w' of
    Nothing -> Nothing
    Just Refl -> Just Refl

decEq (Bytes_r w) (Bytes_r w') = case testEquality w w' of
  Nothing -> Nothing
  Just Refl -> Just Refl

decEq (Product_r ps) (Product_r qs) = case testEquality ps qs of
  Nothing -> Nothing
  Just Refl -> Just Refl

decEq (Sum_r ss) (Sum_r ts) = case testEquality ss ts of
  Nothing -> Nothing
  Just Refl -> Just Refl

decEq _ _ = Nothing

instance TestEquality TypeRep where
  testEquality = decEq

integer_t :: SignednessRep s -> WidthRep w -> TypeRep ('Integer_t s w)
integer_t = Integer_r

bytes_t :: WidthRep w -> TypeRep ('Bytes_t w)
bytes_t = Bytes_r

product_t :: All TypeRep fields -> TypeRep ('Product_t fields)
product_t = Product_r

sum_t :: All TypeRep fields -> TypeRep ('Sum_t fields)
sum_t = Sum_r

instance Represented Type where
  type Rep Type = TypeRep

instance (Known s, Known w) => Known ('Integer_t s w) where
  known _ = Integer_r (known (Proxy :: Proxy s)) (known (Proxy :: Proxy w))

instance Known w => Known ('Bytes_t w) where
  known _ = Bytes_r (known (Proxy :: Proxy w))

instance Known ('Product_t '[]) where
  known _ = Product_r All

instance Known ('Sum_t '[]) where
  known _ = Sum_r All

instance (Known t, Known ('Product_t ts)) => Known ('Product_t (t ': ts)) where
  known _ = case known (Proxy :: Proxy ('Product_t ts)) of
    Product_r fields -> Product_r (And (known (Proxy :: Proxy t)) fields)

instance (Known t, Known ('Sum_t ts)) => Known ('Sum_t (t ': ts)) where
  known _ = case known (Proxy :: Proxy ('Sum_t ts)) of
    Sum_r variants -> Sum_r (And (known (Proxy :: Proxy t)) variants)

-- | This is useful because it has an Eq and Ord instance. Unlike `decEq` or
-- `testEquality`, it won't actually give you any type-level information, but
-- it allows you to, for instance, use a `TypeRep` as a key in a map or as an
-- element of a set.
data SomeTypeRep where
  SomeTypeRep :: TypeRep t -> SomeTypeRep

instance Eq SomeTypeRep where
  SomeTypeRep a == SomeTypeRep b = Prelude.maybe False (const True) (decEq a b)

instance Ord SomeTypeRep where

  SomeTypeRep (Integer_r s1 w1) `compare` SomeTypeRep (Integer_r s2 w2) =
    (SomeSignednessRep s1, SomeWidthRep w1) `compare` (SomeSignednessRep s2, SomeWidthRep w2)

  SomeTypeRep (Bytes_r w1) `compare` SomeTypeRep (Bytes_r w2) =
    SomeWidthRep w1 `compare` SomeWidthRep w2

  -- Products and sums take their ordering from the ordering on the list of
  -- their fields/variants, under SomeTypeRep.

  SomeTypeRep (Product_r p1) `compare` SomeTypeRep (Product_r p2) =
    allToList SomeTypeRep p1 `compare` allToList SomeTypeRep p2

  SomeTypeRep (Sum_r s1) `compare` SomeTypeRep (Sum_r s2) =
    allToList SomeTypeRep s1 `compare` allToList SomeTypeRep s2

  -- Integer is lowest.
  SomeTypeRep (Integer_r _ _) `compare` SomeTypeRep (Bytes_r _) = LT
  SomeTypeRep (Integer_r _ _) `compare` SomeTypeRep (Product_r _) = LT
  SomeTypeRep (Integer_r _ _) `compare` SomeTypeRep (Sum_r _) = LT

  -- Followed by bytes
  SomeTypeRep (Bytes_r _) `compare` SomeTypeRep (Integer_r _ _) = GT
  SomeTypeRep (Bytes_r _) `compare` SomeTypeRep (Product_r _) = LT
  SomeTypeRep (Bytes_r _) `compare` SomeTypeRep (Sum_r _) = LT

  -- Then product
  SomeTypeRep (Product_r _) `compare` SomeTypeRep (Integer_r _ _) = GT
  SomeTypeRep (Product_r _) `compare` SomeTypeRep (Bytes_r _) = GT
  SomeTypeRep (Product_r _) `compare` SomeTypeRep (Sum_r _) = LT

  SomeTypeRep (Sum_r _) `compare` SomeTypeRep (Integer_r _ _) = GT
  SomeTypeRep (Sum_r _) `compare` SomeTypeRep (Bytes_r _) = GT
  SomeTypeRep (Sum_r _) `compare` SomeTypeRep (Product_r _) = GT

instance Show SomeTypeRep where

  show (SomeTypeRep (Integer_r Unsigned_r W_One_r))   = "uint8"
  show (SomeTypeRep (Integer_r Unsigned_r W_Two_r))   = "uint16"
  show (SomeTypeRep (Integer_r Unsigned_r W_Four_r))  = "uint32"
  show (SomeTypeRep (Integer_r Unsigned_r W_Eight_r)) = "uint64"

  show (SomeTypeRep (Integer_r Signed_r W_One_r))   = "int8"
  show (SomeTypeRep (Integer_r Signed_r W_Two_r))   = "int16"
  show (SomeTypeRep (Integer_r Signed_r W_Four_r))  = "int32"
  show (SomeTypeRep (Integer_r Signed_r W_Eight_r)) = "int64"

  show (SomeTypeRep (Bytes_r W_One_r))   = "word8"
  show (SomeTypeRep (Bytes_r W_Two_r))   = "word16"
  show (SomeTypeRep (Bytes_r W_Four_r))  = "word32"
  show (SomeTypeRep (Bytes_r W_Eight_r)) = "word64"

  show (SomeTypeRep (Product_r ps)) = mconcat
    [ "P["
    , intercalate "," (fmap show terms)
    , "]"
    ]
    where
    terms :: [SomeTypeRep]
    terms = allToList SomeTypeRep ps

  show (SomeTypeRep (Sum_r ss)) = mconcat
    [ "S["
    , intercalate "," (fmap show summands)
    , "]"
    ]
    where
    summands :: [SomeTypeRep]
    summands = allToList SomeTypeRep ss

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
