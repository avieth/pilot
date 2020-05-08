{-|
Module      : Pilot.EDSL.Point
Description : The pointwise EDSL.
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

module Pilot.EDSL.Point
  ( Type (..)
  , TypeRep (..)
  , ExprF (..)
  , All (..)
  , Any (..)
  , Selector (..)
  , Cases (..)

  , IntegerLiteral (..)

  , Signedness (..)
  , Width (..)
  , SignednessRep (..)
  , WidthRep (..)

  , UInt8
  , uint8_t
  , UInt16
  , uint16_t
  , UInt32
  , uint32_t
  , UInt64
  , uint64_t
  , Int8
  , int8_t
  , Int16
  , int16_t
  , Int32
  , int32_t
  , Int64
  , int64_t

  , Unit
  , unit_t
  , Void
  , void_t
  , Boolean
  , boolean_t
  , Pair
  , pair_t
  , maybe_t
  ) where

import Prelude hiding (Maybe, Either)
import qualified Data.Int as Haskell (Int8, Int16, Int32, Int64)
import qualified Data.Kind as Haskell (Type)
import Data.Typeable (Typeable)
import qualified Data.Word as Haskell (Word8, Word16, Word32, Word64)

-- | Types for the pointwise EDSL: various numeric types, with finite sums and
-- products. As usual, the empty product is unit, and the empty sum is void.
-- There is no boolean type; it can be expressed as a sum of units.
data Type where
  Integer  :: Signedness -> Width -> Type
  Rational :: Type
  Product  :: [Type] -> Type
  Sum      :: [Type] -> Type

data Signedness where
  Signed   :: Signedness
  Unsigned :: Signedness

data SignednessRep (s :: Signedness) where
  Signed_t :: SignednessRep 'Signed
  Unsigned_t :: SignednessRep 'Unsigned

-- | Width in bits.
data Width where
  Eight     :: Width
  Sixteen   :: Width
  ThirtyTwo :: Width
  SixtyFour :: Width

data WidthRep (t :: Width) where
  Eight_t     :: WidthRep 'Eight
  Sixteen_t   :: WidthRep 'Sixteen
  ThirtyTwo_t :: WidthRep 'ThirtyTwo
  SixtyFour_t :: WidthRep 'SixtyFour

data IntegerLiteral (signedness :: Signedness) (width :: Width) where

  UInt8  :: Haskell.Word8  -> IntegerLiteral Unsigned Eight
  UInt16 :: Haskell.Word16 -> IntegerLiteral Unsigned Sixteen
  UInt32 :: Haskell.Word32 -> IntegerLiteral Unsigned ThirtyTwo
  UInt64 :: Haskell.Word64 -> IntegerLiteral Unsigned SixtyFour

  Int8  :: Haskell.Int8  -> IntegerLiteral Signed Eight
  Int16 :: Haskell.Int16 -> IntegerLiteral Signed Sixteen
  Int32 :: Haskell.Int32 -> IntegerLiteral Signed ThirtyTwo
  Int64 :: Haskell.Int64 -> IntegerLiteral Signed SixtyFour

-- | Value-level representation of 'Type' data kinds.
data TypeRep (t :: Type) where

  Integer_t  :: SignednessRep signedness
             -> WidthRep width
             -> TypeRep ('Integer sigedness width)
  Rational_t :: TypeRep 'Rational

  Product_t :: Typeable tys => All TypeRep tys -> TypeRep ('Product tys)
  Sum_t     :: Typeable tys => All TypeRep tys -> TypeRep ('Sum tys)

-- | Expressions in the pointwise EDSL. The `f` parameter represents the
-- _target_ or object language, for instance generated C code, or an in-Haskell
-- representation.
--
data ExprF (f :: Type -> Haskell.Type) (t :: Type) where

  IntroInteger :: TypeRep ('Integer signedness width)
               -> IntegerLiteral signedness width
               -> ExprF f ('Integer signedness width)

  IntroProduct :: TypeRep ('Product types)
               -> All f types
               -> ExprF f ('Product types)

  IntroSum     :: TypeRep ('Sum types)
               -> Any f types
               -> ExprF f ('Sum types)

  ElimProduct :: TypeRep ('Product types)
              -> TypeRep r
              -> Selector f types r
              -> f ('Product types)
              -> ExprF f r

  ElimSum     :: TypeRep ('Sum types)
              -> TypeRep r
              -> Cases f types r
              -> f ('Sum types)
              -> ExprF f r

data All (f :: k -> Haskell.Type) (ts :: [k]) where
  AllF :: All f '[]
  AndF :: f t -> All f ts -> All f (t ': ts)

data Any (f :: k -> Haskell.Type) (ts :: [k]) where
  AnyF :: f t -> Any f (t ': ts)
  OrF  :: Any f ts -> Any f (t ': ts)

data Selector (f :: k -> Haskell.Type) (ts :: [k]) (r :: k) where
  AnyC :: (f t -> f r) -> Selector f (t ': ts) r
  OrC  :: Selector f ts r -> Selector f (t ': ts) r

data Cases (f :: k -> Haskell.Type) (ts :: [k]) (r :: k) where
  AllC :: Cases f '[] r
  AndC :: (f t -> f r)
       -> Cases f ts r
       -> Cases f (t ': ts) r

-- Some examples of 'Type's and 'TypeRep's

type UInt8  = 'Integer Unsigned Eight
type UInt16 = 'Integer Unsigned Sixteen
type UInt32 = 'Integer Unsigned ThirtyTwo
type UInt64 = 'Integer Unsigned SixtyFour

type Int8  = 'Integer Signed Eight
type Int16 = 'Integer Signed Sixteen
type Int32 = 'Integer Signed ThirtyTwo
type Int64 = 'Integer Signed SixtyFour

uint8_t :: TypeRep UInt8
uint8_t = Integer_t Unsigned_t Eight_t

uint16_t :: TypeRep UInt16
uint16_t = Integer_t Unsigned_t Sixteen_t

uint32_t :: TypeRep UInt32
uint32_t = Integer_t Unsigned_t ThirtyTwo_t

uint64_t :: TypeRep UInt64
uint64_t = Integer_t Unsigned_t SixtyFour_t

int8_t :: TypeRep Int8
int8_t = Integer_t Signed_t Eight_t

int16_t :: TypeRep Int16
int16_t = Integer_t Signed_t Sixteen_t

int32_t :: TypeRep Int32
int32_t = Integer_t Signed_t ThirtyTwo_t

int64_t :: TypeRep Int64
int64_t = Integer_t Signed_t SixtyFour_t

type Unit = 'Product '[]

unit_t :: TypeRep Unit
unit_t = Product_t AllF

type Void = 'Sum '[]

void_t :: TypeRep Void
void_t = Sum_t AllF

type Boolean = 'Sum '[ Unit, Unit ]

boolean_t :: TypeRep Boolean
boolean_t = Sum_t (AndF unit_t $ AndF unit_t $ AllF)

type Pair (s :: Type) (t :: Type) = 'Product '[ s, t]

pair_t :: (Typeable s, Typeable t) => TypeRep s -> TypeRep t -> TypeRep (Pair s t)
pair_t s t = Product_t (AndF s $ AndF t $ AllF)

type Maybe (t :: Type) = 'Sum '[ Unit, t ]

maybe_t :: Typeable t => TypeRep t -> TypeRep (Maybe t)
maybe_t t = Sum_t (AndF unit_t $ AndF t $ AllF)

type Either (s :: Type) (t :: Type) = 'Sum '[ s, t ]

either_t :: (Typeable s, Typeable t) => TypeRep s -> TypeRep t -> TypeRep (Either s t)
either_t s t = Sum_t (AndF s $ AndF t $ AllF)

-- NB: we cannot have the typical Haskell list type. Recursive types are not
-- allowed.
