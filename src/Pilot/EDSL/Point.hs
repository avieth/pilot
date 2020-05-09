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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pilot.EDSL.Point
  ( Expr (..)
  , evalInMonad
  , lift

  , Type (..)
  , TypeRep (..)
  , KnownType (..)

  , ExprF (..)
  , All (..)
  , Any (..)
  , Selector (..)
  , Cases (..)

  , IntegerLiteral (..)

  , Signedness (..)
  , SignednessRep (..)
  , KnownSignedness (..)
  , Width (..)
  , WidthRep (..)
  , KnownWidth (..)

  , UInt8
  , uint8_t
  , uint8
  , UInt16
  , uint16_t
  , uint16
  , UInt32
  , uint32_t
  , uint32
  , UInt64
  , uint64_t
  , uint64
  , Int8
  , int8_t
  , int8
  , Int16
  , int16_t
  , int16
  , Int32
  , int32_t
  , int32
  , Int64
  , int64_t
  , int64

  , plus

  , local

  , Unit
  , unit_t
  , unit
  , Void
  , void_t
  , Boolean
  , boolean_t
  , Pair
  , pair_t
  , pair
  , fst
  , snd
  , Maybe
  , maybe_t
  , just
  , nothing
  , elim_maybe
  , Either
  , either_t
  , left
  , right

  ) where

import Prelude hiding (Maybe, Either, fst, snd)
import Control.Monad (ap, join)
import qualified Data.Int as Haskell (Int8, Int16, Int32, Int64)
import qualified Data.Kind as Haskell (Type)
import Data.Proxy (Proxy (..))
import Data.Typeable (Typeable)
import qualified Data.Word as Haskell (Word8, Word16, Word32, Word64)

-- | The user-facing DSL.
--
-- It must be a monad, with the ST binding type parameter trick. Any pure
-- Haskell computation can be used in this monad of course, and the result is
-- something in the parameter f.
--
-- Intuitively, this type means that, if you know how to elaborate ExprF inside
-- f, then you can get an expression inside f. That's to say, whatever this is,
-- it's built atop ExprF and pure meta-language (Haskell) constructs.
--
-- Idea: to make it a monad, just add an STRef analog, call it Val?
-- ExprF recursive parts can take
--
--   f s (Val s t) -> ...
--
-- then what we want in the continuation in Expr is
--
--   forall x y . ExprF f x y -> f x (Val x y)
--
-- ah but damn, Val actually depends upon f, as you might expect, since this is
-- essentially the representation of the expression.
-- One nice option could be to take 2 params: the monad and the STRef/val type.
--
--   (forall x y . ExprF f val x y -> f val x (val x y)) -> f val s t
--
-- and even beyond that, we still don't want to incur any constraints on f
-- until evaluation time, so we need some sort of free structure over it.
--
-- f represents the interpretation. Think of it as code generation or something.
-- s represents the binding context. It's the ST-style parameter used to ensure
-- that what you do in one Expr cannot come out of that context.
-- val represents object-language values, parameterized by the binding context.
-- t is what you expect; this is a functor.
--
newtype Expr
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Haskell.Type) = Expr
  { getExpr :: (forall x y . ExprF f val x y -> f x (val x y))
            -- ^ Interpret expressions
            -> (forall x y z . (y -> z) -> f x y -> f x z)
            -- ^ fmap
            -> (forall x y . y -> f x y)
            -- ^ pure
            -> (forall x y . f x (f x y) -> f x y)
            -- ^ join
            -> f s t
  }

instance Functor (Expr f val s) where
  fmap f expr = Expr $ \interp map pure join ->
    map f (getExpr expr interp map pure join)

instance Applicative (Expr f val s) where
  pure x = Expr $ \interp map pure' join -> pure' x
  (<*>) = ap

instance Monad (Expr f val s) where
  return = pure
  expr >>= f = Expr $ \interp map pure join ->
    join (map (\x -> getExpr (f x) interp map pure join) (getExpr expr interp map pure join))

lift :: f s t -> Expr f val s t
lift ft = Expr $ \_ _ _ _ -> ft

evalInMonad
  :: forall f val s t.
     ( forall s . Monad (f s) )
  -- TODO use the ST trick later. Not in because I want flexibility for development
  -- => (forall q . Expr f val q t)
  => Expr f val s t
  -> (forall x y . ExprF f val x y -> f x (val x y))
  -> f s t
evalInMonad expr interp = getExpr expr interp fmap pure join

-- Problem with this is the constraint is going to appear in every derived
-- expression but I'd prefer to leave it until interpretation time (runInMonad).
exprF :: forall f val s t . ExprF f val s t -> Expr f val s (val s t)
exprF exprf = Expr $ \f map pure join ->
  let v :: f s (val s t)
      v = f exprf
  in  join (map pure v)

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

class KnownSignedness (s :: Signedness) where
  signednessRep :: proxy s -> SignednessRep s

instance KnownSignedness 'Signed where
  signednessRep _ = Signed_t

instance KnownSignedness 'Unsigned where
  signednessRep _ = Unsigned_t

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

class KnownWidth (w :: Width) where
  widthRep :: proxy w -> WidthRep w

instance KnownWidth 'Eight where
  widthRep _ = Eight_t

instance KnownWidth 'Sixteen where
  widthRep _ = Sixteen_t

instance KnownWidth 'ThirtyTwo where
  widthRep _ = ThirtyTwo_t

instance KnownWidth 'SixtyFour where
  widthRep _ = SixtyFour_t

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

class KnownType (t :: Type) where
  typeRep :: proxy t -> TypeRep t

instance (KnownSignedness signedness, KnownWidth width) => KnownType ('Integer signedness width) where
  typeRep _ = Integer_t (signednessRep (Proxy :: Proxy signedness))
                        (widthRep (Proxy :: Proxy width))

instance KnownType ('Product '[]) where
  typeRep _ = Product_t AllF

instance (Typeable t, Typeable ts, KnownType t, KnownType ('Product ts))
  => KnownType ('Product (t ': ts)) where
  typeRep _ =
    let Product_t theRest = typeRep (Proxy :: Proxy ('Product ts))
    in  Product_t (AndF (typeRep (Proxy :: Proxy t)) theRest)

instance KnownType ('Sum '[]) where
  typeRep _ = Sum_t AllF

instance (Typeable t, Typeable ts, KnownType t, KnownType ('Sum ts))
  => KnownType ('Sum (t ': ts)) where
  typeRep _ =
    let Sum_t theRest = typeRep (Proxy :: Proxy ('Sum ts))
    in  Sum_t (AndF (typeRep (Proxy :: Proxy t)) theRest)

-- | Expressions in the pointwise EDSL. The `f` parameter represents the
-- _target_ or object language, for instance generated C code, or an in-Haskell
-- representation.
--
data ExprF
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Type)
  where

  -- Atomic data

  IntroInteger :: TypeRep ('Integer signedness width)
               -> IntegerLiteral signedness width
               -> ExprF f val s ('Integer signedness width)

  -- TODO more arithmetic and logic stuff

  AddInteger :: TypeRep ('Integer signedness width)
             -> val s ('Integer signedness width)
             -> val s ('Integer signedness width)
             -> ExprF f val s ('Integer signedness width)

  -- TODO safe upcasts
  -- TODO checked downcasts

  -- Compound data: algebraic datatypes

  IntroProduct :: TypeRep ('Product types)
               -> All (val s) types
               -> ExprF f val s ('Product types)

  IntroSum     :: TypeRep ('Sum types)
               -> Any (val s) types
               -> ExprF f val s ('Sum types)

  ElimProduct :: TypeRep ('Product types)
              -> TypeRep r
              -> Selector f val s types r
              -> val s ('Product types)
              -> ExprF f val s r

  ElimSum     :: TypeRep ('Sum types)
              -> TypeRep r
              -> Cases f val s types r
              -> val s ('Sum types)
              -> ExprF f val s r

  -- Explicit binding, so that the programmer may control sharing.
  Local :: TypeRep t
        -> TypeRep r
        -> val s t
        -> (val s t -> Expr f val s (val s r))
        -> ExprF f val s r

data All (f :: k -> Haskell.Type) (ts :: [k]) where
  AllF :: All f '[]
  AndF :: f t -> All f ts -> All f (t ': ts)

data Any (f :: k -> Haskell.Type) (ts :: [k]) where
  AnyF :: f t -> Any f (t ': ts)
  OrF  :: Any f ts -> Any f (t ': ts)

data Selector
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts  :: [k])
  (r   :: k)
  where
  AnyC :: TypeRep t -> (val s t -> Expr f val s (val s r)) -> Selector f val s (t ': ts) r
  OrC  :: Selector f val s ts r -> Selector f val s (t ': ts) r

data Cases
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts  :: [k])
  (r   :: k)
  where
  AllC :: Cases f val s '[] r
  AndC :: (val s t -> Expr f val s (val s r))
       -> Cases f val s ts r
       -> Cases f val s (t ': ts) r

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

unit :: Expr f val s (val s Unit)
unit = exprF $ IntroProduct unit_t AllF

type Void = 'Sum '[]

void_t :: TypeRep Void
void_t = Sum_t AllF

type Boolean = 'Sum '[ Unit, Unit ]

boolean_t :: TypeRep Boolean
boolean_t = Sum_t (AndF unit_t $ AndF unit_t $ AllF)

type Pair (s :: Type) (t :: Type) = 'Product '[ s, t]

pair_t :: (Typeable s, Typeable t) => TypeRep s -> TypeRep t -> TypeRep (Pair s t)
pair_t s t = Product_t (AndF s $ AndF t $ AllF)

pair :: (Typeable a, Typeable b)
     => TypeRep a
     -> TypeRep b
     -> val s a
     -> val s b
     -> Expr f val s (val s (Pair a b))
pair ta tb va vb = exprF $ IntroProduct (pair_t ta tb) (AndF va $ AndF vb $ AllF)

fst :: (Typeable a, Typeable b)
    => TypeRep a
    -> TypeRep b
    -> val s (Pair a b)
    -> Expr f val s (val s a)
fst ta tb vp = exprF $ ElimProduct (pair_t ta tb) ta
  (AnyC ta (\it -> pure it))
  vp

snd :: (Typeable a, Typeable b)
    => TypeRep a
    -> TypeRep b
    -> val s (Pair a b)
    -> Expr f val s (val s b)
snd ta tb vp = exprF $ ElimProduct (pair_t ta tb) tb
  (OrC $ AnyC tb (\it -> pure it))
  vp

type Maybe (t :: Type) = 'Sum '[ Unit, t ]

maybe_t :: Typeable t => TypeRep t -> TypeRep (Maybe t)
maybe_t t = Sum_t (AndF unit_t $ AndF t $ AllF)

just :: Typeable t => TypeRep t -> val s t -> Expr f val s (val s (Maybe t))
just tt t = exprF $ IntroSum (maybe_t tt) (OrF (AnyF t))

nothing :: Typeable t => TypeRep t -> Expr f val s (val s (Maybe t))
nothing tt = do
  u <- unit
  exprF $ IntroSum (maybe_t tt) (AnyF u)

elim_maybe
  :: forall val f s t r .
     ( Typeable t )
  => TypeRep t
  -> TypeRep r
  -> val s (Maybe t)
  -> (val s Unit -> Expr f val s (val s r))
  -> (val s t -> Expr f val s (val s r))
  -> Expr f val s (val s r)
elim_maybe trt trr v cNothing cJust = exprF $ ElimSum trs trr
  (AndC cNothing $ AndC cJust $ AllC)
  v
  where
  trs = maybe_t trt

type Either (s :: Type) (t :: Type) = 'Sum '[ s, t ]

either_t :: (Typeable s, Typeable t) => TypeRep s -> TypeRep t -> TypeRep (Either s t)
either_t s t = Sum_t (AndF s $ AndF t $ AllF)

left
  :: (Typeable a, Typeable b)
  => TypeRep a
  -> TypeRep b
  -> val s a
  -> Expr f val s (val s (Either a b))
left ta tb va = exprF $ IntroSum (either_t ta tb) (AnyF va)

right
  :: (Typeable a, Typeable b)
  => TypeRep a
  -> TypeRep b
  -> val s b
  -> Expr f val s (val s (Either a b))
right ta tb vb = exprF $ IntroSum (either_t ta tb) (OrF (AnyF vb))

-- NB: we cannot have the typical Haskell list type. Recursive types are not
-- allowed.

uint8 :: Haskell.Word8 -> Expr f val s (val s ('Integer Unsigned Eight))
uint8 w8 = exprF $ IntroInteger uint8_t (UInt8 w8)

uint16 :: Haskell.Word16 -> Expr f val s (val s ('Integer Unsigned Sixteen))
uint16 w16 = exprF $ IntroInteger uint16_t (UInt16 w16)

uint32 :: Haskell.Word32 -> Expr f val s (val s ('Integer Unsigned ThirtyTwo))
uint32 w32 = exprF $ IntroInteger uint32_t (UInt32 w32)

uint64 :: Haskell.Word64 -> Expr f val s (val s ('Integer Unsigned SixtyFour))
uint64 w64 = exprF $ IntroInteger uint64_t (UInt64 w64)

int8 :: Haskell.Int8 -> Expr f val s (val s ('Integer Signed Eight))
int8 i8 = exprF $ IntroInteger int8_t (Int8 i8)

int16 :: Haskell.Int16 -> Expr f val s (val s ('Integer Signed Sixteen))
int16 i16 = exprF $ IntroInteger int16_t (Int16 i16)

int32 :: Haskell.Int32 -> Expr f val s (val s ('Integer Signed ThirtyTwo))
int32 i32 = exprF $ IntroInteger int32_t (Int32 i32)

int64 :: Haskell.Int64 -> Expr f val s (val s ('Integer Signed SixtyFour))
int64 i64 = exprF $ IntroInteger int64_t (Int64 i64)

plus :: TypeRep ('Integer signedness width)
     -> val s ('Integer signedness width)
     -> val s ('Integer signedness width)
     -> Expr f val s (val s ('Integer signedness width))
plus tr x y = exprF $ AddInteger tr x y

local
  :: TypeRep t
  -> TypeRep r
  -> val s t
  -> (val s t -> Expr f val s (val s r))
  -> Expr f val s (val s r)
local trt trr val k = exprF (Local trt trr val k)
