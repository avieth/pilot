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
{-# LANGUAGE BangPatterns #-}

module Pilot.EDSL.Point
  ( module Expr

  , Type (..)
  , TypeRep (..)
  , SomeTypeRep (..)
  , KnownType (..)
  , typeOf

  , ExprF (..)
  , Selector (..)
  , Case (..)
  , allSelectors
  , allCases

  , IntegerLiteral (..)

  , Signedness (..)
  , SignednessRep (..)
  , KnownSignedness (..)
  , Width (..)
  , WidthRep (..)
  , SomeWidthRep (..)
  , KnownWidth (..)

  , PrimOpF (..)
  , ArithmeticOpF (..)
  , BitwiseOpF (..)
  , RelativeOpF (..)

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

  , add
  , sub
  , mul
  , div
  , mod
  , neg

  , andB
  , orB
  , xorB
  , notB
  , shiftL
  , shiftR

  , cmp

  , Unit
  , unit_t
  , unit
  , Void
  , void_t
  , absurd
  , Boolean
  , boolean_t
  , true
  , false
  , elim_boolean
  , if_else
  , and
  , or
  , not
  , Ordering
  , ordering_t
  , lt
  , eq
  , gt
  , elim_ordering
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
  , elim_either

  ) where

import Prelude hiding (Maybe, Either, Ordering, and, fst, snd, div, drop, mod, not, or)
import qualified Prelude
import qualified Data.Int as Haskell (Int8, Int16, Int32, Int64)
import qualified Data.Kind as Haskell (Type)
import qualified Data.Word as Haskell (Word8, Word16, Word32, Word64)

import Pilot.EDSL.Expr as Expr
import Pilot.Types.Represented
import Pilot.Types.Logic

-- | Types for the pointwise EDSL: various numeric types, with finite sums and
-- products. As usual, the empty product is unit, and the empty sum is void.
-- There is no boolean type; it can be expressed as a sum of units.
data Type where
  Integer  :: Signedness -> Width -> Type
  Rational :: Type
  Product  :: [Type] -> Type
  Sum      :: [Type] -> Type

instance Represented Type where
  type Rep Type = TypeRep

-- TODO Auto instance for everything in Type.

data Signedness where
  Signed   :: Signedness
  Unsigned :: Signedness

instance Represented Signedness where
  type Rep Signedness = SignednessRep

data SignednessRep (s :: Signedness) where
  Signed_t :: SignednessRep 'Signed
  Unsigned_t :: SignednessRep 'Unsigned

instance Auto 'Signed where
  repVal _ = Signed_t

instance Auto 'Unsigned where
  repVal _ = Unsigned_t

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

instance Represented Width where
  type Rep Width = WidthRep

data WidthRep (t :: Width) where
  Eight_t     :: WidthRep 'Eight
  Sixteen_t   :: WidthRep 'Sixteen
  ThirtyTwo_t :: WidthRep 'ThirtyTwo
  SixtyFour_t :: WidthRep 'SixtyFour

instance Auto 'Eight where
  repVal _ = Eight_t

instance Auto 'Sixteen where
  repVal _ = Sixteen_t

instance Auto 'ThirtyTwo where
  repVal _ = ThirtyTwo_t

instance Auto 'SixtyFour where
  repVal _ = SixtyFour_t

data SomeWidthRep where
  SomeWidthRep :: WidthRep t -> SomeWidthRep

instance Eq SomeWidthRep where
  a == b = (a `compare` b) == EQ

instance Ord SomeWidthRep where

  SomeWidthRep Eight_t `compare` SomeWidthRep Eight_t = EQ
  SomeWidthRep Eight_t `compare` _                    = LT

  SomeWidthRep Sixteen_t `compare` SomeWidthRep Sixteen_t = EQ
  SomeWidthRep Sixteen_t `compare` SomeWidthRep Eight_t   = GT
  SomeWidthRep Sixteen_t `compare` _                      = LT

  SomeWidthRep ThirtyTwo_t `compare` SomeWidthRep ThirtyTwo_t = EQ
  SomeWidthRep ThirtyTwo_t `compare` SomeWidthRep Eight_t     = GT
  SomeWidthRep ThirtyTwo_t `compare` SomeWidthRep Sixteen_t   = GT
  SomeWidthRep ThirtyTwo_t `compare` _                        = LT

  SomeWidthRep SixtyFour_t `compare` SomeWidthRep SixtyFour_t = EQ
  SomeWidthRep SixtyFour_t `compare` _                        = GT

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

  UInt8  :: Haskell.Word8  -> IntegerLiteral 'Unsigned 'Eight
  UInt16 :: Haskell.Word16 -> IntegerLiteral 'Unsigned 'Sixteen
  UInt32 :: Haskell.Word32 -> IntegerLiteral 'Unsigned 'ThirtyTwo
  UInt64 :: Haskell.Word64 -> IntegerLiteral 'Unsigned 'SixtyFour

  Int8  :: Haskell.Int8  -> IntegerLiteral 'Signed 'Eight
  Int16 :: Haskell.Int16 -> IntegerLiteral 'Signed 'Sixteen
  Int32 :: Haskell.Int32 -> IntegerLiteral 'Signed 'ThirtyTwo
  Int64 :: Haskell.Int64 -> IntegerLiteral 'Signed 'SixtyFour

-- | Characterization of safe casts with no need for a check. That's any
-- cast from a smaller to a wider type, of the same signedness.
data UncheckedCast (w1 :: Width) (w2 :: Width) where

  Cast_Unchecked_Eight_Sixteen   :: UncheckedCast 'Eight 'Sixteen
  Cast_Unchecked_Eight_ThirtyTwo :: UncheckedCast 'Eight 'ThirtyTwo
  Cast_Unchecked_Eight_SxityFour :: UncheckedCast 'Eight 'SixtyFour

  Cast_Unchekced_Sixteen_ThirtyTwo :: UncheckedCast 'Sixteen 'ThirtyTwo
  Cast_Unchecked_Sixteen_SixtyFour :: UncheckedCast 'Sixteen 'SixtyFour

  Cast_Unchecked_ThirtyTwo_SixtyFour :: UncheckedCast 'ThirtyTwo 'SixtyFour

-- | Value-level representation of 'Type' data kinds.
data TypeRep (t :: Type) where

  Integer_t  :: SignednessRep signedness
             -> WidthRep width
             -> TypeRep ('Integer signedness width)
  Rational_t :: TypeRep 'Rational

  Product_t :: All TypeRep tys -> TypeRep ('Product tys)
  Sum_t     :: All TypeRep tys -> TypeRep ('Sum tys)

-- TODO do not use the KnownType class, use Auto instead.
-- Here we define Auto in terms of KnownType since the latter was already there.
instance KnownType t => Auto t where
  repVal = typeRep

-- | Analagous to GHC Haskell's SomeTypeRep from Data.Typeable.
-- We're interested in having this because it's Eq and Ord (i.e. you can put
-- it into a Map).
data SomeTypeRep where
  SomeTypeRep :: TypeRep t -> SomeTypeRep

instance Eq SomeTypeRep where
  a == b = (a `compare` b) == EQ

-- TODO how do we order this?
-- Defining nontrivial ord instances is error prone and it's bitten me before.
--
-- For the integer types it can be simple enough.
--   unsigned x < signed y
--   signed x   < signed y   iff x < y
--   unsigned x < unsigned y iif x < y
--
-- but for sums and products? Treat it like a tuple?
--
--   1. products are less than sums
--   2. The shorter compound is less than the longer compound
--   3. at each common point in the compound, if one is less than the other,
--      then that composite is less than the other.
-- 
-- Pretty sure this is transitive.

instance Ord SomeTypeRep where

  SomeTypeRep (Integer_t Signed_t wr) `compare` SomeTypeRep (Integer_t Signed_t wr') =
    SomeWidthRep wr `compare` SomeWidthRep wr'
  SomeTypeRep (Integer_t Unsigned_t wr) `compare` SomeTypeRep (Integer_t Unsigned_t wr') =
    SomeWidthRep wr `compare` SomeWidthRep wr'

  SomeTypeRep (Integer_t Signed_t _)   `compare` SomeTypeRep (Integer_t Unsigned_t _) = LT
  SomeTypeRep (Integer_t Unsigned_t _) `compare` SomeTypeRep (Integer_t Signed_t   _) = GT

  SomeTypeRep (Integer_t _ _) `compare` _ = LT

  SomeTypeRep Rational_t      `compare` SomeTypeRep (Integer_t _ _) = GT
  SomeTypeRep Rational_t      `compare` _ = LT

  SomeTypeRep (Product_t p) `compare` SomeTypeRep (Product_t q) = compare_compound p q
  SomeTypeRep (Product_t _) `compare` SomeTypeRep (Sum_t _) = LT
  SomeTypeRep (Product_t _) `compare` _ = GT

  SomeTypeRep (Sum_t s) `compare` SomeTypeRep (Sum_t r) = compare_compound s r
  SomeTypeRep (Sum_t _) `compare` _ = GT

-- | An ordering on lists of 'TypeRep's.
--
-- The lists always have a common equal prefix (prefix such that all types at
-- the corresponding positions are equal) even though that prefix may be of
-- length 0.
--
-- To compute the order, we drop that prefix, finding the first position for
-- which there is a different type rep.
-- - If there is no such position, they're equal.
-- - If the left list is a prefix of the right list then left is less than
--   right.
-- - If the right list is a prefix of the left list then right is less than
--   left.
-- - If there is a position for which the lists differ, then the ordering of
--   that element is the ordering of the compound.
--
-- This is just list ordering. Should be legit.
--
compare_compound :: All TypeRep tys -> All TypeRep tys' -> Prelude.Ordering
compare_compound All All = EQ
compare_compound All (And _ _) = LT
compare_compound (And _ _) All = GT
compare_compound (And ty tys) (And ty' tys') = case SomeTypeRep ty `compare` SomeTypeRep ty' of
  LT -> LT
  GT -> GT
  EQ -> compare_compound tys tys'

-- TODO 
instance Show SomeTypeRep where
  show _ = "SomeTypeRep"

class KnownType (t :: Type) where
  typeRep :: proxy t -> TypeRep t

instance (KnownSignedness signedness, KnownWidth width) => KnownType ('Integer signedness width) where
  typeRep _ = Integer_t (signednessRep (Proxy :: Proxy signedness))
                        (widthRep (Proxy :: Proxy width))

instance KnownType ('Product '[]) where
  typeRep _ = Product_t All

instance (KnownType t, KnownType ('Product ts))
  => KnownType ('Product (t ': ts)) where
  typeRep _ =
    let Product_t theRest = typeRep (Proxy :: Proxy ('Product ts))
    in  Product_t (And (typeRep (Proxy :: Proxy t)) theRest)

instance KnownType ('Sum '[]) where
  typeRep _ = Sum_t All

instance (KnownType t, KnownType ('Sum ts))
  => KnownType ('Sum (t ': ts)) where
  typeRep _ =
    let Sum_t theRest = typeRep (Proxy :: Proxy ('Sum ts))
    in  Sum_t (And (typeRep (Proxy :: Proxy t)) theRest)

typeOf :: forall anything t . KnownType t => anything t -> TypeRep t
typeOf _ = typeRep (Proxy :: Proxy t)

data PrimOpF (expr :: Type -> Haskell.Type) (t :: Type) where
  Arithmetic :: ArithmeticOpF expr t -> PrimOpF expr t
  Bitwise    :: BitwiseOpF    expr t -> PrimOpF expr t
  Relative   :: RelativeOpF   expr t -> PrimOpF expr t

data ArithmeticOpF (expr :: Type -> Haskell.Type) (t :: Type) where
  AddInteger :: TypeRep ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> ArithmeticOpF expr ('Integer signedness width)
  SubInteger :: TypeRep ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> ArithmeticOpF expr ('Integer signedness width)
  MulInteger :: TypeRep ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> ArithmeticOpF expr ('Integer signedness width)
  DivInteger :: TypeRep ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> ArithmeticOpF expr ('Integer signedness width)
  ModInteger :: TypeRep ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> expr ('Integer signedness width)
             -> ArithmeticOpF expr ('Integer signedness width)
  NegInteger :: TypeRep ('Integer 'Signed width)
             -> expr ('Integer 'Signed width)
             -> ArithmeticOpF expr ('Integer 'Signed width)

-- | Bitwise operations are permitted on all integral types. TODO maybe this
-- is not ideal. Should we give bit types which do not allow for arithmetic,
-- and demand explicit type conversions? Would maybe be useful.
data BitwiseOpF (expr :: Type -> Haskell.Type) (t :: Type) where
  AndB :: TypeRep ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> BitwiseOpF expr ('Integer signedness width)
  OrB  :: TypeRep ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> BitwiseOpF expr ('Integer signedness width)
  XOrB :: TypeRep ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> BitwiseOpF expr ('Integer signedness width)
  NotB :: TypeRep ('Integer signedness width)
       -> expr ('Integer signedness width)
       -> BitwiseOpF expr ('Integer signedness width)
  ShiftL :: TypeRep ('Integer signedness width)
         -> expr ('Integer signedness width)
         -> expr ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF expr ('Integer signedness width)
  ShiftR :: TypeRep ('Integer signedness width)
         -> expr ('Integer signedness width)
         -> expr ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF expr ('Integer signedness width)

data RelativeOpF (expr :: Type -> Haskell.Type) (t :: Type) where
  Cmp :: TypeRep ('Integer signedness width)
      -> TypeRep r
      -> expr ('Integer signedness width)
      -> expr ('Integer signedness width)
      -> expr r -- ^ First less than second
      -> expr r -- ^ Equal
      -> expr r -- ^ First greater than second
      -> RelativeOpF expr r

-- | Expressions in the pointwise EDSL. The `f` parameter represents the
-- _target_ or object language, for instance generated C code, or an in-Haskell
-- representation.
data ExprF (expr :: Type -> Haskell.Type) (t :: Type) where

  IntroInteger :: TypeRep ('Integer signedness width)
               -> IntegerLiteral signedness width
               -> ExprF expr ('Integer signedness width)

  PrimOp :: PrimOpF expr t -> ExprF expr t

  -- | An unchecked cast may be done whenver it's guaranteed to fit into the
  -- result type. No sign change is possible.
  UncheckedCastOp :: SignednessRep signedness
                  -> UncheckedCast w1 w2
                  -> expr ('Integer signedness w1)
                  -> ExprF expr ('Integer signedness w2)

  -- | A checked cast may be done for any integer types (even if they are the
  -- same).
  CheckedCastOp :: TypeRep ('Integer s1 w1)
                -> TypeRep ('Integer s2 w2)
                -> expr ('Integer s1 w2)
                -> ExprF expr (Maybe ('Integer s2 w2))

  -- Compound data: algebraic datatypes

  IntroProduct :: TypeRep ('Product fields)
               -> All expr fields
               -> ExprF expr ('Product fields)

  IntroSum     :: TypeRep ('Sum variants)
               -> TypeRep variant
               -> Any expr variants variant
               -> ExprF expr ('Sum variants)

  ElimProduct :: TypeRep ('Product fields)
              -> TypeRep field
              -> Any Selector fields field
              -> expr ('Product fields)
              -> ExprF expr field

  ElimSum     :: TypeRep ('Sum variants)
              -> TypeRep r
              -> expr ('Sum variants)
              -> All (Case expr r) variants
              -> ExprF expr r

data Selector (t :: k) where
  Selector :: Selector t

data Case (f :: k -> Haskell.Type) (r :: k) (t :: k) where
  Case :: TypeRep t -> (f t -> f r) -> Case f r t

allSelectors
  :: forall ts .
     All TypeRep ts
  -> All (Any Selector ts) ts
allSelectors = forAll (\_ -> Selector)

allCases
  :: forall f ts r .
     (forall x . TypeRep x -> f x -> f r)
  -> All TypeRep ts
  -> All (Any (Case f r) ts) ts
allCases f = forAll (\trep -> Case trep (f trep))

-- Some examples of 'Type's and 'TypeRep's

type UInt8  = 'Integer 'Unsigned 'Eight
type UInt16 = 'Integer 'Unsigned 'Sixteen
type UInt32 = 'Integer 'Unsigned 'ThirtyTwo
type UInt64 = 'Integer 'Unsigned 'SixtyFour

type Int8  = 'Integer 'Signed 'Eight
type Int16 = 'Integer 'Signed 'Sixteen
type Int32 = 'Integer 'Signed 'ThirtyTwo
type Int64 = 'Integer 'Signed 'SixtyFour

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
unit_t = Product_t All

-- | An empty product can be introduced, but it cannot be eliminated.
unit :: Expr ExprF expr f Unit
unit = exprF $ IntroProduct unit_t All

type Void = 'Sum '[]

void_t :: TypeRep Void
void_t = Sum_t All

-- | An empty sum can be eliminated, but it cannot be introduced.
absurd :: TypeRep x -> Expr ExprF expr f Void -> Expr ExprF expr f x
absurd x_t impossible = exprF $ ElimSum void_t x_t impossible All

-- | Use a 1 + 1 type for boolean. Important to note that the first disjunct
-- stands for true. An interpreter may need to know that. A C backend could,
-- for instance, represent this as a byte, and use typical logical operators.
type Boolean = 'Sum '[ Unit, Unit ]

boolean_t :: TypeRep Boolean
boolean_t = Sum_t (And unit_t $ And unit_t $ All)

type Ordering = 'Sum '[ Unit, Unit, Unit ]

ordering_t :: TypeRep Ordering
ordering_t = Sum_t (And unit_t $ And unit_t $ And unit_t $ All)

type Pair (s :: Type) (t :: Type) = 'Product '[ s, t]

pair_t :: TypeRep s -> TypeRep t -> TypeRep (Pair s t)
pair_t s t = Product_t (And s $ And t $ All)

type Maybe (t :: Type) = 'Sum '[ Unit, t ]

maybe_t :: TypeRep t -> TypeRep (Maybe t)
maybe_t t = Sum_t (And unit_t $ And t $ All)

type Either (s :: Type) (t :: Type) = 'Sum '[ s, t ]

either_t
  :: TypeRep s
  -> TypeRep t
  -> TypeRep (Either s t)
either_t s t = Sum_t (And s $ And t $ All)

pair :: TypeRep a
     -> TypeRep b
     -> Expr ExprF expr f a
     -> Expr ExprF expr f b
     -> Expr ExprF expr f (Pair a b)
pair ta tb va vb = exprF $ IntroProduct (pair_t ta tb)
  (And va $
   And vb $
   All)

fst :: TypeRep a
    -> TypeRep b
    -> Expr ExprF expr f (Pair a b)
    -> Expr ExprF expr f a
fst ta tb vp = exprF $ ElimProduct (pair_t ta tb) ta (Any Selector) vp

snd :: TypeRep a
    -> TypeRep b
    -> Expr ExprF expr f (Pair a b)
    -> Expr ExprF expr f b
snd ta tb vp = exprF $ ElimProduct (pair_t ta tb) tb (Or $ Any Selector) vp

just :: TypeRep t -> Expr ExprF expr f t -> Expr ExprF expr f (Maybe t)
just tt t = exprF $ IntroSum (maybe_t tt) tt (Or (Any t))

nothing :: TypeRep t -> Expr ExprF expr f (Maybe t)
nothing tt = exprF $ IntroSum (maybe_t tt) unit_t (Any unit)

elim_maybe
  :: forall expr f t r .
     TypeRep t
  -> TypeRep r
  -> Expr ExprF expr f (Maybe t)
  -> (Expr ExprF expr f Unit -> Expr ExprF expr f r)
  -> (Expr ExprF expr f t    -> Expr ExprF expr f r)
  -> Expr ExprF expr f r
elim_maybe trt trr v cNothing cJust = exprF $ ElimSum trs trr
  v
  (And (Case unit_t cNothing) $
   And (Case trt    cJust   ) $
   All)
  where
  trs = maybe_t trt

left
  :: TypeRep a
  -> TypeRep b
  -> Expr ExprF expr f a
  -> Expr ExprF expr f (Either a b)
left ta tb va = exprF $ IntroSum (either_t ta tb) ta (Any va)

right
  :: TypeRep a
  -> TypeRep b
  -> Expr ExprF expr f b
  -> Expr ExprF expr f (Either a b)
right ta tb vb = exprF $ IntroSum (either_t ta tb) tb (Or (Any vb))

elim_either
  :: forall a b c val f .
     TypeRep a
  -> TypeRep b
  -> TypeRep c
  -> Expr ExprF val f (Either a b)
  -> (Expr ExprF val f a -> Expr ExprF val f c)
  -> (Expr ExprF val f b -> Expr ExprF val f c)
  -> Expr ExprF val f c
elim_either tra trb trc v cLeft cRight = exprF $ ElimSum
  (either_t tra trb) trc
  v
  (And (Case tra cLeft ) $
   And (Case trb cRight) $
   All)

false :: Expr ExprF expr f Boolean
false = exprF $ IntroSum boolean_t unit_t (Any $ unit)

true :: Expr ExprF expr f Boolean
true = exprF $ IntroSum boolean_t unit_t (Or $ Any $ unit)

elim_boolean
  :: forall val r f .
     TypeRep r
  -> Expr ExprF val f Boolean
  -> Expr ExprF val f r
  -> Expr ExprF val f r
  -> Expr ExprF val f r
elim_boolean trep vb cFalse cTrue = exprF $ ElimSum boolean_t trep
  vb
  (And (Case unit_t (\_ -> cFalse)) $
   And (Case unit_t (\_ -> cTrue)) $
   All)

if_else
  :: forall val r f .
     TypeRep r
  -> Expr ExprF val f Boolean
  -> Expr ExprF val f r
  -> Expr ExprF val f r
  -> Expr ExprF val f r
if_else = elim_boolean

and :: Expr ExprF val f Boolean
    -> Expr ExprF val f Boolean
    -> Expr ExprF val f Boolean
and a b = if_else boolean_t a false b

or :: Expr ExprF val f Boolean
   -> Expr ExprF val f Boolean
   -> Expr ExprF val f Boolean
or a b = if_else boolean_t a b true

not :: Expr ExprF val f Boolean -> Expr ExprF val f Boolean
not a = if_else boolean_t a true false

lt :: Expr ExprF val f Ordering
lt = exprF $ IntroSum ordering_t unit_t (Any $ unit)

eq :: Expr ExprF val f Ordering
eq = exprF $ IntroSum ordering_t unit_t (Or $ Any $ unit)

gt :: Expr ExprF val f Ordering
gt = exprF $ IntroSum ordering_t unit_t (Or $ Or $ Any $ unit)

elim_ordering
  :: forall val r f .
     TypeRep r
  -> Expr ExprF val f Ordering
  -> Expr ExprF val f r
  -> Expr ExprF val f r
  -> Expr ExprF val f r
  -> Expr ExprF val f r
elim_ordering trep vo cLt cEq cGt = exprF $ ElimSum ordering_t trep
  vo
  (And (Case unit_t (\_ -> cLt)) $
   And (Case unit_t (\_ -> cEq)) $ 
   And (Case unit_t (\_ -> cGt)) $
   All)

cmp :: TypeRep ('Integer signedness width)
    -> TypeRep r
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f r -- ^ First less than second
    -> Expr ExprF val f r -- ^ Equal
    -> Expr ExprF val f r -- ^ First greater than second
    -> Expr ExprF val f r
cmp trep trepr x y cLT cEQ cGT = exprF $ PrimOp $ Relative $ Cmp trep trepr x y
  cLT cEQ cGT

-- NB: we cannot have the typical Haskell list type. Recursive types are not
-- allowed.

uint8 :: Haskell.Word8 -> Expr ExprF val f ('Integer 'Unsigned 'Eight)
uint8 w8 = exprF $ IntroInteger uint8_t (UInt8 w8)

uint16 :: Haskell.Word16 -> Expr ExprF val f ('Integer 'Unsigned 'Sixteen)
uint16 w16 = exprF $ IntroInteger uint16_t (UInt16 w16)

uint32 :: Haskell.Word32 -> Expr ExprF val f ('Integer 'Unsigned 'ThirtyTwo)
uint32 w32 = exprF $ IntroInteger uint32_t (UInt32 w32)

uint64 :: Haskell.Word64 -> Expr ExprF val f ('Integer 'Unsigned 'SixtyFour)
uint64 w64 = exprF $ IntroInteger uint64_t (UInt64 w64)

int8 :: Haskell.Int8 -> Expr ExprF val f ('Integer 'Signed 'Eight)
int8 i8 = exprF $ IntroInteger int8_t (Int8 i8)

int16 :: Haskell.Int16 -> Expr ExprF val f ('Integer 'Signed 'Sixteen)
int16 i16 = exprF $ IntroInteger int16_t (Int16 i16)

int32 :: Haskell.Int32 -> Expr ExprF val f ('Integer 'Signed 'ThirtyTwo)
int32 i32 = exprF $ IntroInteger int32_t (Int32 i32)

int64 :: Haskell.Int64 -> Expr ExprF val f ('Integer 'Signed 'SixtyFour)
int64 i64 = exprF $ IntroInteger int64_t (Int64 i64)

add :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
add tr x y = exprF $ PrimOp $ Arithmetic $ AddInteger tr x y

sub :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
sub tr x y = exprF $ PrimOp $ Arithmetic $ SubInteger tr x y

mul :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
mul tr x y = exprF $ PrimOp $ Arithmetic $ MulInteger tr x y

div :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
div tr x y = exprF $ PrimOp $ Arithmetic $ DivInteger tr x y

mod :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
mod tr x y = exprF $ PrimOp $ Arithmetic $ ModInteger tr x y

neg :: TypeRep ('Integer 'Signed width)
    -> Expr ExprF val f ('Integer 'Signed width)
    -> Expr ExprF val f ('Integer 'Signed width)
neg tr x = exprF $ PrimOp $ Arithmetic $ NegInteger tr x

andB :: TypeRep ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
andB tr x y = exprF $ PrimOp $ Bitwise $ AndB tr x y

orB :: TypeRep ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
    -> Expr ExprF val f ('Integer signedness width)
orB tr x y = exprF $ PrimOp $ Bitwise $ OrB tr x y

xorB :: TypeRep ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
xorB tr x y = exprF $ PrimOp $ Bitwise $ XOrB tr x y

notB :: TypeRep ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
     -> Expr ExprF val f ('Integer signedness width)
notB tr x = exprF $ PrimOp $ Bitwise $ NotB tr x

shiftL :: TypeRep ('Integer signedness width)
       -> Expr ExprF val f ('Integer signedness width)
       -> Expr ExprF val f ('Integer 'Unsigned 'Eight)
       -> Expr ExprF val f ('Integer signedness width)
shiftL tr x y = exprF $ PrimOp $ Bitwise $ ShiftL tr x y

shiftR :: TypeRep ('Integer signedness width)
       -> Expr ExprF val f ('Integer signedness width)
       -> Expr ExprF val f ('Integer 'Unsigned 'Eight)
       -> Expr ExprF val f ('Integer signedness width)
shiftR tr x y = exprF $ PrimOp $ Bitwise $ ShiftR tr x y
