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
  ( module Expr

  , Type (..)
  , TypeRep (..)
  , SomeTypeRep (..)
  , KnownType (..)
  , typeOf

  , ExprF (..)
  , All (..)
  , mapAll
  , traverseAll
  , zipAll
  , anyOfAll
  , Any (..)
  , mapAny
  , traverseAny
  , Field (..)
  , Selector (..)
  , Case (..)
  , forAll
  , allFields
  , allSelectors
  , allCases

  , IntegerLiteral (..)

  , Signedness (..)
  , SignednessRep (..)
  , KnownSignedness (..)
  , Width (..)
  , WidthRep (..)
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

  , local

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
import qualified Control.Monad as Monad (join)
import qualified Data.Int as Haskell (Int8, Int16, Int32, Int64)
import qualified Data.Kind as Haskell (Type)
import Data.Proxy (Proxy (..))
import qualified Data.Word as Haskell (Word8, Word16, Word32, Word64)

import Pilot.EDSL.Expr as Expr
import Pilot.Types.Represented

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

data PrimOpF (f :: Type -> Haskell.Type) (t :: Type) where
  Arithmetic :: ArithmeticOpF f t -> PrimOpF f t
  Bitwise    :: BitwiseOpF f t    -> PrimOpF f t
  Relative   :: RelativeOpF f t   -> PrimOpF f t

data ArithmeticOpF (f :: Type -> Haskell.Type) (t :: Type) where
  AddInteger :: TypeRep ('Integer signedness width)
             -> f ('Integer signedness width)
             -> f ('Integer signedness width)
             -> ArithmeticOpF f ('Integer signedness width)
  SubInteger :: TypeRep ('Integer signedness width)
             -> f ('Integer signedness width)
             -> f ('Integer signedness width)
             -> ArithmeticOpF f ('Integer signedness width)
  MulInteger :: TypeRep ('Integer signedness width)
             -> f ('Integer signedness width)
             -> f ('Integer signedness width)
             -> ArithmeticOpF f ('Integer signedness width)
  DivInteger :: TypeRep ('Integer signedness width)
             -> f ('Integer signedness width)
             -> f ('Integer signedness width)
             -> ArithmeticOpF f ('Integer signedness width)
  ModInteger :: TypeRep ('Integer signedness width)
             -> f ('Integer signedness width)
             -> f ('Integer signedness width)
             -> ArithmeticOpF f ('Integer signedness width)
  NegInteger :: TypeRep ('Integer 'Signed width)
             -> f ('Integer 'Signed width)
             -> ArithmeticOpF f ('Integer 'Signed width)

-- | Bitwise operations are permitted on all integral types. TODO maybe this
-- is not ideal. Should we give bit types which do not allow for arithmetic,
-- and demand explicit type conversions? Would maybe be useful.
data BitwiseOpF (f :: Type -> Haskell.Type) (t :: Type) where
  AndB :: TypeRep ('Integer signedness width)
       -> f ('Integer signedness width)
       -> f ('Integer signedness width)
       -> BitwiseOpF f ('Integer signedness width)
  OrB  :: TypeRep ('Integer signedness width)
       -> f ('Integer signedness width)
       -> f ('Integer signedness width)
       -> BitwiseOpF f ('Integer signedness width)
  XOrB :: TypeRep ('Integer signedness width)
       -> f ('Integer signedness width)
       -> f ('Integer signedness width)
       -> BitwiseOpF f ('Integer signedness width)
  NotB :: TypeRep ('Integer signedness width)
       -> f ('Integer signedness width)
       -> BitwiseOpF f ('Integer signedness width)
  ShiftL :: TypeRep ('Integer signedness width)
         -> f ('Integer signedness width)
         -> f ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF f ('Integer signedness width)
  ShiftR :: TypeRep ('Integer signedness width)
         -> f ('Integer signedness width)
         -> f ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF f ('Integer signedness width)

data RelativeOpF (f :: Type -> Haskell.Type) (t :: Type) where
  Cmp :: TypeRep ('Integer signedness width)
      -> TypeRep r
      -> f ('Integer signedness width)
      -> f ('Integer signedness width)
      -> f r -- ^ First less than second
      -> f r -- ^ Equal
      -> f r -- ^ First greater than second
      -> RelativeOpF f r

-- | Expressions in the pointwise EDSL. The `f` parameter represents the
-- _target_ or object language, for instance generated C code, or an in-Haskell
-- representation.
data ExprF (f :: Type -> Haskell.Type) (t :: Type) where

  IntroInteger :: TypeRep ('Integer signedness width)
               -> IntegerLiteral signedness width
               -> ExprF f ('Integer signedness width)

  PrimOp :: PrimOpF f t -> ExprF f t

  -- TODO safe upcasts
  -- TODO checked downcasts

  -- Compound data: algebraic datatypes

  IntroProduct :: TypeRep ('Product fields)
               -> All (Field f) fields
               -> ExprF f ('Product fields)

  -- IntroSum and ElimProduct have good symmetry. Not so much for IntroProduct
  -- and ElimSum.

  IntroSum     :: TypeRep ('Sum variants)
               -> TypeRep variant
               -> Any (Selector f) variants variant
               -> f variant
               -> ExprF f ('Sum variants)

  ElimProduct :: TypeRep ('Product fields)
              -> TypeRep field
              -> Any (Selector f) fields field
              -> f ('Product fields)
              -> ExprF f field

  ElimSum     :: TypeRep ('Sum variants)
              -> TypeRep r
              -> All (Case f r) variants
              -> f ('Sum variants)
              -> ExprF f r

  -- Explicit binding, so that the programmer may control sharing.
  Local :: TypeRep t
        -> TypeRep r
        -> f t
        -> (f t -> f r)
        -> ExprF f r

data All (f :: k -> Haskell.Type) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

mapAll :: (forall t . f t -> g t) -> All f ts -> All g ts
mapAll _ All = All
mapAll h (And t as) = And (h t) (mapAll h as)

traverseAll :: Applicative m => (forall t . f t -> m (g t)) -> All f ts -> m (All g ts)
traverseAll h All = pure All
traverseAll h (And t ts) = And <$> h t <*> traverseAll h ts

zipAll
  :: (forall x . f x -> g x -> h x)
  -> All f ts
  -> All g ts
  -> All h ts
zipAll _ All All = All
zipAll f (And fx fs) (And gx gs) = And (f fx gx) (zipAll f fs gs)

anyOfAll :: (forall t . f t -> Bool) -> All f ts -> Bool
anyOfAll p All = False
anyOfAll p (And t ts) = p t || anyOfAll p ts

-- TODO change constructor names to This and That.
data Any (f :: k -> Haskell.Type) (ts :: [k]) (r :: k) where
  Any :: f t -> Any f (t ': ts) t
  Or  :: Any f ts r -> Any f (t ': ts) r

mapAny :: (forall t . f t -> g t) -> Any f ts r -> Any g ts r
mapAny h (Any t) = Any (h t)
mapAny h (Or as) = Or (mapAny h as)

traverseAny :: Functor m => (forall t . f t -> m (g t)) -> Any f ts r -> m (Any g ts r)
traverseAny h (Any t) = Any <$> h t
traverseAny h (Or as) = Or <$> traverseAny h as

data Field (f :: k -> Haskell.Type) (t :: k) where
  Field :: TypeRep t -> f t -> Field f t

data Selector (f :: k -> Haskell.Type) (t :: k) where
  Selector :: Selector f t

data Case (f :: k -> Haskell.Type) (r :: k) (t :: k) where
  Case :: TypeRep t -> (f t -> f r) -> Case f r t

-- | For each of the conjuncts, pick out that conjunct in a disjunction.
forAll
  :: forall f g ts .
     (forall x . f x -> g x)
  -> All f ts
  -> All (Any g ts) ts
forAll h alls = go alls id
  where
  go :: forall ts' .
        All f ts'
     -> (forall r . Any g ts' r -> Any g ts r)
     -> All (Any g ts) ts'
  go All        _ = All
  go (And t ts) k = And (k (Any (h t))) (go ts (\a -> k (Or a)))

allFields
  :: forall f ts .
     (forall x . TypeRep x -> f x)
  -> All TypeRep ts
  -> All (Any (Field f) ts) ts
allFields f = forAll (\trep -> Field trep (f trep))

allSelectors
  :: forall f ts .
     All TypeRep ts
  -> All (Any (Selector f) ts) ts
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
unit :: Expr ExprF f Unit
unit = exprF_ $ IntroProduct unit_t All

type Void = 'Sum '[]

void_t :: TypeRep Void
void_t = Sum_t All

-- | An empty sum can be eliminated, but it cannot be introduced.
absurd :: TypeRep x -> Expr ExprF f Void -> Expr ExprF f x
absurd x_t void = exprF $ \interp -> ElimSum void_t x_t All (interp void)

-- | Use a 1 + 1 type for boolean. Important to note that the first disjunct
-- stands for true. An interpreter may need to know that. A C backend could,
-- for instance, represent this as a byte, and use typical logical operators.
type Boolean = 'Sum '[ Unit, Unit ]

boolean_t :: TypeRep Boolean
boolean_t = Sum_t (And unit_t $ And unit_t $ All)

true :: Expr ExprF f Boolean
true = exprF $ \interp -> IntroSum boolean_t unit_t (Any $ Selector) (interp unit)

false :: Expr ExprF f Boolean
false = exprF $ \interp -> IntroSum boolean_t unit_t (Or $ Any $ Selector) (interp unit)

elim_boolean
  :: forall f r .
     TypeRep r
  -> Expr ExprF f Boolean
  -> Expr ExprF f r
  -> Expr ExprF f r
  -> Expr ExprF f r
elim_boolean trep vb cTrue cFalse = exprF $ \interp -> ElimSum boolean_t trep
  (And (Case unit_t (\_ -> interp cTrue)) $
   And (Case unit_t (\_ -> interp cFalse)) $
   All)
  (interp vb)

if_else
  :: forall f r .
     TypeRep r
  -> Expr ExprF f Boolean
  -> Expr ExprF f r
  -> Expr ExprF f r
  -> Expr ExprF f r
if_else = elim_boolean

and :: Expr ExprF f Boolean -> Expr ExprF f Boolean -> Expr ExprF f Boolean
and a b = if_else boolean_t a b false

or :: Expr ExprF f Boolean -> Expr ExprF f Boolean -> Expr ExprF f Boolean
or a b = if_else boolean_t a true b

not :: Expr ExprF f Boolean -> Expr ExprF f Boolean
not a = if_else boolean_t a false true

type Ordering = 'Sum '[ Unit, Unit, Unit ]

ordering_t :: TypeRep Ordering
ordering_t = Sum_t (And unit_t $ And unit_t $ And unit_t $ All)

lt :: Expr ExprF f Ordering
lt = exprF $ \interp -> IntroSum ordering_t unit_t (Any $ Selector) (interp unit)

eq :: Expr ExprF f Ordering
eq = exprF $ \interp -> IntroSum ordering_t unit_t (Or $ Any $ Selector) (interp unit)

gt :: Expr ExprF f Ordering
gt = exprF $ \interp -> IntroSum ordering_t unit_t (Or $ Or $ Any $ Selector) (interp unit)

elim_ordering
  :: forall f r .
     TypeRep r
  -> Expr ExprF f Ordering
  -> Expr ExprF f r
  -> Expr ExprF f r
  -> Expr ExprF f r
  -> Expr ExprF f r
elim_ordering trep vo cLt cEq cGt = exprF $ \interp -> ElimSum ordering_t trep
  (And (Case unit_t (\_ -> interp cLt)) $
   And (Case unit_t (\_ -> interp cEq)) $ 
   And (Case unit_t (\_ -> interp cGt)) $
   All)
  (interp vo)

cmp :: TypeRep ('Integer signedness width)
    -> TypeRep r
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f r -- ^ First less than second
    -> Expr ExprF f r -- ^ Equal
    -> Expr ExprF f r -- ^ First greater than second
    -> Expr ExprF f r
cmp trep trepr x y lt eq gt = exprF $ \interp -> PrimOp $ Relative $ Cmp trep trepr
  (interp x)
  (interp y)
  (interp lt)
  (interp eq)
  (interp gt)

type Pair (s :: Type) (t :: Type) = 'Product '[ s, t]

pair_t :: TypeRep s -> TypeRep t -> TypeRep (Pair s t)
pair_t s t = Product_t (And s $ And t $ All)

pair :: TypeRep a
     -> TypeRep b
     -> Expr ExprF f a
     -> Expr ExprF f b
     -> Expr ExprF f (Pair a b)
pair ta tb va vb = exprF $ \interp -> IntroProduct (pair_t ta tb)
  (And (Field ta (interp va)) $ And (Field tb (interp vb)) $ All)

fst :: TypeRep a
    -> TypeRep b
    -> Expr ExprF f (Pair a b)
    -> Expr ExprF f a
fst ta tb vp = exprF $ \interp -> ElimProduct (pair_t ta tb) ta
  (Any Selector)
  (interp vp)

snd :: TypeRep a
    -> TypeRep b
    -> Expr ExprF f (Pair a b)
    -> Expr ExprF f b
snd ta tb vp = exprF $ \interp -> ElimProduct (pair_t ta tb) tb
  (Or $ Any Selector)
  (interp vp)

type Maybe (t :: Type) = 'Sum '[ Unit, t ]

maybe_t :: TypeRep t -> TypeRep (Maybe t)
maybe_t t = Sum_t (And unit_t $ And t $ All)

just :: TypeRep t -> Expr ExprF f t -> Expr ExprF f (Maybe t)
just tt t = exprF $ \interp -> IntroSum (maybe_t tt) tt (Or (Any Selector))
  (interp t)

nothing :: TypeRep t -> Expr ExprF f (Maybe t)
nothing tt = exprF $ \interp -> IntroSum (maybe_t tt) unit_t (Any Selector)
  (interp unit)

elim_maybe
  :: forall f t r .
     TypeRep t
  -> TypeRep r
  -> Expr ExprF f (Maybe t)
  -> (Expr ExprF f Unit -> Expr ExprF f r)
  -> (Expr ExprF f t    -> Expr ExprF f r)
  -> Expr ExprF f r
elim_maybe trt trr v cNothing cJust = exprF $ \interp -> ElimSum trs trr
  (And (Case unit_t (interp . cNothing . known)) $
   And (Case trt    (interp . cJust    . known)) $
   All)
  (interp v)
  where
  trs = maybe_t trt

type Either (s :: Type) (t :: Type) = 'Sum '[ s, t ]

either_t
  :: TypeRep s
  -> TypeRep t
  -> TypeRep (Either s t)
either_t s t = Sum_t (And s $ And t $ All)

left
  :: TypeRep a
  -> TypeRep b
  -> Expr ExprF f a
  -> Expr ExprF f (Either a b)
left ta tb va = exprF $ \interp -> IntroSum (either_t ta tb) ta
  (Any Selector) (interp va)

right
  :: TypeRep a
  -> TypeRep b
  -> Expr ExprF f b
  -> Expr ExprF f (Either a b)
right ta tb vb = exprF $ \interp -> IntroSum (either_t ta tb) tb
  (Or (Any (Selector))) (interp vb)

elim_either
  :: forall a b c f .
     TypeRep a
  -> TypeRep b
  -> TypeRep c
  -> Expr ExprF f (Either a b)
  -> (Expr ExprF f a -> Expr ExprF f c)
  -> (Expr ExprF f b -> Expr ExprF f c)
  -> Expr ExprF f c
elim_either tra trb trc v cLeft cRight = exprF $ \interp -> ElimSum
  (either_t tra trb) trc
  (And (Case tra (interp . cLeft  . known)) $
   And (Case trb (interp . cRight . known)) $
   All)
  (interp v)

-- NB: we cannot have the typical Haskell list type. Recursive types are not
-- allowed.

uint8 :: Haskell.Word8 -> Expr ExprF f ('Integer 'Unsigned 'Eight)
uint8 w8 = exprF_ $ IntroInteger uint8_t (UInt8 w8)

uint16 :: Haskell.Word16 -> Expr ExprF f ('Integer 'Unsigned 'Sixteen)
uint16 w16 = exprF_ $ IntroInteger uint16_t (UInt16 w16)

uint32 :: Haskell.Word32 -> Expr ExprF f ('Integer 'Unsigned 'ThirtyTwo)
uint32 w32 = exprF_ $ IntroInteger uint32_t (UInt32 w32)

uint64 :: Haskell.Word64 -> Expr ExprF f ('Integer 'Unsigned 'SixtyFour)
uint64 w64 = exprF_ $ IntroInteger uint64_t (UInt64 w64)

int8 :: Haskell.Int8 -> Expr ExprF f ('Integer 'Signed 'Eight)
int8 i8 = exprF_ $ IntroInteger int8_t (Int8 i8)

int16 :: Haskell.Int16 -> Expr ExprF f ('Integer 'Signed 'Sixteen)
int16 i16 = exprF_ $ IntroInteger int16_t (Int16 i16)

int32 :: Haskell.Int32 -> Expr ExprF f ('Integer 'Signed 'ThirtyTwo)
int32 i32 = exprF_ $ IntroInteger int32_t (Int32 i32)

int64 :: Haskell.Int64 -> Expr ExprF f ('Integer 'Signed 'SixtyFour)
int64 i64 = exprF_ $ IntroInteger int64_t (Int64 i64)

add :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
add tr x y = exprF $ \interp -> PrimOp $ Arithmetic $ AddInteger tr (interp x) (interp y)

sub :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
sub tr x y = exprF $ \interp -> PrimOp $ Arithmetic $ SubInteger tr (interp x) (interp y)

mul :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
mul tr x y = exprF $ \interp -> PrimOp $ Arithmetic $ MulInteger tr (interp x) (interp y)

div :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
div tr x y = exprF $ \interp -> PrimOp $ Arithmetic $ DivInteger tr (interp x) (interp y)

mod :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
mod tr x y = exprF $ \interp -> PrimOp $ Arithmetic $ ModInteger tr (interp x) (interp y)

neg :: TypeRep ('Integer 'Signed width)
    -> Expr ExprF f ('Integer 'Signed width)
    -> Expr ExprF f ('Integer 'Signed width)
neg tr x = exprF $ \interp -> PrimOp $ Arithmetic $ NegInteger tr (interp x)

andB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
andB tr x y = exprF $ \interp -> PrimOp $ Bitwise $ AndB tr (interp x) (interp y)

orB :: TypeRep ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
    -> Expr ExprF f ('Integer signedness width)
orB tr x y = exprF $ \interp -> PrimOp $ Bitwise $ OrB tr (interp x) (interp y)

xorB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
xorB tr x y = exprF $ \interp -> PrimOp $ Bitwise $ XOrB tr (interp x) (interp y)

notB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
     -> Expr ExprF f ('Integer signedness width)
notB tr x = exprF $ \interp -> PrimOp $ Bitwise $ NotB tr (interp x)

shiftL :: TypeRep ('Integer signedness width)
       -> Expr ExprF f ('Integer signedness width)
       -> Expr ExprF f ('Integer 'Unsigned 'Eight)
       -> Expr ExprF f ('Integer signedness width)
shiftL tr x y = exprF $ \interp -> PrimOp $ Bitwise $ ShiftL tr (interp x) (interp y)

shiftR :: TypeRep ('Integer signedness width)
       -> Expr ExprF f ('Integer signedness width)
       -> Expr ExprF f ('Integer 'Unsigned 'Eight)
       -> Expr ExprF f ('Integer signedness width)
shiftR tr x y = exprF $ \interp -> PrimOp $ Bitwise $ ShiftR tr (interp x) (interp y)

local
  :: TypeRep t
  -> TypeRep r
  -> Expr ExprF f t
  -> (Expr ExprF f t -> Expr ExprF f r)
  -> Expr ExprF f r
local trt trr v k = exprF $ \interp -> Local trt trr (interp v) (interp . k . known)
