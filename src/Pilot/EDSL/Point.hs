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
  , exprF
  , value
  , evalInMonad

  , Type (..)
  , TypeRep (..)
  , SomeTypeRep (..)
  , KnownType (..)
  , typeOf

  , ExprF (..)
  , All (..)
  , Fields (..)
  , Variant (..)
  , Selector (..)
  , Cases (..)

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
  , lift
  , join
  , drop
  , shift
  , memory

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

import Prelude hiding (Maybe, Either, Ordering, fst, snd, div, drop, mod)
import qualified Prelude
import qualified Control.Monad as Monad (join)
import qualified Data.Int as Haskell (Int8, Int16, Int32, Int64)
import qualified Data.Kind as Haskell (Type)
import Data.Proxy (Proxy (..))
import qualified Data.Word as Haskell (Word8, Word16, Word32, Word64)

import Pilot.Types.Nat
import Pilot.Types.Represented
import Pilot.EDSL.Fun as Fun

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
-- TODO define this in its own module.
newtype Expr
  (exprF) -- Kind is too long to write.
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> domain -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: domain) = Expr
  { getExpr :: (forall x y . exprF f val x y -> f x (val x y))
            -- ^ Interpret expressions
            -> (forall x y z . (y -> z) -> f x y -> f x z)
            -- ^ fmap
            -> (forall x y . y -> f x y)
            -- ^ pure
            -> (forall x y . f x (f x y) -> f x y)
            -- ^ join
            -> f s (val s t)
  }

-- | Put an existing value into an expression. Note the `s` parameter, which
-- ensures the value came from within the same expression context, for instance
-- from a `local` binding.
value :: val s t -> Expr exprF f val s t
value v = Expr $ \_interp _map pure' _join -> pure' v

-- TODO TBD whether we actually would want Expr to be a
-- functor/applicative/monad. I don't think it's useful at all.

{-
instance Functor (Expr f val s) where
  fmap f expr = Expr $ \interp' map' pure' join' ->
    map' f (getExpr expr interp' map' pure' join')

instance Applicative (Expr f val s) where
  pure x = Expr $ \_interp _map pure' _join -> pure' x
  (<*>)  = Monad.ap

instance Monad (Expr f val s) where
  return = pure
  expr >>= f = Expr $ \interp' map' pure' join' ->
    join' (map' (\x -> getExpr (f x) interp' map' pure' join') (getExpr expr interp' map' pure' join'))
-}

--lift :: f s (val s t) -> Expr exprF f val s t
--lift ft = Expr $ \_ _ _ _ -> ft

evalInMonad
  :: forall exprF f val s t.
     ( forall q . Monad (f q) )
  -- TODO use the ST trick later. Not in because I want flexibility for development
  -- => (forall q . Expr f val q t)
  => Expr exprF f val s t
  -> (forall x y . exprF f val x y -> f x (val x y))
  -> f s (val s t)
evalInMonad expr interp = getExpr expr interp fmap pure Monad.join

-- | NB: no constraints appear. A Monad instance is not needed until evaluation
-- time ('evalInMonad') which is nice; `f` and `val` remain truly unconstrained.
exprF :: forall exprF f val s t . exprF f val s t -> Expr exprF f val s t
exprF exprf = Expr $ \f map' pure' join' ->
  let v :: f s (val s t)
      v = f exprf
  in  join' (map' pure' v)

-- | Types for the pointwise EDSL: various numeric types, with finite sums and
-- products. As usual, the empty product is unit, and the empty sum is void.
-- There is no boolean type; it can be expressed as a sum of units.
data Type where
  Integer  :: Signedness -> Width -> Type
  Rational :: Type
  Product  :: [Type] -> Type
  Sum      :: [Type] -> Type
  Stream   :: Nat -> Type -> Type

instance Represented Type where
  type Rep Type = TypeRep

data Signedness where
  Signed   :: Signedness
  Unsigned :: Signedness

instance Represented Signedness where
  type Rep Signedness = SignednessRep

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

instance Represented Width where
  type Rep Width = WidthRep

data WidthRep (t :: Width) where
  Eight_t     :: WidthRep 'Eight
  Sixteen_t   :: WidthRep 'Sixteen
  ThirtyTwo_t :: WidthRep 'ThirtyTwo
  SixtyFour_t :: WidthRep 'SixtyFour

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

  Stream_t  :: NatRep nat -> TypeRep ty -> TypeRep ('Stream nat ty)

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
  SomeTypeRep (Sum_t _) `compare` SomeTypeRep (Stream_t _ _) = LT
  SomeTypeRep (Sum_t _) `compare` _ = GT

  SomeTypeRep (Stream_t n s) `compare` SomeTypeRep (Stream_t n' s') =
    (SomeNatRep n, SomeTypeRep s) `compare` (SomeNatRep n', SomeTypeRep s')
  SomeTypeRep (Stream_t _ _) `compare` _ = GT

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

instance (KnownNat n, KnownType t) => KnownType ('Stream n t) where
  typeRep _ = Stream_t (natRep (Proxy :: Proxy n)) (typeRep (Proxy :: Proxy t))

data PrimOpF
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Type)
  where
  Arithmetic :: ArithmeticOpF f val s t -> PrimOpF f val s t
  Bitwise :: BitwiseOpF f val s t -> PrimOpF f val s t
  Relative :: RelativeOpF f val s t -> PrimOpF f val s t

data ArithmeticOpF
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Type)
  where
  AddInteger :: TypeRep ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> ArithmeticOpF f val s ('Integer signedness width)
  SubInteger :: TypeRep ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> ArithmeticOpF f val s ('Integer signedness width)
  MulInteger :: TypeRep ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> ArithmeticOpF f val s ('Integer signedness width)
  DivInteger :: TypeRep ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> ArithmeticOpF f val s ('Integer signedness width)
  ModInteger :: TypeRep ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> Expr ExprF f val s ('Integer signedness width)
             -> ArithmeticOpF f val s ('Integer signedness width)
  NegInteger :: TypeRep ('Integer 'Signed width)
             -> Expr ExprF f val s ('Integer 'Signed width)
             -> ArithmeticOpF f val s ('Integer 'Signed width)

-- | Bitwise operations are permitted on all integral types. TODO maybe this
-- is not ideal. Should we give bit types which do not allow for arithmetic,
-- and demand explicit type conversions? Would maybe be useful.
data BitwiseOpF
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Type)
  where
  AndB :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> BitwiseOpF f val s ('Integer signedness width)
  OrB  :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> BitwiseOpF f val s ('Integer signedness width)
  XOrB :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> BitwiseOpF f val s ('Integer signedness width)
  NotB :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> BitwiseOpF f val s ('Integer signedness width)
  ShiftL :: TypeRep ('Integer signedness width)
         -> Expr ExprF f val s ('Integer signedness width)
         -> Expr ExprF f val s ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF f val s ('Integer signedness width)
  ShiftR :: TypeRep ('Integer signedness width)
         -> Expr ExprF f val s ('Integer signedness width)
         -> Expr ExprF f val s ('Integer 'Unsigned 'Eight)
         -> BitwiseOpF f val s ('Integer signedness width)

data RelativeOpF
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> Type -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: Type)
  where
  Cmp :: TypeRep ('Integer signedness width)
      -> Expr ExprF f val s ('Integer signedness width)
      -> Expr ExprF f val s ('Integer signedness width)
      -> RelativeOpF f val s Ordering

typeOf :: forall f val s t . KnownType t => Expr ExprF f val s t -> TypeRep t
typeOf _ = typeRep (Proxy :: Proxy t)

-- | Expressions in the pointwise EDSL. The `f` parameter represents the
-- _target_ or object language, for instance generated C code, or an in-Haskell
-- representation.
--
-- TODO FIXME should not take f, val, but instead a single recursive parameter
-- of kind `Type -> Haskell.Type` that is substituted for
--
--   Expr ExprF f val s
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

  PrimOp :: PrimOpF f val s t -> ExprF f val s t

  -- TODO safe upcasts
  -- TODO checked downcasts

  -- Compound data: algebraic datatypes

  -- TODO intro should take `Expr f val s . val s` rather than `val s`.

  IntroProduct :: TypeRep ('Product types)
               -> Fields f val s types
               -> ExprF f val s ('Product types)

  IntroSum     :: TypeRep ('Sum types)
               -> Variant f val s types
               -> ExprF f val s ('Sum types)

  ElimProduct :: TypeRep ('Product types)
              -> TypeRep r
              -> Selector f val s types r
              -> Expr ExprF f val s ('Product types)
              -> ExprF f val s r

  ElimSum     :: TypeRep ('Sum types)
              -> TypeRep r
              -> Cases f val s types r
              -> Expr ExprF f val s ('Sum types)
              -> ExprF f val s r

  -- Explicit binding, so that the programmer may control sharing.
  Local :: TypeRep t
        -> TypeRep r
        -> Expr ExprF f val s t
        -> (Expr ExprF f val s t -> Expr ExprF f val s r)
        -> ExprF f val s r

  -- | Any first-order function within expr can be "lifted" so that all of its
  -- arguments and its results are now streams. It must be fully applied, since
  -- this language does not have functions. Makes sense: all of the other
  -- expressions which take parameters are fully applied (intro/elim,
  -- arithmetic, etc).
  --
  -- NB: this also expresses "pure" or constant streams, when the argument list
  -- is empty.
  LiftStream :: NatRep n
             -> Args TypeRep args
             -> (Args (Expr ExprF f val s) args -> Expr ExprF f val s r)
             -- ^ The function being lifted.
             -> Args (Expr ExprF f val s) (MapArgs ('Stream n) args)
             -- ^ The arguments to the lifted function, but their types now have
             -- Stream n applied out front.
             -- An interpretation of this term therefore must be able to
             -- use `Stream n t` wherever `t` is required, so long as the result
             -- also has `Stream n` in front. This is like applicative functor
             -- style.
             -> ExprF f val s ('Stream n r)

  JoinStream :: TypeRep t
             -> NatRep n
             -> Expr ExprF f val s ('Stream n ('Stream n t))
             -> ExprF f val s ('Stream n t)

  DropStream :: TypeRep t
             -> NatRep n
             -> Expr ExprF f val s ('Stream ('S n) t)
             -> ExprF f val s ('Stream n t)

  -- Like DropStream it lowers the nat index, but the value at an instant of the
  -- stream doesn't change. This just says that a stream with more memory can
  -- stand in for a stream with less memory, whereas DropStream says that we
  -- can forget memory.
  ShiftStream :: TypeRep t
              -> NatRep ('S n)
              -> Expr ExprF f val s ('Stream ('S n) t)
              -> ExprF f val s ('Stream n t)

  -- | This is how memory is introduced into a program: give 1 or more initial
  -- values, then define the rest of the stream (possibly using those values).
  -- Notice that the stream given in the continuation is 1 less than the number
  -- of values given. That's because the latest/current value of the stream
  -- must not be used there, else it would be circular. If, for example, 1
  -- initial value is given, then DropStream allows us to take the latest value
  -- (not the one in memory), but we wouldn't want to be able to do that within
  -- the definition of the current value itself (i.e. the continuation here).
  MemoryStream :: TypeRep t
               -> NatRep ('S n)
               -> Vec ('S n) (Expr ExprF f val s t)
               -> (Expr ExprF f val s ('Stream n t) -> Expr ExprF f val s ('Stream 'Z t))
               -> ExprF f val s ('Stream ('S n) t)

data All (f :: k -> Haskell.Type) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

data Fields
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts :: [k])
  where
  AllF :: Fields f val s '[]
  AndF :: Expr ExprF f val s t -> Fields f val s ts -> Fields f val s (t ': ts)

data Variant
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts :: [k])
  where
  AnyV :: Expr ExprF f val s t -> Variant f val s (t ': ts)
  OrV  :: Variant f val s ts -> Variant f val s (t ': ts)

data Selector
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts  :: [k])
  (r   :: k)
  where
  AnyC :: TypeRep t
       -> (Expr ExprF f val s t -> Expr ExprF f val s r)
       -> Selector f val s (t ': ts) r
  OrC  :: Selector f val s ts r -> Selector f val s (t ': ts) r

data Cases
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> k -> Haskell.Type)
  (s   :: Haskell.Type)
  (ts  :: [k])
  (r   :: k)
  where
  AllC :: Cases f val s '[] r
  AndC :: TypeRep t
       -> (Expr ExprF f val s t -> Expr ExprF f val s r)
       -> Cases f val s ts r
       -> Cases f val s (t ': ts) r

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
unit :: Expr ExprF f val s Unit
unit = exprF $ IntroProduct unit_t AllF

type Void = 'Sum '[]

void_t :: TypeRep Void
void_t = Sum_t All

-- | An empty sum can be eliminated, but it cannot be introduced.
absurd :: TypeRep x -> Expr ExprF f val s Void -> Expr ExprF f val s x
absurd x_t void = exprF $ ElimSum void_t x_t AllC void

-- | Use a 1 + 1 type for boolean. Important to note that the first disjunct
-- stands for true. An interpreter may need to know that. A C backend could,
-- for instance, represent this as a byte, and use typical logical operators.
type Boolean = 'Sum '[ Unit, Unit ]

boolean_t :: TypeRep Boolean
boolean_t = Sum_t (And unit_t $ And unit_t $ All)

true :: Expr ExprF f val s Boolean
true = exprF $ IntroSum boolean_t (AnyV unit)

false :: Expr ExprF f val s Boolean
false = exprF $ IntroSum boolean_t (OrV $ AnyV unit)

elim_boolean
  :: forall val f s r .
     TypeRep r
  -> Expr ExprF f val s Boolean
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
elim_boolean trep vb cTrue cFalse = exprF $ ElimSum boolean_t trep
  (AndC unit_t (\_ -> cTrue) $ AndC unit_t (\_ -> cFalse) $ AllC)
  vb

if_else
  :: forall val f s r .
     TypeRep r
  -> Expr ExprF f val s Boolean
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
if_else = elim_boolean

type Ordering = 'Sum '[ Unit, Unit, Unit ]

ordering_t :: TypeRep Ordering
ordering_t = Sum_t (And unit_t $ And unit_t $ And unit_t $ All)

cmp :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s Ordering
cmp tr x y = exprF $ PrimOp $ Relative $ Cmp tr x y

lt :: Expr ExprF f val s Ordering
lt = exprF $ IntroSum ordering_t (AnyV unit)

eq :: Expr ExprF f val s Ordering
eq = exprF $ IntroSum ordering_t (OrV $ AnyV unit)

gt :: Expr ExprF f val s Ordering
gt = exprF $ IntroSum ordering_t (OrV $ OrV $ AnyV unit)

elim_ordering
  :: forall val f s r .
     TypeRep r
  -> Expr ExprF f val s Ordering
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
  -> Expr ExprF f val s r
elim_ordering trep vo cLt cEq cGt = exprF $ ElimSum ordering_t trep
  (AndC unit_t (\_ -> cLt) $ AndC unit_t (\_ -> cEq) $ AndC unit_t (\_ -> cGt) $ AllC)
  vo

type Pair (s :: Type) (t :: Type) = 'Product '[ s, t]

pair_t :: TypeRep s -> TypeRep t -> TypeRep (Pair s t)
pair_t s t = Product_t (And s $ And t $ All)

pair :: TypeRep a
     -> TypeRep b
     -> Expr ExprF f val s a
     -> Expr ExprF f val s b
     -> Expr ExprF f val s (Pair a b)
pair ta tb va vb = exprF $ IntroProduct (pair_t ta tb) (AndF va $ AndF vb $ AllF)

fst :: TypeRep a
    -> TypeRep b
    -> Expr ExprF f val s (Pair a b)
    -> Expr ExprF f val s a
fst ta tb vp = exprF $ ElimProduct (pair_t ta tb) ta
  (AnyC ta (\it -> it))
  vp

snd :: TypeRep a
    -> TypeRep b
    -> Expr ExprF f val s (Pair a b)
    -> Expr ExprF f val s b
snd ta tb vp = exprF $ ElimProduct (pair_t ta tb) tb
  (OrC $ AnyC tb (\it -> it))
  vp

type Maybe (t :: Type) = 'Sum '[ Unit, t ]

maybe_t :: TypeRep t -> TypeRep (Maybe t)
maybe_t t = Sum_t (And unit_t $ And t $ All)

just :: TypeRep t -> Expr ExprF f val s t -> Expr ExprF f val s (Maybe t)
just tt t = exprF $ IntroSum (maybe_t tt) (OrV (AnyV t))

nothing :: TypeRep t -> Expr ExprF f val s (Maybe t)
nothing tt = exprF $ IntroSum (maybe_t tt) (AnyV unit)

elim_maybe
  :: forall val f s t r .
     TypeRep t
  -> TypeRep r
  -> Expr ExprF f val s (Maybe t)
  -> (Expr ExprF f val s Unit -> Expr ExprF f val s r)
  -> (Expr ExprF f val s t    -> Expr ExprF f val s r)
  -> Expr ExprF f val s r
elim_maybe trt trr v cNothing cJust = exprF $ ElimSum trs trr
  (AndC unit_t cNothing $ AndC trt cJust $ AllC)
  v
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
  -> Expr ExprF f val s a
  -> Expr ExprF f val s (Either a b)
left ta tb va = exprF $ IntroSum (either_t ta tb) (AnyV va)

right
  :: TypeRep a
  -> TypeRep b
  -> Expr ExprF f val s b
  -> Expr ExprF f val s (Either a b)
right ta tb vb = exprF $ IntroSum (either_t ta tb) (OrV (AnyV vb))

elim_either
  :: forall a b c f val s .
     TypeRep a
  -> TypeRep b
  -> TypeRep c
  -> Expr ExprF f val s (Either a b)
  -> (Expr ExprF f val s a -> Expr ExprF f val s c)
  -> (Expr ExprF f val s b -> Expr ExprF f val s c)
  -> Expr ExprF f val s c
elim_either tra trb trc val cLeft cRight = exprF $ ElimSum (either_t tra trb) trc
  (AndC tra cLeft $ AndC trb cRight $ AllC)
  val

-- NB: we cannot have the typical Haskell list type. Recursive types are not
-- allowed.

uint8 :: Haskell.Word8 -> Expr ExprF f val s ('Integer 'Unsigned 'Eight)
uint8 w8 = exprF $ IntroInteger uint8_t (UInt8 w8)

uint16 :: Haskell.Word16 -> Expr ExprF f val s ('Integer 'Unsigned 'Sixteen)
uint16 w16 = exprF $ IntroInteger uint16_t (UInt16 w16)

uint32 :: Haskell.Word32 -> Expr ExprF f val s ('Integer 'Unsigned 'ThirtyTwo)
uint32 w32 = exprF $ IntroInteger uint32_t (UInt32 w32)

uint64 :: Haskell.Word64 -> Expr ExprF f val s ('Integer 'Unsigned 'SixtyFour)
uint64 w64 = exprF $ IntroInteger uint64_t (UInt64 w64)

int8 :: Haskell.Int8 -> Expr ExprF f val s ('Integer 'Signed 'Eight)
int8 i8 = exprF $ IntroInteger int8_t (Int8 i8)

int16 :: Haskell.Int16 -> Expr ExprF f val s ('Integer 'Signed 'Sixteen)
int16 i16 = exprF $ IntroInteger int16_t (Int16 i16)

int32 :: Haskell.Int32 -> Expr ExprF f val s ('Integer 'Signed 'ThirtyTwo)
int32 i32 = exprF $ IntroInteger int32_t (Int32 i32)

int64 :: Haskell.Int64 -> Expr ExprF f val s ('Integer 'Signed 'SixtyFour)
int64 i64 = exprF $ IntroInteger int64_t (Int64 i64)

add :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
add tr x y = exprF $ PrimOp $ Arithmetic $ AddInteger tr x y

sub :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
sub tr x y = exprF $ PrimOp $ Arithmetic $ SubInteger tr x y

mul :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
mul tr x y = exprF $ PrimOp $ Arithmetic $ MulInteger tr x y

div :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
div tr x y = exprF $ PrimOp $ Arithmetic $ DivInteger tr x y

mod :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
mod tr x y = exprF $ PrimOp $ Arithmetic $ ModInteger tr x y

neg :: TypeRep ('Integer 'Signed width)
    -> Expr ExprF f val s ('Integer 'Signed width)
    -> Expr ExprF f val s ('Integer 'Signed width)
neg tr x = exprF $ PrimOp $ Arithmetic $ NegInteger tr x

andB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
andB tr x y = exprF $ PrimOp $ Bitwise $ AndB tr x y

orB :: TypeRep ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
    -> Expr ExprF f val s ('Integer signedness width)
orB tr x y = exprF $ PrimOp $ Bitwise $ OrB tr x y

xorB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
xorB tr x y = exprF $ PrimOp $ Bitwise $ XOrB tr x y

notB :: TypeRep ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
     -> Expr ExprF f val s ('Integer signedness width)
notB tr x = exprF $ PrimOp $ Bitwise $ NotB tr x

shiftL :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> Expr ExprF f val s ('Integer 'Unsigned 'Eight)
       -> Expr ExprF f val s ('Integer signedness width)
shiftL tr x y = exprF $ PrimOp $ Bitwise $ ShiftL tr x y

shiftR :: TypeRep ('Integer signedness width)
       -> Expr ExprF f val s ('Integer signedness width)
       -> Expr ExprF f val s ('Integer 'Unsigned 'Eight)
       -> Expr ExprF f val s ('Integer signedness width)
shiftR tr x y = exprF $ PrimOp $ Bitwise $ ShiftR tr x y

local
  :: TypeRep t
  -> TypeRep r
  -> Expr ExprF f val s t
  -> (Expr ExprF f val s t -> Expr ExprF f val s r)
  -> Expr ExprF f val s r
local trt trr val k = exprF (Local trt trr val k)

-- TODO remove? probably not useful. 'lift' seems like a better type from a
-- usability perspective.
lift_ :: NatRep n
      -> Args TypeRep ts
      -> (Args (Expr ExprF f val s) ts -> Expr ExprF f val s r)
      -> Args (Expr ExprF f val s) (MapArgs ('Stream n) ts)
      -> Expr ExprF f val s ('Stream n r)
lift_ nrep argsrep f args = exprF $ LiftStream nrep argsrep f args

-- | Any first-order function over expressions can be "lifted" over streams:
-- all of the arguments and the result become streams.
--
-- This is like typical applicative functor style in Haskell. Such things cannot
-- be done directly in this EDSL, because it doesn't have functions.
lift :: NatRep n
     -> Args TypeRep ts
     -> Fun (Expr ExprF f val s) ('Sig ts r)
     -> Fun (Expr ExprF f val s) (Fun.Lift ('Stream n) ('Sig ts r))
lift nrep argsrep f = Fun.unapply (mkStreamRep nrep argsrep) $ \sargs ->
  exprF $ LiftStream nrep argsrep (Fun.apply f) sargs

-- | "Lift" the argument type reps into streams for a given prefix length.
mkStreamRep :: NatRep n -> Args TypeRep ts -> Args TypeRep (MapArgs ('Stream n) ts)
mkStreamRep _    Args            = Args
mkStreamRep nrep (Arg arep args) = Arg (Stream_t nrep arep) (mkStreamRep nrep args)

join :: TypeRep t
     -> NatRep n
     -> Expr ExprF f val s ('Stream n ('Stream n t))
     -> Expr ExprF f val s ('Stream n t)
join trep nrep ss = exprF $ JoinStream trep nrep ss

drop :: TypeRep t
     -> NatRep n
     -> Expr ExprF f val s ('Stream ('S n) t)
     -> Expr ExprF f val s ('Stream n t)
drop trep nrep s = exprF $ DropStream trep nrep s

shift :: TypeRep t
      -> NatRep ('S n)
      -> Expr ExprF f val s ('Stream ('S n) t)
      -> Expr ExprF f val s ('Stream n t)
shift trep nrep s = exprF $ ShiftStream trep nrep s

memory :: TypeRep t
       -> NatRep ('S n)
       -> Vec ('S n) (Expr ExprF f val s t)
       -> (Expr ExprF f val s ('Stream n t) -> Expr ExprF f val s ('Stream 'Z t))
       -> Expr ExprF f val s ('Stream ('S n) t)
memory trep nrep inits k = exprF $ MemoryStream trep nrep inits k
