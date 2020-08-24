{-|
Module      : Language.Pilot.Object
Description : Definition of the object-language
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Pilot.Object
  ( Point (..)
  , Type (..)

  , Constant
  , Varying

  , UInt8
  , UInt16
  , UInt32
  , UInt64
  , Int8
  , Int16
  , Int32
  , Int64
  , Word8
  , Word16
  , Word32
  , Word64
  , Product
  , Sum
  , Unit
  , Void
  , Bool
  , Cmp
  , Maybe
  , Pair
  , Either

  , Width (..)
  , Signedness (..)

  , Form (..)

  , Fields (..)
  , Variant (..)
  , Selector (..)
  , Cases (..)
  , Lift (..)
  , Knot (..)
  , Cast (..)
  , Wider (..)
  , type Vector

  , let_
  , local

  , u8
  , u16
  , u32
  , u64
  , i8
  , i16
  , i32
  , i64

  , add
  , subtract
  , multiply
  , divide
  , modulo
  , negate
  , abs
  , cmp

  , and
  , or
  , xor
  , complement
  , shiftl
  , shiftr

  , cast

  , bundle
  , project
  , choose
  , match

  , lift
  , lift_
  , constant
  , knot
  , shift
  , drop

  , unit
  , absurd
  , true
  , false
  , if_then_else
  , lnot
  , lor
  , land
  , maybe
  , just
  , nothing
  , pair
  , fst
  , snd

  , is_lt
  , is_gt
  , is_eq
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)

  , AutoLift (..)

  ) where

import Prelude hiding (Bool, Maybe, Either, maybe, id, drop, pair, fst, snd,
  const, subtract, negate, abs, and, or, (<), (>), (<=), (>=), (==), (/=))
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Language.Pilot.Meta (Obj, Terminal, type (:->), type (:*))
import qualified Language.Pilot.Meta as Meta
import Language.Pilot.Repr hiding (fst, snd)
import Language.Pilot.Types

data Width where
  W_One_t   :: Width
  W_Two_t   :: Width
  W_Four_t  :: Width
  W_Eight_t :: Width

data Signedness where
  Signed_t   :: Signedness
  Unsigned_t :: Signedness

-- | This data kind gives all of the "point" types: finite sums and products,
-- along with numeric and bitwise base types.
data Point where

  -- TODO may want to include fractional numbers.
  Integer_t :: Signedness -> Width -> Point
  Bytes_t :: Width -> Point

  -- The empty product is unit, the empty sum is void.

  Product_t :: [Point] -> Point
  Sum_t     :: [Point] -> Point

type Product ts = 'Product_t ts
type Sum ts = 'Sum_t ts

type UInt8  = 'Integer_t 'Unsigned_t 'W_One_t
type UInt16 = 'Integer_t 'Unsigned_t 'W_Two_t
type UInt32 = 'Integer_t 'Unsigned_t 'W_Four_t
type UInt64 = 'Integer_t 'Unsigned_t 'W_Eight_t

type Int8  = 'Integer_t 'Signed_t 'W_One_t
type Int16 = 'Integer_t 'Signed_t 'W_Two_t
type Int32 = 'Integer_t 'Signed_t 'W_Four_t
type Int64 = 'Integer_t 'Signed_t 'W_Eight_t

type Word8  = 'Bytes_t 'W_One_t
type Word16 = 'Bytes_t 'W_Two_t
type Word32 = 'Bytes_t 'W_Four_t
type Word64 = 'Bytes_t 'W_Eight_t

type Unit = 'Product_t '[]
type Void = 'Sum_t '[]

type Pair a b = 'Product_t '[ a, b ]

type Bool = 'Sum_t '[ Unit, Unit ]

-- | Comparison type, to replace the classic -1, 0, 1 motif with a proper
-- algebraic type.
--
-- Cmp = LT | EQ | GT
type Cmp = 'Sum_t '[ Unit, Unit, Unit ]

type Maybe a = 'Sum_t '[ Unit, a ]
type Either a b = 'Sum_t '[ a, b ]

-- | This data kind gives all of the types in the EDSL.
-- A key feature is that a Varying_t cannot contain another Varying_t.
data Type where
  Constant_t :: Point -> Type
  Varying_t  :: Nat -> Point -> Type

type Constant = 'Constant_t
type Varying = 'Varying_t

data Form (t :: Meta.Type Type) where

  Integer_Literal_UInt8_f  :: Haskell.Word8  -> Form (Obj (Constant UInt8))
  Integer_Literal_UInt16_f :: Haskell.Word16 -> Form (Obj (Constant UInt16))
  Integer_Literal_UInt32_f :: Haskell.Word32 -> Form (Obj (Constant UInt32))
  Integer_Literal_UInt64_f :: Haskell.Word64 -> Form (Obj (Constant UInt64))

  Integer_Literal_Int8_f  :: Haskell.Int8  -> Form (Obj (Constant Int8))
  Integer_Literal_Int16_f :: Haskell.Int16 -> Form (Obj (Constant Int16))
  Integer_Literal_Int32_f :: Haskell.Int32 -> Form (Obj (Constant Int32))
  Integer_Literal_Int64_f :: Haskell.Int64 -> Form (Obj (Constant Int64))

  Bytes_Literal_8_f  :: Haskell.Word8  -> Form (Obj (Constant Word8))
  Bytes_Literal_16_f :: Haskell.Word16 -> Form (Obj (Constant Word16))
  Bytes_Literal_32_f :: Haskell.Word32 -> Form (Obj (Constant Word32))
  Bytes_Literal_64_f :: Haskell.Word64 -> Form (Obj (Constant Word64))

  Integer_Add_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Subtract_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Multiply_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Divide_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Modulo_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Negate_f :: Form
    (   Obj (Constant ('Integer_t 'Signed_t width))
    :-> Obj (Constant ('Integer_t 'Signed_t width))
    )
  Integer_Abs_f :: Form
    (   Obj (Constant ('Integer_t 'Signed_t width))
    :-> Obj (Constant ('Integer_t 'Unsigned_t width))
    )
  Integer_Compare_f :: Form
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant Cmp)
    )

  Bytes_And_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Or_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Xor_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Complement_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Shiftl_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t 'W_One_t))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Shiftr_f :: Form
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t 'W_One_t))
    :-> Obj (Constant ('Bytes_t width))
    )

  Cast_f :: Cast a b -> Form
    (Obj (Constant a) :-> Obj (Constant b))

  -- | Product introduction takes a meta-language product containing all of
  -- the fields. The `Fields` value constrains `r` to be such a product, or
  -- the meta-language terminal object in case there are no fields, giving the
  -- object-language unit.
  Product_Intro_f :: Fields r fields -> Form
    (r :-> Obj (Constant ('Product_t fields)))

  -- | Sum introduction takes one variant, determined by the `Variant` value.
  Sum_Intro_f :: Variant r variants -> Form
    (r :-> Obj (Constant ('Sum_t variants)))

  -- | Product elimination takes one field selector.
  Product_Elim_f :: Selector fields q r -> Form
    (Obj (Constant ('Product_t fields)) :-> q)

  -- | Sum elimination takes a meta-language products of functions, one for
  -- each variant, with a common return value.
  --
  -- TODO look into making product elimination similar to this (no q parameter).
  Sum_Elim_f :: Cases variants r -> Form
    (Obj (Constant ('Sum_t variants)) :-> r)

  Stream_Lift_f :: NatRep n -> Lift n s t -> Form (s :-> t)
  Stream_Knot_f :: Knot s t q i -> Form ((s :-> t) :-> (q :-> r) :-> (i :-> r))

  Stream_Drop_f :: Form
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))
  Stream_Shift_f :: Form
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))

  -- Let bindings for object-language values. To let-bind a meta-language
  -- value you would just use the Haskell let. Notice that the result can
  -- be a meta-language thing. That's key: you _are_ able to let-bind outside
  -- of meta-language products, for instance, thereby allowing the expression
  -- of sharing between more than one value without building a product in the
  -- object-language.
  Let_f :: Form (x :-> (x :-> r) :-> r)

-- | Used for sum introduction.
-- `Variant r variants` means that an `r` is sufficient to construct a
-- sum of `variants`.
data Variant (r :: Meta.Type Type) (variants :: [Point]) where
  V_This :: Variant (Obj (Constant variant)) (variant ': variants)
  V_That :: Variant r variants -> Variant r (variant ': variants)

-- | Used for product introduction.
-- `Fields repr r fields` means that if you have an `r`, then you can
-- introduce a product with `fields`.
data Fields (r :: Meta.Type Type) (fields :: [Point]) where
  F_All :: Fields Terminal '[]
  F_And :: Fields                          r            fields
        -> Fields (Obj (Constant field) :* r) (field ': fields)

data Selector (fields :: [Point]) (q :: Meta.Type Type) (r :: Meta.Type Type) where
  S_Here  :: Selector (field ': fields) ((Obj (Constant field) :-> r) :-> r) r
  S_There :: Selector           fields  q r
          -> Selector (field ': fields) q r

-- | `Cases repr variants q r` means that given a sum of `variants`, you can
-- get something of type `r`. It is defined in such a way that `r` is always a
-- function from a product of case eliminators for each variant, returning a
-- common type--except when the variants is '[], in which case you can get any
-- type.
--
data Cases (variants :: [Point]) (r :: Meta.Type Type) where
  C_Any :: Cases '[] x
  C_Or  :: Cases             variants  (                                   q  :-> r)
        -> Cases (variant ': variants) (((Obj (Constant variant) :-> r) :* q) :-> r)

-- |
--
-- 1. Constant objects may be lifted to varying objects of any prefix size.
-- 2. Function arguments of type constant object may be lifted to function
--    arguments of type varying object of any prefix size, assuming the
--    right-hand-side of the function is also lifted on the same prefix size.
--
data Lift (n :: Nat) (s :: Meta.Type Type) (t :: Meta.Type Type) where
  Pure :: Lift n (Obj ('Constant_t a)) (Obj ('Varying_t n a))
  Ap   :: Lift n s t
       -> Lift n (Obj ('Constant_t a) :-> s) (Obj ('Varying_t n a) :-> t)

-- |
--
-- - `s` is the input product for the definition function, giving prefixes for
--   each stream determined by the vector inits.
-- - `t` is the output product for the definition function, giving suffixes for
--   each stream.
-- - `q` is the input product for the continuation function, or equivalently
--   the output product for the knot itself. It gives the whole streams, as
--   defined recursively by the definition function.
-- - `i` is the input product for the resulting function. This is an init vector
--   for each of the streams.
--
data Knot (s :: Meta.Type Type) (t :: Meta.Type Type) (q :: Meta.Type Type) (i :: Meta.Type Type) where
  Tied :: NatRep ('S n)
       -> Knot (Obj (Varying n a))
               (Obj (Varying 'Z a))
               (Obj (Varying ('S n) a))
               (Vector ('S n) (Obj (Constant a)))
  Tie  :: NatRep ('S n)
       -> Knot s t q i
       -> Knot ((Obj (Varying n a)) :* s)
               ((Obj (Varying 'Z a)) :* t)
               ((Obj (Varying ('S n) a)) :* q)
               ((Vector ('S n) (Obj (Constant a))) :* i)

-- | Constructs a vector type in Meta.Type of a given length. It's slightly
-- non-regular in that 0-length vectors are Terminal, but non-zero-length
-- vectors do not end in a Terminal.
type family Vector (n :: Nat) (t :: Meta.Type Type) :: Meta.Type Type where
  Vector     'Z  t = Terminal
  Vector ('S 'Z) t = t
  Vector ('S  n) t = t :* Vector n t

-- | Each constructor determines a cast from the left type to the right type.
data Cast (a :: Point) (b :: Point) where

  -- | Casts to wider numbers of the same signedness are allowed.
  UpCastInteger
    :: Wider width' width
    -> Cast ('Integer_t sign width) ('Integer_t sign width')

  -- | Casts to wider bytes are allowed.
  UpCastBytes
    :: Wider width' width
    -> Cast ('Bytes_t width) ('Bytes_t width')

  -- | An unsigned number may be cast to a signed number of the same width,
  -- with possibility of failure if the unsigned number is too big.
  --
  -- The opposite direction is not here because it is done by absolute value.
  CastToSigned :: Cast ('Integer_t 'Unsigned_t width) (Maybe ('Integer_t 'Signed_t width))
  -- | An unsigned number may always be cast to a bigger signed number.
  UpCastToSigned
    :: Wider width' width
    -> Cast ('Integer_t 'Unsigned_t width) ('Integer_t 'Signed_t width')

-- | Says that w1 is strictly wider than w2.
data Wider (w1 :: Width) (w2 :: Width) where

  TwoWiderOne :: Wider ('W_Two_t) ('W_One_t)

  FourWiderOne :: Wider ('W_Four_t) ('W_One_t)
  FourWiderTwo :: Wider ('W_Four_t) ('W_Two_t)

  EightWiderOne  :: Wider ('W_Eight_t) ('W_One_t)
  EightWiderTwo  :: Wider ('W_Eight_t) ('W_Two_t)
  EightWiderFour :: Wider ('W_Eight_t) ('W_Four_t)

let_ :: E Form f val (a :-> (a :-> b) :-> b)
let_ = formal Let_f

local :: E Form f val a -> (E Form f val a -> E Form f val b) -> E Form f val b
local x k = let_ <@> x <@> (fun $ \x' -> k x')

u8 :: Haskell.Word8 -> E Form f val (Obj (Constant UInt8))
u8 w = formal $ Integer_Literal_UInt8_f w

u16 :: Haskell.Word16 -> E Form f val (Obj (Constant UInt16))
u16 w = formal $ Integer_Literal_UInt16_f w

u32 :: Haskell.Word32 -> E Form f val (Obj (Constant UInt32))
u32 w = formal $ Integer_Literal_UInt32_f w

u64 :: Haskell.Word64 -> E Form f val (Obj (Constant UInt64))
u64 w = formal $ Integer_Literal_UInt64_f w

i8 :: Haskell.Int8 -> E Form f val (Obj (Constant Int8))
i8 i = formal $ Integer_Literal_Int8_f i

i16 :: Haskell.Int16 -> E Form f val (Obj (Constant Int16))
i16 i = formal $ Integer_Literal_Int16_f i

i32 :: Haskell.Int32 -> E Form f val (Obj (Constant Int32))
i32 i = formal $ Integer_Literal_Int32_f i

i64 :: Haskell.Int64 -> E Form f val (Obj (Constant Int64))
i64 i = formal $ Integer_Literal_Int64_f i

add :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
add = formal Integer_Add_f

subtract :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
subtract = formal Integer_Subtract_f

multiply :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
multiply = formal Integer_Multiply_f

divide :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
divide = formal Integer_Divide_f

modulo :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
modulo = formal Integer_Modulo_f

negate :: E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t width))
  :-> Obj (Constant ('Integer_t 'Signed_t width))
  )
negate = formal Integer_Negate_f

abs :: E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t   width))
  :-> Obj (Constant ('Integer_t 'Unsigned_t width))
  )
abs = formal Integer_Abs_f

cmp :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Cmp)
  )
cmp = formal Integer_Compare_f

and :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
and = formal Bytes_And_f

or :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
or = formal Bytes_Or_f

xor :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
xor = formal Bytes_Xor_f

complement :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
complement = formal Bytes_Complement_f

shiftl :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftl = formal Bytes_Shiftl_f

shiftr :: E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftr = formal Bytes_Shiftr_f

cast :: Cast a b -> E Form f val
  (Obj (Constant a) :-> Obj (Constant b))
cast c = formal (Cast_f c)

-- | Construct a product.
bundle :: Fields r fields -> E Form f val
  (r :-> Obj (Constant ('Product_t fields)))
bundle fields = formal (Product_Intro_f fields)

-- | Construct a sum.
choose :: Variant r variants -> E Form f val
  (r :-> Obj (Constant ('Sum_t variants)))
choose variant = formal (Sum_Intro_f variant)

-- | Eliminate a product
project :: Selector fields q r -> E Form f val
  (Obj (Constant ('Product_t fields)) :-> q)
project selector = formal (Product_Elim_f selector)

match :: Cases variants r -> E Form f val
  (Obj (Constant ('Sum_t variants)) :-> r)
match cases = formal (Sum_Elim_f cases)

-- | The formal product intro construction gives a function from a meta-language
-- product--in this case the terminal object--to the object-language thing, so
-- here we apply it to `specific terminal`
unit :: E Form f val (Obj (Constant Unit))
unit = formal (Product_Intro_f F_All) <@> terminal

-- | The formal sum elim constructor has a base case that works for any type.
-- Since the empty sum requires only this base case, we don't even have to
-- construct anything of this type, so we get the typical `absurd` type.
absurd :: E Form f val (Obj (Constant Void) :-> Obj (Constant r))
absurd = fun $ \impossible -> formal (Sum_Elim_f C_Any) <@> impossible <@> terminal

-- NB: an empty product cannot be eliminated, and an empty sum cannot be
-- introduced. The meta-language enforces this: there are no Selector or
-- Variant types for an empty field/variant list.

-- | The formal sum intro construction, like that of the product, gives a
-- meta-language function. The Variant value (V_That V_This) indicates which
-- variant to construct, and therefore what type is needed (in this case it's
-- the object-language unit, so 'unit' is used).
true :: E Form f val (Obj (Constant Bool))
true = formal (Sum_Intro_f (V_That V_This)) <@> unit

false :: E Form f val (Obj (Constant Bool))
false = formal (Sum_Intro_f V_This) <@> unit

if_then_else :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  )
if_then_else = fun $ \b -> fun $ \ifTrue -> fun $ \ifFalse ->
  formal (Sum_Elim_f (C_Or (C_Or C_Any))) <@> b <@> ((const <@> ifTrue) &> (const <@> ifFalse) &> terminal)

lnot :: E Form f val ( Obj (Constant Bool) :-> Obj (Constant Bool))
lnot = fun $ \b -> if_then_else <@> b <@> false <@> true

lor :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
lor = fun $ \a -> fun $ \b -> if_then_else <@> a <@> true <@> b

land :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
land = fun $ \a -> fun $ \b -> if_then_else <@> a <@> b <@> false

is_lt :: E Form f val (Obj (Constant Cmp) :-> Obj (Constant Bool))
is_lt = fun $ \x -> match (C_Or (C_Or (C_Or (C_Any)))) <@> x <@> cases
  where
  cases = (const <@> true) &> (const <@> false) &> (const <@> false) &> terminal

is_eq :: E Form f val (Obj (Constant Cmp) :-> Obj (Constant Bool))
is_eq = fun $ \x -> match (C_Or (C_Or (C_Or (C_Any)))) <@> x <@> cases
  where
  cases = (const <@> false) &> (const <@> true) &> (const <@> false) &> terminal

is_gt :: E Form f val (Obj (Constant Cmp) :-> Obj (Constant Bool))
is_gt = fun $ \x -> match (C_Or (C_Or (C_Or (C_Any)))) <@> x <@> cases
  where
  cases = (const <@> false) &> (const <@> false) &> (const <@> true) &> terminal

(<) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(<) = fun $ \a -> fun $ \b -> is_lt <@> (cmp <@> a <@> b)

(>) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(>) = fun $ \a -> fun $ \b -> is_gt <@> (cmp <@> a <@> b)

(==) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(==) = fun $ \a -> fun $ \b -> is_eq <@> (cmp <@> a <@> b)

(<=) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(<=) = fun $ \a -> fun $ \b -> local (cmp <@> a <@> b) $ \x ->
  lor <@> (is_lt <@> x) <@> (is_eq <@> x)

(>=) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(>=) = fun $ \a -> fun $ \b -> local (cmp <@> a <@> b) $ \x ->
  lor <@> (is_gt <@> x) <@> (is_eq <@> x)

(/=) :: E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Bool)
  )
(/=) = fun $ \a -> fun $ \b -> (lnot <.> is_eq) <@> (cmp <@> a <@> b)

class AutoLift n a b where
  autoLift :: Proxy n -> Proxy a -> Proxy b -> Lift n a b

instance AutoLift n (Obj ('Constant_t a)) (Obj ('Varying_t n a)) where
  autoLift _ _ _ = Pure

instance
  ( AutoLift n s t
  ) => AutoLift n (Obj ('Constant_t a) :-> s) (Obj ('Varying_t n a) :-> t)
  where
  autoLift pn _ _ = Ap (autoLift pn (Proxy :: Proxy s) (Proxy :: Proxy t))

-- TODO give custom type errors for unliftable things.

lift :: forall f val n s t .
        ( AutoLift n s t )
     => NatRep n
     -> E Form f val (s :-> t)
lift nrep = formal (Stream_Lift_f nrep (autoLift proxyN proxyS proxyT))
  where
  proxyS :: Proxy s
  proxyS = Proxy
  proxyT :: Proxy t
  proxyT = Proxy
  proxyN :: Proxy n
  proxyN = Proxy

lift_ :: NatRep n -> Lift n s t -> E Form f val (s :-> t)
lift_ n l = formal (Stream_Lift_f n l)

constant :: NatRep n -> E Form f val (Obj (Constant s) :-> Obj (Varying n s))
constant nrep = lift nrep

-- Is lifting properly defined? It's good for many examples and use cases, but
-- what about something like if_then_else? Maybe the error is that
-- if_then_else should have `Obj (Constant r)` rather than `r`? Do we gain
-- anything by having `r` be possibly meta? I don't think so. In fact I think
-- it's just totally wrong!
--
-- Fixed. But still, if_then_else is an easy one. What about lifting a
-- maybe eliminator?

just :: E Form f val
  (Obj (Constant a) :-> Obj (Constant (Maybe a)))
just = formal (Sum_Intro_f (V_That V_This))

nothing :: E Form f val (Obj (Constant (Maybe s)))
nothing = formal (Sum_Intro_f V_This) <@> unit

maybe :: E Form f val
  (   Obj (Constant r)
  :-> (Obj (Constant s) :-> Obj (Constant r))
  :-> Obj (Constant (Maybe s))
  :-> Obj (Constant r)
  )
maybe = fun $ \ifNothing -> fun $ \ifJust -> fun $ \m ->
  formal (Sum_Elim_f (C_Or (C_Or C_Any)))
    <@> m <@> ((fun $ \_ -> ifNothing) &> ifJust &> terminal)

-- | Constructs a pair. The formal 'product_intro_f' gives a function from a
-- meta-language product with an explicit terminal in the rightmost position,
-- but we change it to be a curried from without the terminal.
pair :: E Form f val
  (Obj (Constant a) :-> Obj (Constant b) :-> Obj (Constant (Pair a b)))
pair = fun $ \a -> fun $ \b ->
  formal (Product_Intro_f (F_And (F_And F_All))) <@> (a &> b &> terminal)

fst :: E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant a))
fst = fun $ \p -> formal (Product_Elim_f S_Here) <@> p <@> id

snd :: E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant b))
snd = fun $ \p -> formal (Product_Elim_f (S_There S_Here)) <@> p <@> id

drop :: E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
drop = formal Stream_Drop_f

shift :: E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
shift = formal Stream_Shift_f

-- |
-- = Mutually-recursive memory streams.

-- | The most general, but comparatively verbose, way to write a
-- mutually-recursive memory stream.
knot :: Knot s t q i
     -> E Form f val ((s :-> t) :-> (q :-> r) :-> (i :-> r))
knot sig = formal (Stream_Knot_f sig)
