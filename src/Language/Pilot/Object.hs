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
  ( Type (..)
  , TypeRep (..)

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
  , (+)
  , subtract
  , (-)
  , multiply
  , (*)
  , divide
  , div
  , modulo
  , mod
  , negate
  , neg
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
  , (||)
  , land
  , (&&)
  , implies
  , (==>)
  , maybe
  , just
  , nothing
  , isJust
  , isNothing
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

  , lift_prefix_size

  ) where

import Prelude hiding (Bool, Maybe, Either, maybe, id, drop, pair, fst, snd,
  const, subtract, negate, abs, and, or, mod, div, (<), (>), (<=), (>=), (==),
  (/=), (-), (+), (*), (||), (&&))
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Language.Pilot.Meta (Obj, Terminal, type (:->), type (:*))
import qualified Language.Pilot.Meta as Meta
import Language.Pilot.Repr hiding (fst, snd)
import Language.Pilot.Types

import Language.Pilot.Object.Point as Point hiding (Type, TypeRep)
import qualified Language.Pilot.Object.Point as Point

-- | This data kind gives all of the types in the EDSL.
-- A key feature is that a Varying_t cannot contain another Varying_t.
data Type where
  Constant_t :: Point.Type -> Type
  Varying_t  :: Nat -> Point.Type -> Type

data TypeRep (t :: Type) where
  Constant_r :: Point.TypeRep p -> TypeRep ('Constant_t p)
  Varying_r  :: NatRep n -> Point.TypeRep p -> TypeRep ('Varying_t n p)

instance Represented Type where
  type Rep Type = TypeRep

instance Known t => Known ('Constant_t t) where
  known _ = Constant_r (known (Proxy :: Proxy t))

instance (Known n, Known t) => Known ('Varying_t n t) where
  known _ = Varying_r (known (Proxy :: Proxy n)) (known (Proxy :: Proxy t))

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

  Stream_Lift_f :: Lift n s t -> Form (s :-> t)
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

-- | The type rep of the result of a stream lift always determines the prefix
-- size of the entire lift--assuming it's a valid lifted thing (first-order
-- function or a constant).
lift_prefix_size :: Meta.TypeRep TypeRep (s :-> t) -> Lift n s t -> NatRep n
lift_prefix_size (Meta.Arrow_r _ trep) lf = case lf of
  Pure -> case trep of
    Meta.Object_r (Varying_r nrep _) -> nrep
  Ap _ -> case trep of
    Meta.Arrow_r (Meta.Object_r (Varying_r nrep _)) _ -> nrep

-- | Used for sum introduction.
-- `Variant r variants` means that an `r` is sufficient to construct a
-- sum of `variants`.
data Variant (r :: Meta.Type Type) (variants :: [Point.Type]) where
  V_This :: Variant (Obj (Constant variant)) (variant ': variants)
  V_That :: Variant r variants -> Variant r (variant ': variants)

-- | Used for product introduction.
-- `Fields repr r fields` means that if you have an `r`, then you can
-- introduce a product with `fields`.
data Fields (r :: Meta.Type Type) (fields :: [Point.Type]) where
  F_All :: Fields Terminal '[]
  F_And :: Fields                          r            fields
        -> Fields (Obj (Constant field) :* r) (field ': fields)

data Selector (fields :: [Point.Type]) (q :: Meta.Type Type) (r :: Meta.Type Type) where
  S_Here  :: Selector (field ': fields) ((Obj (Constant field) :-> r) :-> r) r
  S_There :: Selector           fields  q r
          -> Selector (field ': fields) q r

-- | `Cases repr variants q r` means that given a sum of `variants`, you can
-- get something of type `r`. It is defined in such a way that `r` is always a
-- function from a product of case eliminators for each variant, returning a
-- common type--except when the variants is '[], in which case you can get any
-- type.
--
data Cases (variants :: [Point.Type]) (r :: Meta.Type Type) where
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
data Cast (a :: Point.Type) (b :: Point.Type) where

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

let_ :: (Known a, Known b) => E Form f val (a :-> (a :-> b) :-> b)
let_ = formal Let_f

-- | Same as 'let_', but using typical Haskell functions rather than the
-- fun/<@> construction.
local
  :: (Known a, Known b)
  => E Form f val a
  -> (E Form f val a -> E Form f val b)
  -> E Form f val b
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

add :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
add = formal Integer_Add_f

infixl 6 +
(+) :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a + b = add <@> a <@> b

subtract :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
subtract = formal Integer_Subtract_f

infixl 6 -
(-) :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a - b = subtract <@> a <@> b

multiply :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
multiply = formal Integer_Multiply_f

infixl 7 *
(*) :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a * b = multiply <@> a <@> b

divide :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
divide = formal Integer_Divide_f

div :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a `div` b = divide <@> a <@> b

modulo :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
modulo = formal Integer_Modulo_f

mod :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a `mod` b = modulo <@> a <@> b

negate :: Known width => E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t width))
  :-> Obj (Constant ('Integer_t 'Signed_t width))
  )
negate = formal Integer_Negate_f

neg :: (Known width)
    => E Form f val (Obj (Constant ('Integer_t 'Signed_t width)))
    -> E Form f val (Obj (Constant ('Integer_t 'Signed_t width)))
neg a = negate <@> a

abs :: Known width => E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t   width))
  :-> Obj (Constant ('Integer_t 'Unsigned_t width))
  )
abs = formal Integer_Abs_f

cmp :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Cmp)
  )
cmp = formal Integer_Compare_f

and :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
and = formal Bytes_And_f

or :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
or = formal Bytes_Or_f

xor :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
xor = formal Bytes_Xor_f

complement :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
complement = formal Bytes_Complement_f

shiftl :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftl = formal Bytes_Shiftl_f

shiftr :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftr = formal Bytes_Shiftr_f

cast :: (Known a, Known b) => Cast a b -> E Form f val
  (Obj (Constant a) :-> Obj (Constant b))
cast c = formal (Cast_f c)

-- | Construct a product.
bundle :: (Known ('Product_t fields), Known r) => Fields r fields -> E Form f val
  (r :-> Obj (Constant ('Product_t fields)))
bundle fields = formal (Product_Intro_f fields)

-- | Construct a sum.
choose :: (Known ('Sum_t variants), Known r) => Variant r variants -> E Form f val
  (r :-> Obj (Constant ('Sum_t variants)))
choose variant = formal (Sum_Intro_f variant)

-- | Eliminate a product
project :: (Known ('Product_t fields), Known q) => Selector fields q r -> E Form f val
  (Obj (Constant ('Product_t fields)) :-> q)
project selector = formal (Product_Elim_f selector)

match :: (Known ('Sum_t variants), Known r) => Cases variants r -> E Form f val
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
absurd :: Known r => E Form f val (Obj (Constant Void) :-> Obj (Constant r))
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

if_then_else_ :: Known r => E Form f val
  (   Obj (Constant Bool)
  :-> r
  :-> r
  :-> r
  )
if_then_else_ = fun $ \b -> fun $ \ifTrue -> fun $ \ifFalse ->
  formal (Sum_Elim_f (C_Or (C_Or C_Any))) <@> b <@> ((const <@> ifFalse) &> (const <@> ifTrue) &> terminal)

if_then_else
  :: Known r
  => E Form f val (Obj (Constant Bool))
  -> E Form f val r -- True case
  -> E Form f val r -- False case
  -> E Form f val r
if_then_else b ifTrue ifFalse = formal (Sum_Elim_f (C_Or (C_Or C_Any)))
  <@> b
  -- Note the order, w.r.t. the 'false' and 'true' functions: the first variant
  -- represents false.
  <@> ((const <@> ifFalse) &> (const <@> ifTrue) &> terminal)

lnot :: E Form f val ( Obj (Constant Bool) :-> Obj (Constant Bool))
lnot = fun $ \b -> if_then_else_ <@> b <@> false <@> true

lor :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
lor = fun $ \a -> fun $ \b -> if_then_else_ <@> a <@> true <@> b

infixr 2 ||
(||) :: E Form f val (Obj (Constant Bool))
     -> E Form f val (Obj (Constant Bool))
     -> E Form f val (Obj (Constant Bool))
x || y = lor <@> x <@> y

land :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
land = fun $ \a -> fun $ \b -> if_then_else_ <@> a <@> b <@> false

infixr 3 &&
(&&) :: E Form f val (Obj (Constant Bool))
     -> E Form f val (Obj (Constant Bool))
     -> E Form f val (Obj (Constant Bool))
x && y = land <@> x <@> y

implies :: E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
implies = fun $ \a -> fun $ \b -> (lnot <@> a) || b

infixr 1 ==>
(==>) :: E Form f val (Obj (Constant Bool))
      -> E Form f val (Obj (Constant Bool))
      -> E Form f val (Obj (Constant Bool))
x ==> y = implies <@> x <@> y


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

(<) :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant Bool))
(<) a b = is_lt <@> (cmp <@> a <@> b)

(>) :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant Bool))
(>) a b = is_gt <@> (cmp <@> a <@> b)

(<=) :: (Known sign, Known width)
     => E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant Bool))
(<=) a b = local (cmp <@> a <@> b) $ \x ->
  lor <@> (is_lt <@> x) <@> (is_eq <@> x)

(>=) :: (Known sign, Known width)
     => E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant Bool))
(>=) a b = local (cmp <@> a <@> b) $ \x ->
  lor <@> (is_gt <@> x) <@> (is_eq <@> x)

(==) :: (Known sign, Known width)
     => E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant Bool))
(==) a b = is_eq <@> (cmp <@> a <@> b)

(/=) :: (Known sign, Known width)
     => E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant Bool))
(/=) a b = (lnot <.> is_eq) <@> (cmp <@> a <@> b)

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
        (Known s, Known t, AutoLift n s t)
     => NatRep n
     -> E Form f val (s :-> t)
lift _ = formal (Stream_Lift_f (autoLift proxyN proxyS proxyT))
  where
  proxyS :: Proxy s
  proxyS = Proxy
  proxyT :: Proxy t
  proxyT = Proxy
  proxyN :: Proxy n
  proxyN = Proxy

lift_ :: (Known s, Known t) => Lift n s t -> E Form f val (s :-> t)
lift_ l = formal (Stream_Lift_f l)

constant :: forall f val n s t . (Known n, Known s) => E Form f val
  (Obj (Constant s) :-> Obj (Varying n s))
constant = lift (known (Proxy :: Proxy n))

-- Is lifting properly defined? It's good for many examples and use cases, but
-- what about something like if_then_else? Maybe the error is that
-- if_then_else should have `Obj (Constant r)` rather than `r`? Do we gain
-- anything by having `r` be possibly meta? I don't think so. In fact I think
-- it's just totally wrong!
--
-- Fixed. But still, if_then_else is an easy one. What about lifting a
-- maybe eliminator?

just :: Known a
     => E Form f val (Obj (Constant a))
     -> E Form f val (Obj (Constant (Maybe a)))
just a = formal (Sum_Intro_f (V_That V_This)) <@> a

nothing :: Known s => E Form f val (Obj (Constant (Maybe s)))
nothing = formal (Sum_Intro_f V_This) <@> unit

maybe :: (Known s, Known r) => E Form f val
  (   r
  :-> (Obj (Constant s) :-> r)
  :-> Obj (Constant (Maybe s))
  :-> r
  )
maybe = fun $ \ifNothing -> fun $ \ifJust -> fun $ \m ->
  formal (Sum_Elim_f (C_Or (C_Or C_Any)))
    <@> m <@> ((fun $ \_ -> ifNothing) &> ifJust &> terminal)

isJust :: Known a => E Form f val (Obj (Constant (Maybe a)) :-> Obj (Constant Bool))
isJust = fun $ \m -> maybe <@> false <@> (const <@> true) <@> m

isNothing :: Known a => E Form f val (Obj (Constant (Maybe a)) :-> Obj (Constant Bool))
isNothing = fun $ \m -> maybe <@> true <@> (const <@> false) <@> m

-- | Constructs a pair. The formal 'product_intro_f' gives a function from a
-- meta-language product with an explicit terminal in the rightmost position,
-- but we change it to be a curried from without the terminal.
pair :: (Known a, Known b) => E Form f val
  (Obj (Constant a) :-> Obj (Constant b) :-> Obj (Constant (Pair a b)))
pair = fun $ \a -> fun $ \b ->
  formal (Product_Intro_f (F_And (F_And F_All))) <@> (a &> b &> terminal)

fst :: (Known a, Known b) => E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant a))
fst = fun $ \p -> formal (Product_Elim_f S_Here) <@> p <@> identity

snd :: (Known a, Known b) => E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant b))
snd = fun $ \p -> formal (Product_Elim_f (S_There S_Here)) <@> p <@> identity

drop :: (Known n, Known t) => E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
drop = formal Stream_Drop_f

shift :: (Known n, Known t) => E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
shift = formal Stream_Shift_f

-- |
-- = Mutually-recursive memory streams.

-- | The most general, but comparatively verbose, way to write a
-- mutually-recursive memory stream.
knot :: (Known s, Known t, Known q, Known r, Known i)
     => Knot s t q i
     -> E Form f val ((s :-> t) :-> (q :-> r) :-> (i :-> r))
knot sig = formal (Stream_Knot_f sig)
