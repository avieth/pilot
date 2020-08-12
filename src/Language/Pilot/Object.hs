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
  , UncheckedCast (..)
  , CheckedCast (..)
  , type Vector

  , lift
  , lift_
  , knot
  , shift
  , drop

  , unit
  , absurd
  , pair
  , true
  , false
  , if_then_else
  , if_then_else_
  , maybe
  , maybe_
  , just
  , nothing

  , u8
  , i8
  , plus
  , plus_u8

  , AutoLift (..)

  ) where

import Prelude hiding (Bool, Maybe, Either, maybe, id, drop)
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Language.Pilot.Expr
import qualified Language.Pilot.Meta as Meta
import Language.Pilot.Meta hiding (Type (..), Form)
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

data Form (repr :: Meta.Type Type -> Hask) (t :: Meta.Type Type) where

  Integer_Literal_UInt8_f  :: Haskell.Word8  -> Form repr (Obj (Constant UInt8))
  Integer_Literal_UInt16_f :: Haskell.Word16 -> Form repr (Obj (Constant UInt16))
  Integer_Literal_UInt32_f :: Haskell.Word32 -> Form repr (Obj (Constant UInt32))
  Integer_Literal_UInt64_f :: Haskell.Word64 -> Form repr (Obj (Constant UInt64))

  Integer_Literal_Int8_f  :: Haskell.Int8  -> Form repr (Obj (Constant Int8))
  Integer_Literal_Int16_f :: Haskell.Int16 -> Form repr (Obj (Constant Int16))
  Integer_Literal_Int32_f :: Haskell.Int32 -> Form repr (Obj (Constant Int32))
  Integer_Literal_Int64_f :: Haskell.Int64 -> Form repr (Obj (Constant Int64))

  Bytes_Literal_8_f  :: Haskell.Word8  -> Form repr (Obj (Constant Word8))
  Bytes_Literal_16_f :: Haskell.Word16 -> Form repr (Obj (Constant Word16))
  Bytes_Literal_32_f :: Haskell.Word32 -> Form repr (Obj (Constant Word32))
  Bytes_Literal_64_f :: Haskell.Word64 -> Form repr (Obj (Constant Word64))

  Integer_Add_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Subtract_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Multiply_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Divide_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Modulo_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    )
  Integer_Negate_f :: Form repr
    (   Obj (Constant ('Integer_t 'Signed_t width))
    :-> Obj (Constant ('Integer_t 'Signed_t width))
    )
  Integer_Abs_f :: Form repr
    (   Obj (Constant ('Integer_t 'Signed_t width))
    :-> Obj (Constant ('Integer_t 'Unsigned_t width))
    )
  Integer_Compare_f :: Form repr
    (   Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant ('Integer_t sign width))
    :-> Obj (Constant Cmp)
    )

  Bytes_And_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Or_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Xor_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Not_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Shiftl_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t 'W_One_t))
    :-> Obj (Constant ('Bytes_t width))
    )
  Bytes_Shiftr_f :: Form repr
    (   Obj (Constant ('Bytes_t width))
    :-> Obj (Constant ('Bytes_t 'W_One_t))
    :-> Obj (Constant ('Bytes_t width))
    )

  Product_Intro_f :: Fields r fields -> Form repr
    (r :-> Obj (Constant ('Product_t fields)))
  Product_Elim_f :: Selector fields q r -> Form repr
    (Obj (Constant ('Product_t fields)) :-> q)

  Sum_Intro_f :: Variant r variants -> Form repr
    (r :-> Obj (Constant ('Sum_t variants)))
  Sum_Elim_f :: Cases variants q r -> Form rerp
    (Obj (Constant ('Sum_t variants)) :-> q)

  Stream_Lift_f :: NatRep n -> Lift n s t -> Form repr (s :-> t)
  Stream_Knot_f :: Knot s t q i -> Form repr ((s :-> t) :-> (q :-> r) :-> (i :-> r))

  Stream_Drop_f :: Form repr
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))
  Stream_Shift_f :: Form repr
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))

  -- Let bindings for object-language values. To let-bind a meta-language
  -- value you would just use the Haskell let. Notice that the result can
  -- be a meta-language thing. That's key: you _are_ able to let-bind outside
  -- of meta-language products, for instance, thereby allowing the expression
  -- of sharing between more than one value without building a product in the
  -- object-language.
  Let_f :: Form repr (Obj x :-> (Obj x :-> r) :-> r)

-- | Used for product introduction.
-- `Fields repr r fields` means that if you have an `r`, then you can
-- introduce a product with `fields`.
data Fields (r :: Meta.Type Type) (fields :: [Point]) where
  F_All :: Fields Terminal '[]
  F_And :: Fields                          r            fields
        -> Fields (Obj (Constant field) :* r) (field ': fields)

-- | Used for sum introduction.
-- `Variant r variants` means that an `r` is sufficient to construct a
-- sum of `variants`.
data Variant (r :: Meta.Type Type) (variants :: [Point]) where
  V_This :: Variant (Obj (Constant variant)) (variant ': variants)
  V_That :: Variant r variants -> Variant r (variant ': variants)

data Selector (fields :: [Point]) (q :: Meta.Type Type) (r :: Meta.Type Type) where
  S_Here  :: Selector (field ': fields) (Obj (Constant field) :-> r) r
  S_There :: Selector           fields  q r
          -> Selector (field ': fields) q r

-- | `Cases repr variants q r` means that given a sum of `variants`, you can
-- get something of type `q` which will ultimately return an `r`. This GADT
-- tacks on a function for each variants of the sum.
--
-- NB: the return type `r` is a `Point`. This is crucial. It would not make
-- sense to allow for a meta-language thing to be computed from the
-- object-language case elimination.
data Cases (variants :: [Point]) (q :: Meta.Type Type) (r :: Point) where
  C_Any :: Cases '[] (Obj (Constant r)) r
  C_Or  :: Cases             variants                                      q  r
        -> Cases (variant ': variants) ((Obj (Constant variant) :-> Obj (Constant r)) :-> q) r

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

-- Trying to think of a cleaner way to do the Knot GADT, so that Terminals do
-- not show up at the end.
-- You always have to give at least one vector, so why not start with that?
--
--   Knot :: Vec ('S n) (repr (Obj ('Constant_t a))) -> 

-- TODO enumerate all casts.
data UncheckedCast (a :: Point) (b :: Point)
data CheckedCast (a :: Point) (b :: Point)

u8 :: Haskell.Word8 -> Expr (Meta.Form Form) repr (Obj (Constant UInt8))
u8 w = Meta.object $ Integer_Literal_UInt8_f w

i8 :: Haskell.Int8 -> Expr (Meta.Form Form) repr (Obj (Constant Int8))
i8 w = Meta.object $ Integer_Literal_Int8_f w

plus :: Expr (Meta.Form Form) repr
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
plus = Meta.object Integer_Add_f

-- | Specialized 'plus' to UInt8.
plus_u8 :: Expr (Meta.Form Form) repr
  (   Obj (Constant UInt8)
  :-> Obj (Constant UInt8)
  :-> Obj (Constant UInt8)
  )
plus_u8 = plus

-- | The formal product intro construction gives a function from a meta-language
-- product--in this case the terminal object--to the object-language thing, so
-- here we apply it to `specific terminal`
unit :: Expr (Meta.Form Form) repr (Obj (Constant Unit))
unit = (object $ Product_Intro_f F_All) <@> terminal

-- | The formal sum elim constructor has a base case that works for any type.
-- Since the empty sum requires only this base case, we don't even have to
-- construct anything of this type, so we get the typical `absurd` type.
absurd :: Expr (Meta.Form Form) repr (Obj (Constant Void) :-> Obj (Constant r))
absurd = object $ Sum_Elim_f C_Any

-- NB: an empty product cannot be eliminated, and an empty sum cannot be
-- introduced. The meta-language enforces this: there are no Selector or
-- Variant types for an empty field/variant list.

-- | Constructs a pair. The formal 'product_intro_f' gives a function from a
-- meta-language product with an explicit terminal in the rightmost position,
-- but we change it to be a curried from without the terminal.
pair :: Expr (Meta.Form Form) repr
  (Obj (Constant a) :-> Obj (Constant b) :-> Obj (Constant (Pair a b)))
pair = fun $ \a -> fun $ \b ->
  (object $ Product_Intro_f (F_And (F_And F_All))) <@> (a &> b &> terminal)

-- | The formal sum intro construction, like that of the product, gives a
-- meta-language function. The Variant value (V_That V_This) indicates which
-- variant to construct, and therefore what type is needed (in this case it's
-- the object-language unit, so 'unit' is used).
true :: Expr (Meta.Form Form) repr (Obj (Constant Bool))
true = (object $ Sum_Intro_f (V_That V_This)) <@> unit

false :: Expr (Meta.Form Form) repr (Obj (Constant Bool))
false = (object $ Sum_Intro_f V_This) <@> unit

if_then_else :: Expr (Meta.Form Form) repr
  (   Obj (Constant Bool)
  :-> (Obj (Constant Unit) :-> Obj (Constant r))
  :-> (Obj (Constant Unit) :-> Obj (Constant r))
  :-> Obj (Constant r)
  )
if_then_else = (object $ Sum_Elim_f (C_Or (C_Or C_Any)))

if_then_else_ :: Expr (Meta.Form Form) repr
  (   Obj (Constant Bool)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  )
if_then_else_ = fun $ \b -> fun $ \ifTrue -> fun $ \ifFalse -> 
  if_then_else <@> b <@> (fun $ \_ -> ifTrue) <@> (fun $ \_ -> ifFalse)

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

lift :: forall repr n s t .
        ( AutoLift n s t )
     => NatRep n
     -> Expr (Meta.Form Form) repr (s :-> t)
lift nrep = object $ Stream_Lift_f nrep (autoLift proxyN proxyS proxyT)
  where
  proxyS :: Proxy s
  proxyS = Proxy
  proxyT :: Proxy t
  proxyT = Proxy
  proxyN :: Proxy n
  proxyN = Proxy

lift_ :: NatRep n -> Lift n s t -> Expr (Meta.Form Form) repr (s :-> t)
lift_ n l = object $ Stream_Lift_f n l

-- Is lifting properly defined? It's good for many examples and use cases, but
-- what about something like if_then_else? Maybe the error is that
-- if_then_else should have `Obj (Constant r)` rather than `r`? Do we gain
-- anything by having `r` be possibly meta? I don't think so. In fact I think
-- it's just totally wrong!
--
-- Fixed. But still, if_then_else is an easy one. What about lifting a
-- maybe eliminator?

just :: Expr (Meta.Form Form) repr
  (Obj (Constant a) :-> Obj (Constant (Maybe a)))
just = object $ Sum_Intro_f (V_That V_This)

nothing :: Expr (Meta.Form Form) repr (Obj (Constant (Maybe s)))
nothing = (object $ Sum_Intro_f V_This) <@> unit

maybe :: Expr (Meta.Form Form) repr
  (   Obj (Constant (Maybe s))
  :-> (Obj (Constant Unit) :-> Obj (Constant r))
  :-> (Obj (Constant s) :-> Obj (Constant r))
  :-> Obj (Constant r)
  )
maybe = object $ Sum_Elim_f (C_Or (C_Or C_Any))

maybe_ :: Expr (Meta.Form Form) repr
  (   Obj (Constant r)
  :-> (Obj (Constant s) :-> Obj (Constant r))
  :-> Obj (Constant (Maybe s))
  :-> Obj (Constant r)
  )
maybe_ = fun $ \ifNothing -> fun $ \ifJust -> fun $ \m ->
  maybe <@> m <@> (fun $ \_ -> ifNothing) <@> ifJust

drop :: Expr (Meta.Form Form) repr
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
drop = object $ Stream_Drop_f

shift :: Expr (Meta.Form Form) repr
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
shift = object $ Stream_Shift_f

-- |
-- = Mutually-recursive memory streams.

-- | The most general, but comparatively verbose, way to write a
-- mutually-recursive memory stream.
knot :: Knot s t q i
     -> Expr (Meta.Form Form) repr
        ((s :-> t) :-> (q :-> r) :-> (i :-> r))
knot sig = object $ Stream_Knot_f sig
