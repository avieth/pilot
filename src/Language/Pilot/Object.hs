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
{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE TypeFamilyDependencies #-}

module Language.Pilot.Object
  ( Type (..)
  , TypeRep (..)
  , Language.Pilot.Object.decEq

  , Constant
  , Varying
  , Program

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

  , pattern Varying
  , pattern Constant
  , pattern Program
  , varying_t
  , to_constant_t
  , constant_t
  , program_t
  , uint8_t
  , uint16_t
  , uint32_t
  , uint64_t
  , int8_t
  , int16_t
  , int32_t
  , int64_t
  , cmp_t
  , maybe_t
  , either_t
  , pair_t
  , bool_t
  , void_t
  , unit_t

  , Width (..)
  , Signedness (..)

  , Form (..)

  , Fields (..)
  , Variant (..)
  , Selector (..)
  , Cases (..)
  , Knot (..)
  , Cast (..)
  , Wider (..)
  , type Vector

  , let_
  , let_auto
  , local
  , local_auto

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
  , compare_auto
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

  , map
  , map_auto
  , constant
  , constant_auto
  , knot
  , knot_auto
  , shift
  , shift_auto
  , drop
  , drop_auto

  , prog_map
  , prog_pure
  , prog_ap
  , prog_join
  , prog_bind
  , (>>=)

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
  , pair_auto
  , fst
  , snd
  , fst_auto
  , snd_auto

  , is_lt
  , is_gt
  , is_eq
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)

  , MapImage (..)
  , KnownMapPreImage (..)
  , vectorMapImage
  , vector_t

  ) where

import Prelude hiding (Bool, Maybe, Either, maybe, id, drop, pair, fst, snd,
  const, subtract, negate, abs, and, or, mod, div, (<), (>), (<=), (>=), (==),
  (/=), (-), (+), (*), (||), (&&), map, (>>=), (>>))
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Language.Pilot.Meta (Obj, Terminal, type (:->), type (:*), (.->), (.*),
  pattern Obj)
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
  -- | An endofunctor on `Meta.Type Type` (it makes a `Type`, whihc is in
  -- `Meta.Type Type`). Akin to IO in Haskell.
  Program_t  :: Meta.Type Type -> Type

data TypeRep (t :: Type) where
  Constant_r :: Point.TypeRep p -> TypeRep ('Constant_t p)
  Varying_r  :: NatRep n -> Point.TypeRep p -> TypeRep ('Varying_t n p)
  Program_r  :: Meta.TypeRep TypeRep t -> TypeRep ('Program_t t)

{-# COMPLETE Constant, Varying, Program #-}

pattern Constant   p = Constant_r   p
pattern Varying  n p = Varying_r  n p
pattern Program    p = Program_r    p

type Constant = 'Constant_t
type Varying  = 'Varying_t
type Program  = 'Program_t

decEq :: DecEq TypeRep

decEq (Constant_r  s) (Constant_r  t) = case Point.decEq s t of
  Nothing   -> Nothing
  Just Refl -> Just Refl

decEq (Varying_r n s) (Varying_r m t) = case natEq n m of
  Nothing   -> Nothing
  Just Refl -> case Point.decEq s t of
    Nothing   -> Nothing
    Just Refl -> Just Refl

decEq (Program_r s) (Program_r t) = case testEquality s t of
  Nothing   -> Nothing
  Just Refl -> Just Refl

decEq _ _ = Nothing

instance TestEquality TypeRep where
  testEquality = Language.Pilot.Object.decEq

varying_t :: NatRep n -> Point.TypeRep t -> TypeRep (Varying n t)
varying_t = Varying_r

constant_t :: Point.TypeRep t -> TypeRep (Constant t)
constant_t = Constant_r

to_constant_t :: TypeRep (Constant t) -> Point.TypeRep t
to_constant_t (Constant_r trep) = trep

program_t :: Meta.TypeRep TypeRep t -> TypeRep (Program t)
program_t = Program_r

instance Represented Type where
  type Rep Type = TypeRep

instance Known t => Known ('Constant_t t) where
  known _ = Constant_r (known (Proxy :: Proxy t))

instance (Known n, Known t) => Known ('Varying_t n t) where
  known _ = Varying_r (known (Proxy :: Proxy n)) (known (Proxy :: Proxy t))

instance Known t => Known ('Program_t t) where
  known _ = Program_r (known (Proxy :: Proxy t))

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
    (   Obj (Constant r) -- If x < y
    :-> Obj (Constant r) -- If x = y
    :-> Obj (Constant r) -- If x > y
    :-> Obj (Constant ('Integer_t sign width)) -- x
    :-> Obj (Constant ('Integer_t sign width)) -- y
    :-> Obj (Constant r)
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
  Product_Elim_f :: Selector fields field -> Form
    (Obj (Constant ('Product_t fields)) :-> Obj (Constant field))

  -- | Sum elimination takes a meta-language products of functions, one for
  -- each variant, with a common return value.
  Sum_Elim_f :: Cases variants r -> Form
    (Obj (Constant ('Sum_t variants)) :-> r)

  -- | The constant and varying types are related by a functor: for any prefix
  -- size, there is an applicative functor from constants to varyings of that
  -- prefix size. It's analogous to a Haskell zip list, except things are
  -- weirder here because it's not an endo functor and its domain does not
  -- even include function types.
  --
  -- The `MapImage` values are used to prove that the ends of the arrows in
  -- the constant category `s` and `q` are of the proper form, and that the
  -- ends of the corresponding arrow in the varying category, `t` and `r`,
  -- correspond to them.
  --
  -- This expresses the notion of "pure" by setting s ~ t ~ Terminal, since
  --   () -> a ~ a
  --
  -- TODO this has a categorical explanation that needs to be written out
  -- properly.
  Stream_Map_f  :: NatRep n -> MapImage n s t -> MapImage n q r -> Form
    ((s :-> q) :-> (t :-> r))

  -- | The Knot GADT ensures that the function `s :-> t` defines a
  -- mutually-recursive set of streams without using the Program type. This
  -- means that it's impossible to do a knot within another knot definition.
  Stream_Knot_f :: Knot s t i r -> Form ((s :-> t) :-> (i :-> Obj (Program r)))

  Stream_Drop_f :: Form
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))
  Stream_Shift_f :: Form
    (Obj (Varying ('S n) t) :-> Obj (Varying n t))

  Program_Map_f  :: Form ((s :-> t) :-> (Obj (Program s) :-> Obj (Program t)))
  Program_Pure_f :: Form (t :-> Obj (Program t))
  Program_Ap_f   :: Form (Obj (Program (s :-> t)) :-> Obj (Program s) :-> Obj (Program t))
  Program_Join_f :: Form (Obj (Program (Obj (Program t))) :-> Obj (Program t))

  -- Objects may be let-bound, to introduce sharing.
  --
  -- Notice that the result can be a meta-language thing. You _are_ able to
  -- let-bind outside of meta-language products, for instance, thereby allowing
  -- the expression of sharing between more than one value without building a
  -- product in the object-language.
  --
  -- TODO discuss semantics for let-binding of Varying and Program types.
  Let_f :: Form (Obj x :-> (Obj x :-> r) :-> r)

-- | Proof that t is the image of s in the functor map from constants to
-- varyings of a given prefix size n.
data MapImage (n :: Nat) (s :: Meta.Type Type) (t :: Meta.Type Type) where
  MapTerminal  :: MapImage n Terminal           Terminal
  MapObject    :: MapImage n (Obj (Constant t)) (Obj (Varying n t))
  MapProduct   :: MapImage n  a                  s
               -> MapImage n       b                  t
               -> MapImage n (a :* b)           (s :* t)

vectorMapImage
  :: Proxy t
  -> NatRep n
  -> NatRep m
  -> MapImage n (Vector m (Obj (Constant t))) (Vector m (Obj (Varying n t)))
vectorMapImage _  nrep Z_Rep                  = MapTerminal
vectorMapImage _  nrep (S_Rep Z_Rep)          = MapObject
vectorMapImage pt nrep (S_Rep mrep@(S_Rep _)) = MapProduct MapObject (vectorMapImage pt nrep mrep)

-- | If the type of a preimage of the functor map from constants to varyings
-- is known statically, then the MapImage can be derived from it.
class Known (C n s) => KnownMapPreImage n (s :: Meta.Type Type) where
  type C n s :: Meta.Type Type
  knownMapPreImage :: Proxy n -> Proxy s -> MapImage n s (C n s)

instance KnownMapPreImage n Terminal where
  type C n Terminal = Terminal
  knownMapPreImage _ _ = MapTerminal

instance (Known n, Known t) => KnownMapPreImage n (Obj (Constant t)) where
  type C n (Obj (Constant t)) = Obj (Varying n t)
  knownMapPreImage _ _ = MapObject

instance (KnownMapPreImage n a, KnownMapPreImage n b) => KnownMapPreImage n (a :* b) where
  type C n (a :* b) = (C n a :* C n b)
  knownMapPreImage pn _ = MapProduct (knownMapPreImage pn pa) (knownMapPreImage pn pb)
    where
    pa :: Proxy a
    pa = Proxy
    pb :: Proxy b
    pb = Proxy

-- TODO type error for `C n (a :-> b)`? It's confusing to get this error, which
-- happens when you try to map_ a curried function.

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

data Selector (fields :: [Point.Type]) (r :: Point.Type) where
  S_Here  :: Selector (field ': fields) field
  S_There :: Selector           fields  r
          -> Selector (field ': fields) r

-- | TODO explain
data Cases (variants :: [Point.Type]) (r :: Meta.Type Type) where
  C_Any :: Cases '[] (Terminal  :-> Obj (Constant r))
  C_Or  :: Cases variants (q  :-> Obj (Constant r))
        -> Cases (variant ': variants) (((Obj (Constant variant) :-> Obj (Constant r)) :* q) :-> Obj (Constant r))

-- |
--
-- - `s` is the input product for the definition function, giving prefixes for
--   each stream determined by the vector inits.
-- - `t` is the output product for the definition function, giving suffixes for
--   each stream.
-- - `i` is the input product for the resulting function. This is an init vector
--   for each of the streams.
-- - `r` is the outsputs: the streams with their full prefix sizes.
--
data Knot (s :: Meta.Type Type) (t :: Meta.Type Type) (i :: Meta.Type Type) (r :: Meta.Type Type) where
  Tied :: NatRep ('S n)
       -> Point.TypeRep a
       -> Knot (Obj (Varying n a))
               (Obj (Varying 'Z a))
               (Vector ('S n) (Obj (Constant a)))
               (Obj (Varying ('S n) a))
  Tie  :: NatRep ('S n)
       -> Point.TypeRep a
       -> Knot s t i r
       -> Knot ((Obj (Varying n a)) :* s)
               ((Obj (Varying 'Z a)) :* t)
               ((Vector ('S n) (Obj (Constant a))) :* i)
               ((Obj (Varying ('S n) a)) :* r)

-- | Constructs a vector type in Meta.Type of a given length. It's slightly
-- non-regular in that 0-length vectors are Terminal, but non-zero-length
-- vectors do not end in a Terminal.
--
-- This is useful for expressing known- but variable-length products _inside_
-- the EDSL as meta-language products.
--
-- TODO is this not injective? It's not, for
--
--   Vector (S Z) Terminal = Vector Z Terminal
--
-- If it were restricuted to vectors of objects, then I think it would be.
--
--   Vector    Z  (Obj t) = Terminal
--   Vector (S Z) (Obj t) = Obj t
--   Vector (S n) (Obj t) = Obj t :* Vector 
--
type family Vector (n :: Nat) (t :: Meta.Type Type) :: Meta.Type Type where
  Vector     'Z  t = Terminal
  Vector ('S 'Z) t = t
  Vector ('S  n) t = t :* Vector n t

vector_t :: NatRep n -> Meta.TypeRep TypeRep t -> Meta.TypeRep TypeRep (Vector n t)
vector_t Z_Rep                  _ = Meta.terminal_t
vector_t (S_Rep Z_Rep)          t = t
vector_t (S_Rep nrep@(S_Rep _)) t = t .* vector_t nrep t

-- | A product of objects of a given cardinality. Key feature is that it's
-- injective. That's why we don't have a case for the empty vector.
--
-- TODO this is not used at the moment, but it's possible that, if we replace
-- Vector with it, we could get a nicer UX?
type family VectorObj (n :: Nat) (t :: Type) = (r :: Meta.Type Type) | r -> n t where
  VectorObj ('S 'Z) t = Obj t
  VectorObj ('S  n) t = Obj t :* VectorObj n t

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
  --
  -- TODO don't give a Maybe; instead take two terms, one in case it's nothing
  -- and one in case it's properly casted.
  CastToSigned :: Cast
    ('Integer_t 'Unsigned_t width)
    (Maybe ('Integer_t 'Signed_t width))

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

let_ :: TypeRep a
     -> Meta.TypeRep TypeRep b
     -> E Form f val (Obj a :-> (Obj a :-> b) :-> b)
let_ arep brep = formal rep Let_f
  where
  rep =    Meta.object_t arep
      .-> (Meta.object_t arep .-> brep)
      .-> brep

let_auto :: (Known a, Known b) => E Form f val
  (Obj a :-> (Obj a :-> b) :-> b)
let_auto = let_ auto auto

-- | Same as 'let_', but using typical Haskell functions rather than the
-- fun/<@> construction.
local :: TypeRep a
      -> Meta.TypeRep TypeRep b
      -> E Form f val (Obj a)
      -> (E Form f val (Obj a) -> E Form f val b)
      -> E Form f val b
local arep brep x k = let_ arep brep <@> x <@> (fun $ \x' -> k x')

local_auto
  :: (Known a, Known b)
  => E Form f val (Obj a)
  -> (E Form f val (Obj a) -> E Form f val b)
  -> E Form f val b
local_auto = local auto auto

u8 :: Haskell.Word8 -> E Form f val (Obj (Constant UInt8))
u8 w = formal auto $ Integer_Literal_UInt8_f w

u16 :: Haskell.Word16 -> E Form f val (Obj (Constant UInt16))
u16 w = formal auto $ Integer_Literal_UInt16_f w

u32 :: Haskell.Word32 -> E Form f val (Obj (Constant UInt32))
u32 w = formal auto $ Integer_Literal_UInt32_f w

u64 :: Haskell.Word64 -> E Form f val (Obj (Constant UInt64))
u64 w = formal auto $ Integer_Literal_UInt64_f w

i8 :: Haskell.Int8 -> E Form f val (Obj (Constant Int8))
i8 i = formal auto $ Integer_Literal_Int8_f i

i16 :: Haskell.Int16 -> E Form f val (Obj (Constant Int16))
i16 i = formal auto $ Integer_Literal_Int16_f i

i32 :: Haskell.Int32 -> E Form f val (Obj (Constant Int32))
i32 i = formal auto $ Integer_Literal_Int32_f i

i64 :: Haskell.Int64 -> E Form f val (Obj (Constant Int64))
i64 i = formal auto $ Integer_Literal_Int64_f i

add :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  )
add = formal auto Integer_Add_f

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
subtract = formal auto Integer_Subtract_f

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
multiply = formal auto Integer_Multiply_f

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
divide = formal auto Integer_Divide_f

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
modulo = formal auto Integer_Modulo_f

mod :: (Known sign, Known width)
    => E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
    -> E Form f val (Obj (Constant ('Integer_t sign width)))
a `mod` b = modulo <@> a <@> b

negate :: Known width => E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t width))
  :-> Obj (Constant ('Integer_t 'Signed_t width))
  )
negate = formal auto Integer_Negate_f

neg :: (Known width)
    => E Form f val (Obj (Constant ('Integer_t 'Signed_t width)))
    -> E Form f val (Obj (Constant ('Integer_t 'Signed_t width)))
neg a = negate <@> a

abs :: Known width => E Form f val
  (   Obj (Constant ('Integer_t 'Signed_t   width))
  :-> Obj (Constant ('Integer_t 'Unsigned_t width))
  )
abs = formal auto Integer_Abs_f

compare_auto :: (Known sign, Known width, Known r) => E Form f val
  (   Obj (Constant r) -- lt
  :-> Obj (Constant r) -- eq
  :-> Obj (Constant r) -- gt
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant r)
  )
compare_auto = formal auto Integer_Compare_f

cmp :: (Known sign, Known width) => E Form f val
  (   Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant ('Integer_t sign width))
  :-> Obj (Constant Cmp)
  )
cmp = formal auto Integer_Compare_f <@> lt <@> eq <@> gt

and :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
and = formal auto Bytes_And_f

or :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
or = formal auto Bytes_Or_f

xor :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
xor = formal auto Bytes_Xor_f

complement :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t width))
  )
complement = formal auto Bytes_Complement_f

shiftl :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftl = formal auto Bytes_Shiftl_f

shiftr :: Known width => E Form f val
  (   Obj (Constant ('Bytes_t width))
  :-> Obj (Constant ('Bytes_t 'W_One_t))
  :-> Obj (Constant ('Bytes_t width))
  )
shiftr = formal auto Bytes_Shiftr_f

cast :: (Known a, Known b) => Cast a b -> E Form f val
  (Obj (Constant a) :-> Obj (Constant b))
cast c = formal auto (Cast_f c)

-- | Construct a product.
bundle :: (Known ('Product_t fields), Known r) => Fields r fields -> E Form f val
  (r :-> Obj (Constant ('Product_t fields)))
bundle fields = formal auto (Product_Intro_f fields)

-- | Construct a sum.
choose :: (Known ('Sum_t variants), Known r) => Variant r variants -> E Form f val
  (r :-> Obj (Constant ('Sum_t variants)))
choose variant = formal auto (Sum_Intro_f variant)

-- | Eliminate a product
project :: (Known ('Product_t fields), Known field) => Selector fields field -> E Form f val
  (Obj (Constant ('Product_t fields)) :-> Obj (Constant field))
project selector = formal auto (Product_Elim_f selector)

match :: (Known ('Sum_t variants), Known r) => Cases variants r -> E Form f val
  (Obj (Constant ('Sum_t variants)) :-> r)
match cases = formal auto (Sum_Elim_f cases)

-- | The formal product intro construction gives a function from a meta-language
-- product--in this case the terminal object--to the object-language thing, so
-- here we apply it to `specific terminal`
unit :: E Form f val (Obj (Constant Unit))
unit = formal auto (Product_Intro_f F_All) <@> terminal

-- | The formal sum elim constructor has a base case that works for any type.
-- Since the empty sum requires only this base case, we don't even have to
-- construct anything of this type, so we get the typical `absurd` type.
absurd :: Known r => E Form f val (Obj (Constant Void) :-> Obj (Constant r))
absurd = fun $ \impossible -> formal auto (Sum_Elim_f C_Any) <@> impossible <@> terminal

-- NB: an empty product cannot be eliminated, and an empty sum cannot be
-- introduced. The meta-language enforces this: there are no Selector or
-- Variant types for an empty field/variant list.

-- | The formal sum intro construction, like that of the product, gives a
-- meta-language function. The Variant value (V_That V_This) indicates which
-- variant to construct, and therefore what type is needed (in this case it's
-- the object-language unit, so 'unit' is used).
true :: E Form f val (Obj (Constant Bool))
true = formal auto (Sum_Intro_f (V_That V_This)) <@> unit

false :: E Form f val (Obj (Constant Bool))
false = formal auto (Sum_Intro_f V_This) <@> unit

if_then_else_ :: Known r => E Form f val
  (   Obj (Constant Bool)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  :-> Obj (Constant r)
  )
if_then_else_ = fun $ \b -> fun $ \ifTrue -> fun $ \ifFalse ->
  formal auto (Sum_Elim_f (C_Or (C_Or C_Any))) <@> b <@> ((const <@> ifFalse) &> (const <@> ifTrue) &> terminal)

if_then_else
  :: Known r
  => E Form f val (Obj (Constant Bool))
  -> E Form f val (Obj (Constant r)) -- True case
  -> E Form f val (Obj (Constant r)) -- False case
  -> E Form f val (Obj (Constant r))
if_then_else b ifTrue ifFalse = formal auto (Sum_Elim_f (C_Or (C_Or C_Any)))
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

lt :: E Form f val (Obj (Constant Cmp))
lt = choose V_This <@> unit

eq :: E Form f val (Obj (Constant Cmp))
eq = choose (V_That V_This) <@> unit

gt :: E Form f val (Obj (Constant Cmp))
gt = choose (V_That (V_That V_This)) <@> unit

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
(<=) a b = local_auto (cmp <@> a <@> b) $ \x ->
  lor <@> (is_lt <@> x) <@> (is_eq <@> x)

(>=) :: (Known sign, Known width)
     => E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant ('Integer_t sign width)))
     -> E Form f val (Obj (Constant Bool))
(>=) a b = local_auto (cmp <@> a <@> b) $ \x ->
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

map :: forall f val n s t q r .
       Meta.TypeRep TypeRep s
    -> Meta.TypeRep TypeRep t
    -> Meta.TypeRep TypeRep q
    -> Meta.TypeRep TypeRep r
    -> NatRep n
    -> MapImage n s q
    -> MapImage n t r
    -> E Form f val ((s :-> t) :-> (q :-> r))
map srep trep qrep rrep nrep limage rimage = formal rep (Stream_Map_f nrep limage rimage)
  where
  rep = (srep .-> trep) .-> (qrep .-> rrep)

-- | 'map' but the 'MapImage's are derived. Requires more type annotation by
-- the user.
map_auto :: forall f val n s t .
       (Known s, Known t, KnownMapPreImage n s, KnownMapPreImage n t)
    => NatRep n
    -> E Form f val ((s :-> t) :-> (C n s :-> C n t))
map_auto nrep = map auto auto auto auto nrep limage rimage
  where
  limage = knownMapPreImage pn (Proxy :: Proxy s)
  rimage = knownMapPreImage pn (Proxy :: Proxy t)
  pn :: Proxy n
  pn = Proxy

-- | Constant, akin to applicative pure for zip lists, is expressed by
-- the notion of Stream_Map_f, where the function being mapped is from the
-- terminal object, i.e. something like
--
--   () -> a
--
-- The image of this in the functor would be
--
--   () -> Varying n a
--
-- To make things more pleasant to work with, this function gets rid of the
-- terminal object and arrow.
constant :: forall f val n s t . NatRep n -> Point.TypeRep s -> E Form f val
  (Obj (Constant s) :-> Obj (Varying n s))
constant nrep rep = fun $ \t ->
  map srep trep qrep rrep nrep MapTerminal MapObject <@> (const <@> t) <@> terminal
  where
  srep = Meta.terminal_t
  qrep = Meta.terminal_t
  trep = Meta.object_t (constant_t rep)
  rrep = Meta.object_t (varying_t nrep rep)

constant_auto :: forall f val n s t . (Known s) => NatRep n -> E Form f val
  (Obj (Constant s) :-> Obj (Varying n s))
constant_auto nrep = constant nrep auto

-- Is lifting properly defined? It's good for many examples and use cases, but
-- what about something like if_then_else? Maybe the error is that
-- if_then_else should have `Obj (Constant r)` rather than `r`? Do we gain
-- anything by having `r` be possibly meta? I don't think so. In fact I think
-- it's just totally wrong!
--
-- Fixed. But still, if_then_else is an easy one. What about lifting a
-- maybe eliminator?

just :: Known a
     => E Form f val (Obj (Constant a) :-> Obj (Constant (Maybe a)))
just = formal auto (Sum_Intro_f (V_That V_This))

nothing :: Known s => E Form f val (Obj (Constant (Maybe s)))
nothing = formal auto (Sum_Intro_f V_This) <@> unit

maybe :: (Known s, Known r) => E Form f val
  (   Obj (Constant r)
  :-> (Obj (Constant s) :-> Obj (Constant r))
  :-> Obj (Constant (Maybe s))
  :-> Obj (Constant r)
  )
maybe = fun $ \ifNothing -> fun $ \ifJust -> fun $ \m ->
  formal auto (Sum_Elim_f (C_Or (C_Or C_Any)))
    <@> m <@> ((fun $ \_ -> ifNothing) &> ifJust &> terminal)

isJust :: Known a => E Form f val (Obj (Constant (Maybe a)) :-> Obj (Constant Bool))
isJust = fun $ \m -> maybe <@> false <@> (const <@> true) <@> m

isNothing :: Known a => E Form f val (Obj (Constant (Maybe a)) :-> Obj (Constant Bool))
isNothing = fun $ \m -> maybe <@> true <@> (const <@> false) <@> m

-- | Constructs a pair. The formal 'product_intro_f' gives a function from a
-- meta-language product with an explicit terminal in the rightmost position,
-- but we change it to be a curried from without the terminal.
pair :: Point.TypeRep a -> Point.TypeRep b -> E Form f val
  (Obj (Constant a) :-> Obj (Constant b) :-> Obj (Constant (Pair a b)))
pair arep brep = fun $ \a -> fun $ \b ->
  formal rep (Product_Intro_f (F_And (F_And F_All))) <@> (a &> b &> terminal)
  where
  rep = (Meta.object_t (constant_t arep) .* Meta.object_t (constant_t brep) .* Meta.terminal_t) .-> Meta.object_t (constant_t (pair_t arep brep))

pair_auto :: (Known a, Known b) => E Form f val
  (Obj (Constant a) :-> Obj (Constant b) :-> Obj (Constant (Pair a b)))
pair_auto = pair auto auto

fst :: Point.TypeRep a -> Point.TypeRep b -> E Form f val
  (Obj (Constant (Pair a b)) :-> Obj (Constant a))
fst arep brep = fun $ \p -> formal rep (Product_Elim_f S_Here) <@> p
  where
  rep =      Meta.object_t (constant_t (Point.pair_t arep brep))
        .->  Meta.object_t (constant_t arep)

snd :: Point.TypeRep a -> Point.TypeRep b -> E Form f val
  (Obj (Constant (Pair a b)) :-> Obj (Constant b))
snd arep brep = fun $ \p -> formal rep (Product_Elim_f (S_There S_Here)) <@> p
  where
  rep =      Meta.object_t (constant_t (Point.pair_t arep brep))
        .->  Meta.object_t (constant_t brep)

fst_auto :: (Known a, Known b) => E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant a))
fst_auto = fst auto auto

snd_auto :: (Known a, Known b) => E Form f val (Obj (Constant (Pair a b)) :-> Obj (Constant b))
snd_auto = snd auto auto

drop :: NatRep n -> Point.TypeRep t -> E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
drop nrep trep = formal rep Stream_Drop_f
  where
  rep = (Meta.object_t (varying_t (S_Rep nrep) trep) .-> Meta.object_t (varying_t nrep trep))

shift :: NatRep n -> Point.TypeRep t -> E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
shift nrep trep = formal rep Stream_Shift_f
  where
  rep = (Meta.object_t (varying_t (S_Rep nrep) trep) .-> Meta.object_t (varying_t nrep trep))

drop_auto :: (Known n, Known t) => E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
drop_auto = drop auto auto

shift_auto :: (Known n, Known t) => E Form f val
  (Obj (Varying ('S n) t) :-> Obj (Varying n t))
shift_auto = shift auto auto

-- |
-- = Mutually-recursive memory streams.

-- | The most general, but comparatively verbose, way to write a
-- mutually-recursive memory stream.
--
-- 'knot_auto' can be used when GHC has Known for all of the necessary types.
knot :: Meta.TypeRep TypeRep s
     -> Meta.TypeRep TypeRep t
     -> Meta.TypeRep TypeRep i
     -> Meta.TypeRep TypeRep r
     -> Knot s t i r
     -> E Form f val ((s :-> t) :-> (i :-> Obj (Program r)))
knot srep trep irep rrep sig = formal rep (Stream_Knot_f sig)
  where
  rep = (srep .-> trep) .-> (irep .-> Meta.object_t (program_t rrep))

-- | Like 'knot' but GHC knows all of the types involved.
knot_auto
  :: (Known s, Known t, Known i, Known r)
  => Knot s t i r
  -> E Form f val ((s :-> t) :-> (i :-> Obj (Program r)))
knot_auto = knot auto auto auto auto

-- |
-- = Functor/Applicative/Monad for Program

prog_map
  :: Meta.TypeRep TypeRep s
  -> Meta.TypeRep TypeRep t
  -> E Form f val ((s :-> t) :-> Obj (Program s) :-> Obj (Program t))
prog_map srep trep = formal rep Program_Map_f
  where
  rep = (srep .-> trep) .-> (Meta.object_t (program_t srep) .-> Meta.object_t (program_t trep))

prog_pure
  :: Meta.TypeRep TypeRep t
  -> E Form f val (t :-> Obj (Program t))
prog_pure trep = formal rep Program_Pure_f
  where
  rep = trep .-> Meta.object_t (program_t trep)

prog_ap
  :: Meta.TypeRep TypeRep s
  -> Meta.TypeRep TypeRep t
  -> E Form f val (Obj (Program (s :-> t)) :-> Obj (Program s) :-> Obj (Program t))
prog_ap srep trep = formal rep Program_Ap_f
  where
  rep = Meta.object_t (program_t (srep .-> trep)) .-> Meta.object_t (program_t srep) .-> Meta.object_t (program_t trep)

prog_join
  :: Meta.TypeRep TypeRep t
  -> E Form f val (Obj (Program (Obj (Program t))) :-> Obj (Program t))
prog_join trep = formal rep Program_Join_f
  where
  rep = Meta.object_t (program_t (Meta.object_t (program_t trep))) .-> Meta.object_t (program_t trep)

prog_bind
  :: Meta.TypeRep TypeRep s
  -> Meta.TypeRep TypeRep t
  -> E Form f val (Obj (Program s))
  -> E Form f val (s :-> Obj (Program t))
  -> E Form f val (Obj (Program t))
prog_bind srep trep p k = prog_join trep <@> (prog_map srep trep' <@> k <@> p)
  where
  trep' = Meta.object_t (program_t trep)

-- | 'prog_bind' but with a type that makes it easier to use infix.
(>>=)
  :: (Known s, Known t)
  => E Form f val (Obj (Program s))
  -> (E Form f val s -> E Form f val (Obj (Program t)))
  -> E Form f val (Obj (Program t))
(>>=) it k = prog_bind auto auto it (fun k)
