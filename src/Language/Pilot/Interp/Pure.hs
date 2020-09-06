{-|
Module      : Language.Pilot.Interp.Pure
Description : In-Haskell representation and interpreter.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Pilot.Interp.Pure
  ( Value (..)
  , Identity (..)
  , showValue
  , interpPure
  , constant
  , varying
  , streamToVarying
  , varyingToStream
  , pointToConstant
  , constantToPoint

  , PrefixList.cycle
  , PrefixList.repeat
  , PrefixList.fromInit
  ) where

import Prelude hiding (Integer)
import Data.Functor.Identity (Identity (..))

import Language.Pilot.Types
import Language.Pilot.Meta (Obj, type (:->), type (:*))
import Language.Pilot.Object as Object hiding (Point (..), pattern Varying,
  pattern Constant, pattern Program, constant)
import Language.Pilot.Repr

import Language.Pilot.Interp.Pure.Point as Point
import Language.Pilot.Interp.Pure.PrefixList as PrefixList

instance Interprets Object.Form Identity Value where
  interp = interpPure

data Value (t :: Object.Type) where
  Constant :: Point t -> Value (Constant t)
  Varying  :: PrefixList n Point t -> Value (Varying n t)
  Program  :: Repr Identity Value t -> Value (Program t)

showValue :: Prelude.Maybe Int -> Value t -> String
showValue n it = case it of
  Constant pt  -> Point.prettyPrint pt
  Varying  lst -> PrefixList.prettyPrint n Point.prettyPrint lst
  Program  rep -> "<program>"

constantToPoint :: Repr Identity Value (Obj (Constant t)) -> Point t
constantToPoint = fromConstant . fromObject . runIdentity . getRepr

pointToConstant :: Point t -> Repr Identity Value (Obj (Constant t))
pointToConstant = Repr . Identity . Object . Constant

varyingToStream :: Repr Identity Value (Obj (Varying n t)) -> PrefixList n Point t
varyingToStream = fromVarying . fromObject . runIdentity . getRepr

streamToVarying :: PrefixList n Point t -> Repr Identity Value (Obj (Varying n t))
streamToVarying = Repr . Identity . Object . Varying

applyVarying :: (PrefixList n Point s -> PrefixList m Point t)
             -> (Value (Varying n s) -> Value (Varying m t))
applyVarying f = \(Varying lst) -> Varying (f lst)

constant :: Point t -> Value (Constant t)
constant = Constant

varying :: PrefixList n Point t -> Value (Varying n t)
varying = Varying

program :: Repr Identity Value t -> Value (Program t)
program = Program

fromVarying :: Value (Varying n t) -> PrefixList n Point t
fromVarying (Varying lst) = lst

fromVaryingRep :: PrefixList n Point t -> Value (Varying n t)
fromVaryingRep = Varying

toVaryingRep :: Value (Varying n t) -> PrefixList n Point t
toVaryingRep (Varying lst) = lst

fromConstant :: Value (Constant t) -> Point t
fromConstant (Constant p) = p

fromConstantRep :: Point t -> Value (Constant t)
fromConstantRep = Constant


liftPoint :: (Point a -> Point b)
          -> Val f Value (Obj (Constant a))
          -> Val f Value (Obj (Constant b))
liftPoint f (Object (Constant a)) = Object (Constant (f a))

liftPoint2 :: (Point a -> Point b -> Point c)
           -> Val f Value (Obj (Constant a))
           -> Val f Value (Obj (Constant b))
           -> Val f Value (Obj (Constant c))
liftPoint2 f (Object (Constant a)) (Object (Constant b)) = Object (Constant (f a b))

interpPure :: Interpret Object.Form Identity Value
interpPure trep form = case form of

  Integer_Literal_UInt8_f  w8  -> object (Constant (Integer (Point.UInt8 w8)))
  Integer_Literal_UInt16_f w16 -> object (Constant (Integer (Point.UInt16 w16)))
  Integer_Literal_UInt32_f w32 -> object (Constant (Integer (Point.UInt32 w32)))
  Integer_Literal_UInt64_f w64 -> object (Constant (Integer (Point.UInt64 w64)))
  Integer_Literal_Int8_f  i8  -> object (Constant (Integer (Point.Int8 i8)))
  Integer_Literal_Int16_f i16 -> object (Constant (Integer (Point.Int16 i16)))
  Integer_Literal_Int32_f i32 -> object (Constant (Integer (Point.Int32 i32)))
  Integer_Literal_Int64_f i64 -> object (Constant (Integer (Point.Int64 i64)))
  Bytes_Literal_8_f  w8  -> object (Constant (Bytes (Point.Word8 w8)))
  Bytes_Literal_16_f w16 -> object (Constant (Bytes (Point.Word16 w16)))
  Bytes_Literal_32_f w32 -> object (Constant (Bytes (Point.Word32 w32)))
  Bytes_Literal_64_f w64 -> object (Constant (Bytes (Point.Word64 w64)))

  -- Here we have x and y, which are each of type
  --   Repr f Value (Obj (Constant (Integer_t s w)))
  -- We do not wish to impose any particular order of evaluation on the
  -- arguments, so we'll want to use the applicative instance on f to apply
  -- `Point.add`, which itself must be "lifted" through the Value type.
  Integer_Add_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.add <$> getRepr x <*> getRepr y)
  Integer_Subtract_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.subtract <$> getRepr x <*> getRepr y)
  Integer_Multiply_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.multiply <$> getRepr x <*> getRepr y)
  Integer_Divide_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.divide <$> getRepr x <*> getRepr y)
  Integer_Modulo_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.modulo <$> getRepr x <*> getRepr y)
  Integer_Negate_f -> fun $ \x ->
    repr (liftPoint Point.negate <$> getRepr x)
  Integer_Abs_f -> fun $ \x ->
    repr (liftPoint Point.abs <$> getRepr x)
  Integer_Compare_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.compare <$> getRepr x <*> getRepr y)

  Bytes_And_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.and <$> getRepr x <*> getRepr y)
  Bytes_Or_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.or <$> getRepr x <*> getRepr y)
  Bytes_Xor_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.xor <$> getRepr x <*> getRepr y)
  Bytes_Complement_f -> fun $ \x ->
    repr (liftPoint Point.complement <$> getRepr x)
  Bytes_Shiftl_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.shiftl <$> getRepr x <*> getRepr y)
  Bytes_Shiftr_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.shiftr <$> getRepr x <*> getRepr y)

  Cast_f c -> interp_cast c

  -- For let bindings we do whatever a monadic bind is in f, effectively
  -- "sharing the context" of the x representation by re-introducing it as
  -- pure (the `value` function) in the continuation.
  Let_f -> fun $ \x -> fun $ \f -> repr $ do
    xval <- getRepr x
    getRepr (f <@> value xval)

  Product_Intro_f fields -> interp_product_intro fields
  Product_Elim_f selector -> interp_product_elim selector

  Sum_Intro_f variant -> interp_sum_intro variant
  Sum_Elim_f cases -> interp_sum_elim cases

  Stream_Drop_f  -> fun $ \v -> objectf $
    fmap (applyVarying PrefixList.drop . fromObject) (getRepr v)
  Stream_Shift_f -> fun $ \v -> objectf $
    fmap (applyVarying PrefixList.shift . fromObject) (getRepr v)

  Stream_Map_f nrep limage rimage -> interp_map nrep limage rimage

  Program_Map_f -> interp_prog_map
  Program_Pure_f -> interp_prog_pure
  Program_Ap_f -> interp_prog_ap
  Program_Join_f -> interp_prog_join

  Stream_Knot_f kn -> interp_knot kn

interp_prog_map :: Repr Identity Value ((s :-> t) :-> Obj (Program s) :-> Obj (Program t))
interp_prog_map = fun $ \f -> fun $ \p -> case fromObject (runIdentity (getRepr p)) of
  Program repr -> object $ program $ f <@> repr

interp_prog_pure :: Repr Identity Value (t :-> Obj (Program t))
interp_prog_pure = fun $ \t -> object $ program t

interp_prog_ap :: Repr Identity Value (Obj (Program (s :-> t)) :-> Obj (Program s) :-> Obj (Program t))
interp_prog_ap = fun $ \mf -> fun $ \mx -> case fromObject (runIdentity (getRepr mf)) of
  Program f -> case fromObject (runIdentity (getRepr mx)) of
    Program x -> object $ program $ f <@> x

interp_prog_join :: Repr Identity Value (Obj (Program (Obj (Program t))) :-> Obj (Program t))
interp_prog_join = fun $ \mt -> case fromObject (runIdentity (getRepr mt)) of
  Program t -> t

interp_cast :: Cast a b -> Repr Identity Value (Obj (Constant a) :-> Obj (Constant b))
interp_cast c = fun $ \a -> object $ constant $ case (c, fromConstant (fromObject (runIdentity (getRepr a)))) of

  (UpCastInteger TwoWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.UInt16 (fromIntegral w))
  (UpCastInteger TwoWiderOne, Point.Integer (Point.Int8 w)) -> Point.Integer (Point.Int16 (fromIntegral w))
  (UpCastInteger FourWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.UInt32 (fromIntegral w))
  (UpCastInteger FourWiderTwo, Point.Integer (Point.UInt16 w)) -> Point.Integer (Point.UInt32 (fromIntegral w))
  (UpCastInteger FourWiderOne, Point.Integer (Point.Int8 w)) -> Point.Integer (Point.Int32 (fromIntegral w))
  (UpCastInteger FourWiderTwo, Point.Integer (Point.Int16 w)) -> Point.Integer (Point.Int32 (fromIntegral w))
  (UpCastInteger EightWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.UInt64 (fromIntegral w))
  (UpCastInteger EightWiderTwo, Point.Integer (Point.UInt16 w)) -> Point.Integer (Point.UInt64 (fromIntegral w))
  (UpCastInteger EightWiderFour, Point.Integer (Point.UInt32 w)) -> Point.Integer (Point.UInt64 (fromIntegral w))
  (UpCastInteger EightWiderOne, Point.Integer (Point.Int8 w)) -> Point.Integer (Point.Int64 (fromIntegral w))
  (UpCastInteger EightWiderTwo, Point.Integer (Point.Int16 w)) -> Point.Integer (Point.Int64 (fromIntegral w))
  (UpCastInteger EightWiderFour, Point.Integer (Point.Int32 w)) -> Point.Integer (Point.Int64 (fromIntegral w))

  (UpCastBytes TwoWiderOne, Point.Bytes (Point.Word8 w)) -> Point.Bytes (Point.Word16 (fromIntegral w))
  (UpCastBytes FourWiderOne, Point.Bytes (Point.Word8 w)) -> Point.Bytes (Point.Word32 (fromIntegral w))
  (UpCastBytes FourWiderTwo, Point.Bytes (Point.Word16 w)) -> Point.Bytes (Point.Word32 (fromIntegral w))
  (UpCastBytes EightWiderOne, Point.Bytes (Point.Word8 w)) -> Point.Bytes (Point.Word64 (fromIntegral w))
  (UpCastBytes EightWiderTwo, Point.Bytes (Point.Word16 w)) -> Point.Bytes (Point.Word64 (fromIntegral w))
  (UpCastBytes EightWiderFour, Point.Bytes (Point.Word32 w)) -> Point.Bytes (Point.Word64 (fromIntegral w))

  (CastToSigned, Point.Integer (Point.UInt8 w)) -> fromConstant . fromObject . runIdentity . getRepr $
    if w Prelude.<= (2^7 Prelude.- 1)
    then just (object (constant (Point.Integer (Point.Int8 (fromIntegral w)))))
    else nothing
  (CastToSigned, Point.Integer (Point.UInt16 w)) -> fromConstant . fromObject . runIdentity . getRepr $
    if w Prelude.<= (2^15 Prelude.- 1)
    then just (object (constant (Point.Integer (Point.Int16 (fromIntegral w)))))
    else nothing
  (CastToSigned, Point.Integer (Point.UInt32 w)) -> fromConstant . fromObject . runIdentity . getRepr $
    if w Prelude.<= (2^31 Prelude.- 1)
    then just (object (constant (Point.Integer (Point.Int32 (fromIntegral w)))))
    else nothing
  (CastToSigned, Point.Integer (Point.UInt64 w)) -> fromConstant . fromObject . runIdentity . getRepr $
    if w Prelude.<= (2^63 Prelude.- 1)
    then just (object (constant (Point.Integer (Point.Int64 (fromIntegral w)))))
    else nothing

  (UpCastToSigned TwoWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.Int16 (fromIntegral w))
  (UpCastToSigned FourWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.Int32 (fromIntegral w))
  (UpCastToSigned FourWiderTwo, Point.Integer (Point.UInt16 w)) -> Point.Integer (Point.Int32 (fromIntegral w))
  (UpCastToSigned EightWiderOne, Point.Integer (Point.UInt8 w)) -> Point.Integer (Point.Int64 (fromIntegral w))
  (UpCastToSigned EightWiderTwo, Point.Integer (Point.UInt16 w)) -> Point.Integer (Point.Int64 (fromIntegral w))
  (UpCastToSigned EightWiderFour, Point.Integer (Point.UInt32 w)) -> Point.Integer (Point.Int64 (fromIntegral w))

-- It seems that for product intro we really do need to use the monad of f,
-- for we have to evaluate the meta-language product in order to get the
-- next fields.
--
-- In practice, this is usually fine: the expression will almost certainly use
-- <& or &> which do not add any effects in f (pure). But it's still kinda
-- weird.
--
interp_product_intro
  :: forall f r fields .
     ( Monad f )
  => Fields r fields
  -> Repr f Value (r :-> Obj (Constant (Product fields)))
interp_product_intro fields = fun $ \r -> objectf $ 
  fmap bundle (evaluate fields r)

  where

  evaluate
    :: forall r fields .
       Fields r fields
    -> Repr f Value r
    -> f (Point.All Point.Point fields)
  evaluate F_All           _ = pure Point.All
  -- It's here where we need Monad f.
  evaluate (F_And fields') r = do
    p <- getRepr r
    case fromProduct p of
      (xr, rs) -> do
        x <- getRepr xr
        xs <- evaluate fields' rs
        pure (Point.And (fromConstant (fromObject x)) xs)

  bundle
    :: forall r fields .
       Point.All Point.Point fields
    -> Value (Constant (Product fields))
  bundle = fromConstantRep . Point.Product_r

interp_sum_intro
  :: forall f r variants .
     ( Applicative f )
  => Variant r variants
  -> Repr f Value (r :-> Obj (Constant (Sum variants)))
interp_sum_intro variant = fun $ \v -> objectf $
  fmap (fromConstantRep . Point.Sum_r) (inject variant v)

  where

  inject
    :: forall r variants .
       Variant r variants
    -> Repr f Value r
    -> f (Point.Some Point.Point variants)
  inject V_This        v = fmap (Point.Some . fromConstant . fromObject) (getRepr v)
  inject (V_That that) v = fmap Point.Or (inject that v)

-- |
--
-- TODO is this lazy enough? We ought to be able to come up with the entire
-- function type without actually evaluating the product itself, instead looking
-- only at the `Selector`.
interp_product_elim
  :: forall f fields field .
     ( Monad f )
  => Selector fields field
  -> Repr f Value (Obj (Constant (Product fields)) :-> Obj (Constant field))
interp_product_elim selector = fun $ \p -> valuef $ do
  -- Get the representation of the product...
  fields <- fmap (fromConstant . fromObject) (getRepr p)
  -- Then use the selector to figure out which type of projection function
  -- to take, and apply it to the relevant field.
  getRepr (select selector fields)

  where

  select
    :: forall fields field .
       Selector fields field
    -> Point (Product fields)
    -> Repr f Value (Obj (Constant field))
  select (S_There s) (Product_r (And _ ps)) = select s (Product_r ps)
  select S_Here      (Product_r (And it _)) = object (fromConstantRep it)

interp_sum_elim
  :: forall f r variants .
     ( Monad f )
  => Cases variants r
  -> Repr f Value (Obj (Constant (Sum variants)) :-> r)
interp_sum_elim cases = fun $ \scrutinee -> valuef $ do
  -- Evaluate the scrutinee...
  v <- fmap (fromConstant . fromObject) (getRepr scrutinee)
  -- Use the Cases to match on the scrutinee.
  getRepr (match cases v)

  where

  match
    :: forall r variants .
       Cases variants r
    -> Point (Sum variants)
    -> Repr f Value r
  -- Empty case match is ruled out because empty sums cannot be constructed.
  match C_Any     (Point.Sum_r wut) = case wut of {}
  -- For non-empty cases, we always take one argument: a product of eliminators,
  -- one for each variant.
  match (C_Or cs) it                = fun $ \eliminators ->
    eliminate cs it eliminators

  -- Deconstruct a sum representation, using a Cases value to constrain the
  -- type of the eliminators product.
  eliminate
    :: forall q r variant variants .
       Cases variants (q :-> r)
    -> Point (Sum (variant ': variants))
    -> Repr f Value ((Obj (Constant variant) :-> r) :* q)
    -> Repr f Value r
  eliminate _ (Point.Sum_r (Point.Some it)) elims =
    app (Language.Pilot.Repr.fst elims) (object (fromConstantRep it))
  eliminate (C_Or cs) (Point.Sum_r (Point.Or sum)) elims =
    eliminate cs (Point.Sum_r sum) (Language.Pilot.Repr.snd elims)
  eliminate C_Any (Point.Sum_r (Point.Or sum)) _ = case sum of {}

-- | Interpret the functor from constants to varyings, for a given prefix size,
-- by using the zip-list-like properties of the PrefixList: zip the product of
-- lists together, map the function on constants over it, and then unzip it.
interp_map
  :: forall n s t q r .
     NatRep n
  -> MapImage n s q
  -> MapImage n t r
  -> Repr Identity Value ((s :-> t) :-> (q :-> r))
interp_map nrep limage rimage = fun $ \preimage -> fun $ \q ->
    unroll rimage
  . apply (runIdentity (getRepr preimage))
  . roll nrep limage
  $ runIdentity (getRepr q)

  where

  -- | use the correspondence between the inputs of the arrows to zip up all
  -- of the prefix lists into one which contains the type of the preimage
  -- arrow's input
  roll :: forall n s q .
          NatRep n
       -> MapImage n s q
       -> Val Identity Value q
       -> PrefixList n (Repr Identity Value) s
  -- Here the input value is the terminal object; we don't have a prefix list,
  -- so we must make a new one up, but that's an obvious and natural choice.
  roll nrep MapTerminal      _ = PrefixList.repeat nrep (value Terminal)
  -- The input prefix list has an object; all we need to do is pull it out
  -- front.
  roll _    MapObject        v = PrefixList.map (object . fromConstantRep) (fromVarying (fromObject v))
  -- For products, we zip together the two rolled prefix lists.
  roll nrep (MapProduct l r) v =
    let (lv, rv) = fromProduct v
        lroll = roll nrep l (runIdentity (getRepr lv))
        rroll = roll nrep r (runIdentity (getRepr rv))
    in  PrefixList.meld (\x y -> x &> y) lroll rroll

  apply :: Val Identity Value (s :-> t)
        -> PrefixList n (Repr Identity Value) s
        -> PrefixList n (Repr Identity Value) t
  apply f lst = PrefixList.map (fromArrow f) lst

  unroll :: forall n t r .
            MapImage n t r
         -> PrefixList n (Repr Identity Value) t
         -> Repr Identity Value r
  -- There is by definition only one function to the terminal object
  unroll MapTerminal      _   = terminal
  unroll MapObject        lst = object $
    fromVaryingRep (PrefixList.map (fromConstant . fromObject . runIdentity . getRepr) lst)
  -- Whereas we zip the lists together in roll, in unroll we unzip them.
  unroll (MapProduct l r) lst =
    let (llst, rlst) = PrefixList.unmeld (fromProduct . runIdentity . getRepr) lst
        lunroll = unroll l llst
        runroll = unroll r rlst
    in  lunroll &> runroll

interp_knot
  :: forall s t i r .
     Knot s t i r
  -> Repr Identity Value ((s :-> t) :-> (i :-> Obj (Program r)))
interp_knot kn = fun $ \fknot -> fun $ \inits ->
  -- We have
  --
  --   fknot :: s :-> t
  --   inits :: i
  --
  -- where s t i are related by the GADT value kn.
  --
  -- Suppose we match on the first and it's a Tie. In this case, we can
  -- get
  --
  --   s ~ Obj (Varying n a) :* s1
  --   t ~ Obj (Varying Z a) :* t1
  --   i ~ Vector (S n) (Obj (Constant a)) :* i1
  --   r ~ Obj (Varying (S n) a :* q1
  --
  -- and we also have a NatRep n, so we can get some work done. We would match
  -- on inits, which we know to be a product containing a vector, and use that
  -- vector to construct
  -- - The output prefix list using `fromInitVec  . vecFromVector`
  -- - The input  prefix list using `fromInitVec_ . vecFromVector`
  -- But to do this, we need the output in t... 
  --
  -- Anyway, it's here where we use the meta-language laziness to tie the knot.
  -- The Knot value is of course forced, to reveal information about the
  -- type parameters. That GADT it set up in such a way that this knot should
  -- always be sufficiently lazy, for the PrefixLists in the input `s` are
  -- each given one fewer prefix count, and so the EDSL expression cannot
  -- reference anything beyond what is determined by the init vectors.
  let initvals = runIdentity (getRepr inits)
      prefixes = knot_prefixes kn initvals suffixes
      streams  = knot_streams  kn initvals suffixes
      suffixes = runIdentity . getRepr . app fknot . valuef . Identity $ prefixes
  in  object . program . valuef . Identity $ streams

  where

  -- Construct a Vec, eliminating the Vector type family.
  -- The proxy is here because Vector is a non-injective type family.
  vecFromVector
    :: forall n t .
       Proxy t
    -> NatRep n
    -> Val Identity Value (Vector n (Obj (Constant t)))
    -> Vec n (Value (Constant t))
  -- The pattern match is done in 3 cases so that GHC can figure out what the
  -- type family Vector reduces to.
  vecFromVector _  Z_Rep                  _                 = VNil
  vecFromVector _  (S_Rep Z_Rep)          (Object t)        = VCons t VNil
  vecFromVector pt (S_Rep nrep@(S_Rep _)) (Product (t, ts)) =
    let Object v = runIdentity (getRepr t)
        vs       = vecFromVector pt nrep (runIdentity (getRepr ts))
    in  VCons v vs

  -- This whole thing could probably be shortened, but it's not worth the time
  -- at the moment.

  -- Compute the prefixes of the knot: the inputs to the knot-tying function.
  knot_prefixes :: forall s t i r .
       Knot s t i r
    -> Val Identity Value i
    -> Val Identity Value t
    -> Val Identity Value s
  knot_prefixes kn i t = case kn of
    Tied nrep _     -> prefix_tied nrep     i t
    Tie  nrep _ kn' -> prefix_tie  nrep kn' i t

  prefix_tied
    :: forall n a .
       NatRep ('S n)
    -> Val Identity Value (Vector ('S n) (Obj (Constant a)))
    -> Val Identity Value (Obj (Varying 'Z a))
    -> Val Identity Value (Obj (Varying n a))
  prefix_tied nrep i r =
    let vec  = vecFromVector (Proxy :: Proxy a) nrep i
        suf  = PrefixList.map fromConstantRep (fromVarying (fromObject r))
        full = PrefixList.fromInitVec_ vec suf
    in  Object (Varying (PrefixList.map fromConstant full))

  prefix_tie
    :: forall n a s t i r .
       NatRep ('S n)
    -> Knot s t i r
    -> Val Identity Value (Vector ('S n) (Obj (Constant a)) :* i)
    -> Val Identity Value (Obj (Varying 'Z a) :* t)
    -> Val Identity Value (Obj (Varying  n a) :* s)
  prefix_tie nrep kn ip rp =
    let (i, is) = fromProduct ip
        (r, rs) = fromProduct rp

        vec  = vecFromVector (Proxy :: Proxy a) nrep (runIdentity (getRepr i))
        suf  = PrefixList.map fromConstantRep (fromVarying(fromObject (runIdentity (getRepr r))))
        full = PrefixList.fromInitVec_ vec suf

        here  = Varying (PrefixList.map fromConstant full)
        there = knot_prefixes kn (runIdentity (getRepr is)) (runIdentity (getRepr rs))
    in  Language.Pilot.Repr.Product (object here, valuef (Identity there))

  -- Compute the entire streams of the knot: the resulting full streams that
  -- are passed to the output continuation.
  knot_streams :: forall s t i r .
       Knot s t i r
    -> Val Identity Value i
    -> Val Identity Value t
    -> Val Identity Value r
  knot_streams kn i t = case kn of
    Tied nrep _     -> streams_tied nrep i t
    Tie  nrep _ kn' -> streams_tie  nrep kn' i t

  streams_tied
    :: forall n a .
       NatRep ('S n)
    -> Val Identity Value (Vector ('S n) (Obj (Constant a)))
    -> Val Identity Value (Obj (Varying 'Z a))
    -> Val Identity Value (Obj (Varying ('S n) a))
  streams_tied nrep i r =
    let vec  = vecFromVector (Proxy :: Proxy a) nrep i
        suf  = PrefixList.map fromConstantRep (fromVarying (fromObject r))
        full = PrefixList.fromInitVec vec suf
    in  Object (Varying (PrefixList.map fromConstant full))

  streams_tie
    :: forall n a s t i r .
       NatRep ('S n)
    -> Knot s t i r
    -> Val Identity Value (Vector ('S n) (Obj (Constant a)) :* i)
    -> Val Identity Value (Obj (Varying 'Z a) :* t)
    -> Val Identity Value (Obj (Varying ('S n) a) :* r)
  streams_tie nrep kn ip rp =
    let (i, is) = fromProduct ip
        (r, rs) = fromProduct rp

        vec  = vecFromVector (Proxy :: Proxy a) nrep (runIdentity (getRepr i))
        suf  = PrefixList.map fromConstantRep (fromVarying(fromObject (runIdentity (getRepr r))))
        full = PrefixList.fromInitVec vec suf

        here  = Varying (PrefixList.map fromConstant full)
        there = knot_streams kn (runIdentity (getRepr is)) (runIdentity (getRepr rs))
    in  Language.Pilot.Repr.Product (object here, valuef (Identity there))
