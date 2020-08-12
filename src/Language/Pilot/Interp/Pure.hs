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

module Language.Pilot.Interp.Pure
  ( Repr
  , Value_r (..)
  , showValue
  , interp
  , constant
  , varying
  ) where

import Language.Pilot.Types
import Language.Pilot.Expr
import Language.Pilot.Meta as Meta
import Language.Pilot.Object as Object

import Language.Pilot.Interp.Pure.Point as Point
import Language.Pilot.Interp.Pure.PrefixList as PrefixList

type Repr = Meta_r Value_r

data Value_r (t :: Object.Type) where
  Constant_r :: Point_r t -> Value_r (Constant t)
  Varying_r  :: PrefixList n Point_r t -> Value_r (Varying n t)

constant :: Point_r t -> Value_r (Constant t)
constant = Constant_r

varying :: PrefixList n Point_r t -> Value_r (Varying n t)
varying = Varying_r

fromVaryingRep :: PrefixList n Point_r t -> Value_r (Varying n t)
fromVaryingRep = Varying_r

toVaryingRep :: Value_r (Varying n t) -> PrefixList n Point_r t
toVaryingRep (Varying_r lst) = lst

showValue :: Prelude.Maybe Int -> Value_r t -> String
showValue n it = case it of
  Constant_r pt  -> Point.prettyPrint pt
  Varying_r  lst -> PrefixList.prettyPrint n Point.prettyPrint lst

toConstantRep :: Value_r (Constant t) -> Point_r t
toConstantRep (Constant_r p) = p

fromConstantRep :: Point_r t -> Value_r (Constant t)
fromConstantRep = Constant_r

thru :: (Meta_r Value_r (Obj (Constant s)) -> Meta_r Value_r (Obj (Constant t)))
     -> (Point_r s -> Point_r t)
thru f = toConstantRep . toObjectRep . f . fromObjectRep . fromConstantRep

interp :: Interp Object.Form Repr
interp form = case form of

  Integer_Literal_UInt8_f  w8  -> fromObjectRep (Constant_r (Integer_r (Point.UInt8 w8)))
  Integer_Literal_UInt16_f w16 -> fromObjectRep (Constant_r (Integer_r (Point.UInt16 w16)))
  Integer_Literal_UInt32_f w32 -> fromObjectRep (Constant_r (Integer_r (Point.UInt32 w32)))
  Integer_Literal_UInt64_f w64 -> fromObjectRep (Constant_r (Integer_r (Point.UInt64 w64)))
  Integer_Literal_Int8_f  i8  -> fromObjectRep (Constant_r (Integer_r (Point.Int8 i8)))
  Integer_Literal_Int16_f i16 -> fromObjectRep (Constant_r (Integer_r (Point.Int16 i16)))
  Integer_Literal_Int32_f i32 -> fromObjectRep (Constant_r (Integer_r (Point.Int32 i32)))
  Integer_Literal_Int64_f i64 -> fromObjectRep (Constant_r (Integer_r (Point.Int64 i64)))
  Bytes_Literal_8_f  w8  -> fromObjectRep (Constant_r (Bytes_r (Point.Word8 w8)))
  Bytes_Literal_16_f w16 -> fromObjectRep (Constant_r (Bytes_r (Point.Word16 w16)))
  Bytes_Literal_32_f w32 -> fromObjectRep (Constant_r (Bytes_r (Point.Word32 w32)))
  Bytes_Literal_64_f w64 -> fromObjectRep (Constant_r (Bytes_r (Point.Word64 w64)))

  Integer_Add_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Integer_r (Point.add x' y')))
  Integer_Subtract_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Integer_r (Point.subtract x' y')))
  Integer_Multiply_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Integer_r (Point.multiply x' y')))
  Integer_Divide_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Integer_r (Point.divide x' y')))
  Integer_Modulo_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Integer_r (Point.modulo x' y')))
  Integer_Negate_f -> fun_r $ \x ->
    let Constant_r (Integer_r x') = toObjectRep x
    in  fromObjectRep (Constant_r (Integer_r (Point.negate x')))
  Integer_Abs_f -> fun_r $ \x ->
    let Constant_r (Integer_r x') = toObjectRep x
    in  fromObjectRep (Constant_r (Integer_r (Point.abs x')))
  Integer_Compare_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Integer_r x') = toObjectRep x
        Constant_r (Integer_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Point.compare x' y'))

  Bytes_And_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Bytes_r x') = toObjectRep x
        Constant_r (Bytes_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Bytes_r (Point.and x' y')))
  Bytes_Or_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Bytes_r x') = toObjectRep x
        Constant_r (Bytes_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Bytes_r (Point.or x' y')))
  Bytes_Xor_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Bytes_r x') = toObjectRep x
        Constant_r (Bytes_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Bytes_r (Point.xor x' y')))
  Bytes_Not_f -> fun_r $ \x ->
    let Constant_r (Bytes_r x') = toObjectRep x
    in  fromObjectRep (Constant_r (Bytes_r (Point.complement x')))
  Bytes_Shiftl_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Bytes_r x') = toObjectRep x
        Constant_r (Bytes_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Bytes_r (Point.shiftl x' y')))
  Bytes_Shiftr_f -> fun_r $ \x -> fun_r $ \y ->
    let Constant_r (Bytes_r x') = toObjectRep x
        Constant_r (Bytes_r y') = toObjectRep y
    in  fromObjectRep (Constant_r (Bytes_r (Point.shiftr x' y')))

  Let_f -> fun_r $ \x -> fun_r $ \f -> let y = x in app_r f y

  Stream_Drop_f  -> fun_r $ \(Object_r (Varying_r p)) -> fromObjectRep (Varying_r (PrefixList.drop p))
  Stream_Shift_f -> fun_r $ \(Object_r (Varying_r p)) -> fromObjectRep (Varying_r (PrefixList.shift p))

  Stream_Lift_f nrep lf -> interp_lift nrep lf
  Stream_Knot_f kn -> interp_knot kn

-- | Implementation of a lift is essentially the notion of the zip list
-- applicative functor, but it looks a lot more complicated because we must
-- convert between the types held in the PrefixList.
interp_lift :: forall n s t . NatRep n -> Lift n s t -> Meta_r Value_r (s :-> t)
interp_lift nrep lf = fun_r $ \s ->
  let lst :: PrefixList n (Meta_r Value_r) s
      lst = PrefixList.repeat nrep s
  in  recursive_lift nrep lf lst

  where

  recursive_lift
    :: forall n s t .
       NatRep n
    -> Lift n s t
    -> PrefixList n (Meta_r Value_r) s
    -> Meta_r Value_r t
  recursive_lift nrep lf lst = case lf of

    -- Here we find that
    --
    --   s ~ Obj (Constant a)
    --   t ~ Obj (Varying n a)
    --
    -- so the list already has what we need, we just have to convert the
    -- representation type.
    Pure   -> fromObjectRep (Varying_r (fromPrefixWithMeta_ lst))

    -- Whereas here we have
    --
    --   s ~ Obj (Constant a) :-> s1
    --   t ~ Obj (Varying n a) :-> t1
    --
    -- and so we want to take in an argument, and zip-apply the functions in `lst`
    -- to it. That argument x has type
    --
    --   x :: Meta_r Value_r (Obj (Varying n a))
    --
    -- and in order to zip-apply `lst` to it, we have to make it into a
    -- PrefixList n (Meta_r Value_r) (Obj (Varying n a))
    Ap lf' -> fun_r $ \x ->
      let x' = toPrefixWithMeta_ (fromVarying x)
      in  recursive_lift nrep lf' (prefixWithMetaAp lst x')

  toPrefixWithMeta :: forall n t . PrefixList n Point_r t -> PrefixList n (Meta_r Point_r) (Obj t)
  toPrefixWithMeta = PrefixList.map fromObjectRep

  fromPrefixWithMeta :: forall n t . PrefixList n (Meta_r Point_r) (Obj t) -> PrefixList n Point_r t
  fromPrefixWithMeta = PrefixList.map toObjectRep

  prefixWithMetaAp
    :: forall n f s t .
       PrefixList n (Meta_r f) (s :-> t)
    -> PrefixList n (Meta_r f) s
    -> PrefixList n (Meta_r f) t
  prefixWithMetaAp = PrefixList.meld app_r

  toPrefixWithMeta_ :: forall n t . PrefixList n Point_r t -> PrefixList n (Meta_r Value_r) (Obj (Constant t))
  toPrefixWithMeta_ = PrefixList.map (fromObjectRep . fromConstantRep)

  fromPrefixWithMeta_ :: forall n t . PrefixList n (Meta_r Value_r) (Obj (Constant t)) -> PrefixList n Point_r t
  fromPrefixWithMeta_ = PrefixList.map (toConstantRep . toObjectRep)

  fromVarying :: forall n t . Meta_r Value_r (Obj (Varying n t)) -> PrefixList n Point_r t
  fromVarying (Object_r (Varying_r lst)) = lst

  toVarying :: forall n t . PrefixList n Point_r t -> Meta_r Value_r (Obj (Varying n t))
  toVarying lst = Object_r (Varying_r lst)

-- |
interp_knot
  :: forall s t q i r .
     Knot s t q i
  -> Meta_r Value_r ((s :-> t) :-> (q :-> r) :-> (i :-> r))
interp_knot kn = fun_r $ \fknot -> fun_r $ \fcont -> fun_r $ \inits ->

  -- We have
  --
  --   fknot :: s :-> t
  --   fcont :: q :-> r
  --   inits :: i
  --
  -- where s t q i are related by the GADT value kn.
  --
  -- Suppose we match on the first and its a Tie. In this case, we can
  -- get
  --
  --   s ~ Obj (Varying n a) :* s1
  --   t ~ Obj (Varying Z a) :* t1
  --   q ~ Obj (Varying (S n) a :* q1
  --   i ~ Vector (S n) (Obj (Constant a)) :* i1
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
  let prefixes = knot_prefixes kn inits suffixes
      streams  = knot_streams kn inits suffixes
      suffixes = app_r fknot prefixes
  in  app_r fcont streams

  where

  -- This whole thing could probably be shortened, but it's not worth the time
  -- at the moment.

  -- Compute the prefixes of the knot: the inputs to the knot-tying function.
  knot_prefixes :: forall s t q i .
       Knot s t q i
    -> Meta_r Value_r i
    -> Meta_r Value_r t
    -> Meta_r Value_r s
  knot_prefixes kn i t = case kn of
    Tied nrep     -> prefix_tied nrep i t
    Tie  nrep kn' -> prefix_tie  nrep kn' i t

  -- Compute the entire streams of the knot: the resulting full streams that
  -- are passed to the output continuation.
  knot_streams :: forall s t q i .
       Knot s t q i
    -> Meta_r Value_r i
    -> Meta_r Value_r t
    -> Meta_r Value_r q
  knot_streams kn i t = case kn of
    Tied nrep     -> streams_tied nrep i t
    Tie  nrep kn' -> streams_tie  nrep kn' i t

  prefix_tied
    :: forall n a .
       NatRep ('S n)
    -> Meta_r Value_r (Vector ('S n) (Obj (Constant a)))
    -> Meta_r Value_r (Obj (Varying 'Z a))
    -> Meta_r Value_r (Obj (Varying n a))
  prefix_tied nrep i t = case toObjectRep t of
    Varying_r lst ->
      let vec = vecFromVector (Proxy :: Proxy (Obj (Constant a))) nrep i
          suf = PrefixList.map (fromObjectRep . fromConstantRep) lst
          rep = PrefixList.fromInitVec_ vec suf
          pre = fromObjectRep (fromVaryingRep (PrefixList.map (toConstantRep . toObjectRep) rep))
      in  pre

  prefix_tie
    :: forall n a s t q i .
       NatRep ('S n)
    -> Knot s t q i
    -> Meta_r Value_r (Vector ('S n) (Obj (Constant a)) :* i)
    -> Meta_r Value_r (Obj (Varying 'Z a) :* t)
    -> Meta_r Value_r (Obj (Varying  n a) :* s)
  prefix_tie nrep kn i t = case toObjectRep (fst_r t) of
    Varying_r lst ->
      let vec = vecFromVector (Proxy :: Proxy (Obj (Constant a))) nrep (fst_r i)
          suf = PrefixList.map (fromObjectRep . fromConstantRep) lst
          rep = PrefixList.fromInitVec_ vec suf
          pre = fromObjectRep (fromVaryingRep (PrefixList.map (toConstantRep . toObjectRep) rep))
          rec = knot_prefixes kn (snd_r i) (snd_r t)
      in  tuple_r pre rec

  streams_tied
    :: forall n a .
       NatRep ('S n)
    -> Meta_r Value_r (Vector ('S n) (Obj (Constant a)))
    -> Meta_r Value_r (Obj (Varying 'Z a))
    -> Meta_r Value_r (Obj (Varying ('S n) a))
  streams_tied nrep i t = case toObjectRep t of
    Varying_r lst ->
      let vec = vecFromVector (Proxy :: Proxy (Obj (Constant a))) nrep i
          suf = PrefixList.map (fromObjectRep . fromConstantRep) lst
          rep = PrefixList.fromInitVec vec suf
          pre = fromObjectRep (fromVaryingRep (PrefixList.map (toConstantRep . toObjectRep) rep))
      in  pre

  streams_tie
    :: forall n a s t q i .
       NatRep ('S n)
    -> Knot s t q i
    -> Meta_r Value_r (Vector ('S n) (Obj (Constant a)) :* i)
    -> Meta_r Value_r (Obj (Varying 'Z a) :* t)
    -> Meta_r Value_r (Obj (Varying ('S n) a) :* q)
  streams_tie nrep kn i t = case toObjectRep (fst_r t) of
    Varying_r lst ->
      let vec = vecFromVector (Proxy :: Proxy (Obj (Constant a))) nrep (fst_r i)
          suf = PrefixList.map (fromObjectRep . fromConstantRep) lst
          rep = PrefixList.fromInitVec vec suf
          pre = fromObjectRep (fromVaryingRep (PrefixList.map (toConstantRep . toObjectRep) rep))
          rec = knot_streams kn (snd_r i) (snd_r t)
      in  tuple_r pre rec

  -- The proxy is here because Vector is a non-injective type family
  vecFromVector
    :: forall n t .
       Proxy t
    -> NatRep n
    -> Meta_r Value_r (Vector n t)
    -> Vec n (Meta_r Value_r t)
  vecFromVector _  Z_Rep                  _                        = VNil
  vecFromVector _  (S_Rep Z_Rep)          t                        = VCons t VNil
  vecFromVector pt (S_Rep nrep@(S_Rep _)) (Meta.Product_r (t, ts)) = VCons t (vecFromVector pt nrep ts)
