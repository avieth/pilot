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

module Language.Pilot.Interp.Pure
  ( Value_r (..)
  , Identity (..)
  , showValue
  , interp_pure
  , constant
  , varying
  ) where

import Data.Functor.Identity (Identity (..))

import Language.Pilot.Types
import Language.Pilot.Meta (Obj, type (:->), type (:*))
import Language.Pilot.Object as Object hiding (constant)
import Language.Pilot.Repr

import Language.Pilot.Interp.Pure.Point as Point
import Language.Pilot.Interp.Pure.PrefixList as PrefixList

instance Interprets Object.Form Identity Value_r where
  interp = interp_pure

data Value_r (t :: Object.Type) where
  Constant_r :: Point_r t -> Value_r (Constant t)
  Varying_r  :: PrefixList n Point_r t -> Value_r (Varying n t)

showValue :: Prelude.Maybe Int -> Value_r t -> String
showValue n it = case it of
  Constant_r pt  -> Point.prettyPrint pt
  Varying_r  lst -> PrefixList.prettyPrint n Point.prettyPrint lst

applyConstant :: (Point_r s -> Point_r t)
              -> (Value_r (Constant s) -> Value_r (Constant t))
applyConstant f = \(Constant_r p) -> Constant_r (f p)

applyVarying :: (PrefixList n Point_r s -> PrefixList m Point_r t)
             -> (Value_r (Varying n s) -> Value_r (Varying m t))
applyVarying f = \(Varying_r lst) -> Varying_r (f lst)

constant :: Point_r t -> Value_r (Constant t)
constant = Constant_r

varying :: PrefixList n Point_r t -> Value_r (Varying n t)
varying = Varying_r

fromVarying :: Value_r (Varying n t) -> PrefixList n Point_r t
fromVarying (Varying_r lst) = lst

fromVaryingRep :: PrefixList n Point_r t -> Value_r (Varying n t)
fromVaryingRep = Varying_r

toVaryingRep :: Value_r (Varying n t) -> PrefixList n Point_r t
toVaryingRep (Varying_r lst) = lst

fromConstant :: Value_r (Constant t) -> Point_r t
fromConstant (Constant_r p) = p

fromConstantRep :: Point_r t -> Value_r (Constant t)
fromConstantRep = Constant_r


liftPoint :: (Point_r a -> Point_r b)
          -> Val f Value_r (Obj (Constant a))
          -> Val f Value_r (Obj (Constant b))
liftPoint f (Object (Constant_r a)) = Object (Constant_r (f a))

liftPoint2 :: (Point_r a -> Point_r b -> Point_r c)
           -> Val f Value_r (Obj (Constant a))
           -> Val f Value_r (Obj (Constant b))
           -> Val f Value_r (Obj (Constant c))
liftPoint2 f (Object (Constant_r a)) (Object (Constant_r b)) = Object (Constant_r (f a b))

interp_pure :: Interpret Object.Form Identity Value_r
interp_pure form = case form of

  Integer_Literal_UInt8_f  w8  -> object (Constant_r (Integer_r (Point.UInt8 w8)))
  Integer_Literal_UInt16_f w16 -> object (Constant_r (Integer_r (Point.UInt16 w16)))
  Integer_Literal_UInt32_f w32 -> object (Constant_r (Integer_r (Point.UInt32 w32)))
  Integer_Literal_UInt64_f w64 -> object (Constant_r (Integer_r (Point.UInt64 w64)))
  Integer_Literal_Int8_f  i8  -> object (Constant_r (Integer_r (Point.Int8 i8)))
  Integer_Literal_Int16_f i16 -> object (Constant_r (Integer_r (Point.Int16 i16)))
  Integer_Literal_Int32_f i32 -> object (Constant_r (Integer_r (Point.Int32 i32)))
  Integer_Literal_Int64_f i64 -> object (Constant_r (Integer_r (Point.Int64 i64)))
  Bytes_Literal_8_f  w8  -> object (Constant_r (Bytes_r (Point.Word8 w8)))
  Bytes_Literal_16_f w16 -> object (Constant_r (Bytes_r (Point.Word16 w16)))
  Bytes_Literal_32_f w32 -> object (Constant_r (Bytes_r (Point.Word32 w32)))
  Bytes_Literal_64_f w64 -> object (Constant_r (Bytes_r (Point.Word64 w64)))

  -- Here we have x and y, which are each of type
  --   Repr f Value_r (Obj (Constant (Integer_t s w)))
  -- We do not wish to impose any particular order of evaluation on the
  -- arguments, so we'll want to use the applicative instance on f to apply
  -- `Point.add`, which itself must be "lifted" through the Value_r type.
  Integer_Add_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.add <$> getRepr x <*> getRepr y)
  Integer_Subtract_f -> fun $ \x -> fun $ \y ->
    repr (liftPoint2 Point.add <$> getRepr x <*> getRepr y)
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

  Cast_f c -> case c of {}

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

  Stream_Lift_f nrep lf -> interp_lift nrep lf
  Stream_Knot_f kn -> interp_knot kn

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
  -> Repr f Value_r (r :-> Obj (Constant (Product fields)))
interp_product_intro fields = fun $ \r -> objectf $ 
  fmap bundle (evaluate fields r)

  where

  evaluate
    :: forall r fields .
       Fields r fields
    -> Repr f Value_r r
    -> f (Point.All Point.Point_r fields)
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
       Point.All Point.Point_r fields
    -> Value_r (Constant (Product fields))
  bundle = fromConstantRep . Point.Product_r

interp_sum_intro
  :: forall f r variants .
     ( Applicative f )
  => Variant r variants
  -> Repr f Value_r (r :-> Obj (Constant (Sum variants)))
interp_sum_intro variant = fun $ \v -> objectf $
  fmap (fromConstantRep . Point.Sum_r) (inject variant v)

  where

  inject
    :: forall r variants .
       Variant r variants
    -> Repr f Value_r r
    -> f (Point.Any Point.Point_r variants)
  inject V_This        v = fmap (Point.Any . fromConstant . fromObject) (getRepr v)
  inject (V_That that) v = fmap Point.Or (inject that v)

-- |
--
-- TODO is this lazy enough? We ought to be able to come up with the entire
-- function type without actually evaluating the product itself, instead looking
-- only at the `Selector`.
interp_product_elim
  :: forall f q r fields .
     ( Monad f )
  => Selector fields q r
  -> Repr f Value_r (Obj (Constant (Product fields)) :-> q)
interp_product_elim selector = fun $ \p -> valuef $ do
  -- Get the representation of the product...
  fields <- fmap (fromConstant . fromObject) (getRepr p)
  -- Then use the selector to figure out which type of projection function
  -- to take, and apply it to the relevant field.
  getRepr (select selector fields)

  where

  select
    :: forall fields r .
       Selector fields q r
    -> Point_r (Product fields)
    -> Repr f Value_r q
  select (S_There s) (Product_r (And _ ps)) = select s (Product_r ps)
  select S_Here      (Product_r (And it _)) = fun $ \proj ->
    app proj (object (fromConstantRep it))

interp_sum_elim
  :: forall f r variants .
     ( Monad f )
  => Cases variants r
  -> Repr f Value_r (Obj (Constant (Sum variants)) :-> r)
interp_sum_elim cases = fun $ \scrutinee -> valuef $ do
  -- Evaluate the scrutinee...
  v <- fmap (fromConstant . fromObject) (getRepr scrutinee)
  -- Use the Cases to match on the scrutinee.
  getRepr (match cases v)

  where

  match
    :: forall r variants .
       Cases variants r
    -> Point_r (Sum variants)
    -> Repr f Value_r r
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
    -> Point_r (Sum (variant ': variants))
    -> Repr f Value_r ((Obj (Constant variant) :-> r) :* q)
    -> Repr f Value_r r
  eliminate _ (Point.Sum_r (Point.Any it)) elims =
    app (Language.Pilot.Repr.fst elims) (object (fromConstantRep it))
  eliminate (C_Or cs) (Point.Sum_r (Point.Or sum)) elims =
    eliminate cs (Point.Sum_r sum) (Language.Pilot.Repr.snd elims)
  eliminate C_Any (Point.Sum_r (Point.Or sum)) _ = case sum of {}


-- | Implementation of a lift is essentially the notion of the zip list
-- applicative functor, but it looks a lot more complicated because we must
-- convert between the types held in the PrefixList.
interp_lift
  :: forall f n s t .
     ( Monad f )
  => NatRep n
  -> Lift n s t
  -> Repr f Value_r (s :-> t)
interp_lift nrep lf = fun $ \sr ->
  -- The argument `sr` is either a constant, or a first-order function over
  -- constants. This is proven by the `Lift` value `lf`. For each `Ap`
  -- constructor, we add a function argument which takes a varying instead, and
  -- zip this with whatever we have so far. Then, at the `Pure` case, we convert
  -- to the expected PrefixList type.
  let lst :: f (PrefixList n (Val f Value_r) s)
      lst = fmap (PrefixList.repeat nrep) (getRepr sr)
  in  recursive_lift nrep lf lst

  where

  recursive_lift
    :: forall n s t .
       NatRep n
    -> Lift n s t
    -> f (PrefixList n (Val f Value_r) s)
    -> Repr f Value_r t
  recursive_lift nrep lf lst = case lf of

    -- Here we find that
    --
    --   s ~ Obj (Constant a)
    --   t ~ Obj (Varying n a)
    --
    -- so the list already has what we need, we just have to convert the
    -- representation type.
    Pure -> fromPrefixWithRepr lst

    -- Whereas here we have
    --
    --   s ~ Obj (Constant a) :-> s1
    --   t ~ Obj (Varying n a) :-> t1
    --
    -- and so we want to take in an argument, and zip-apply the functions in
    -- `lst` to it. That argument x has type
    --
    --   x :: Repr f Value_r (Obj (Varying n a))
    --
    Ap lf' -> fun $ \x -> recursive_lift nrep lf' (prefixWithReprAp lst x)

  prefixWithReprAp
    :: forall n s t .
       f (PrefixList n (Val f Value_r) (Obj (Constant s) :-> t))
    -> Repr f Value_r (Obj (Varying n s))
    -> f (PrefixList n (Val f Value_r) t)
  prefixWithReprAp ffs fxs = do
    fs <- ffs
    xs <- toPrefixWithRepr fxs
    fmeld (\f x -> getRepr (fromArrow f (value x))) fs xs

  toPrefixWithRepr
    :: forall n s .
       Repr f Value_r (Obj (Varying n s))
    -> f (PrefixList n (Val f Value_r) (Obj (Constant s)))
  toPrefixWithRepr rx = do
    x <- fmap fromObject (getRepr rx)
    case x of
      Varying_r lst -> pure (PrefixList.map (Object . constant) lst)

  fromPrefixWithRepr
    :: forall n s .
       f (PrefixList n (Val f Value_r) (Obj (Constant s)))
    -> Repr f Value_r (Obj (Varying n s))
  fromPrefixWithRepr fx = objectf $ do
    lst <- fx
    pure (varying (PrefixList.map (fromConstant . fromObject) lst))

-- |
interp_knot
  :: forall s t q i r .
     Knot s t q i
  -> Repr Identity Value_r ((s :-> t) :-> (q :-> r) :-> (i :-> r))
interp_knot kn = fun $ \fknot -> fun $ \fcont -> fun $ \inits ->
  -- We have
  --
  --   fknot :: s :-> t
  --   fcont :: q :-> r
  --   inits :: i
  --
  -- where s t q i are related by the GADT value kn.
  --
  -- Suppose we match on the first and it's a Tie. In this case, we can
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
  let initvals = runIdentity (getRepr inits)
      prefixes = knot_prefixes kn initvals suffixes
      streams  = knot_streams kn initvals suffixes
      suffixes = runIdentity . getRepr . app fknot . valuef . Identity $ prefixes
      results  = runIdentity . getRepr . app fcont . valuef . Identity $ streams
  in  valuef . Identity $ results

  where

  -- Construct a Vec, eliminating the Vector type family.
  -- The proxy is here because Vector is a non-injective type family.
  vecFromVector
    :: forall n t .
       Proxy t
    -> NatRep n
    -> Val Identity Value_r (Vector n (Obj (Constant t)))
    -> Vec n (Value_r (Constant t))
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
  knot_prefixes :: forall s t q i .
       Knot s t q i
    -> Val Identity Value_r i
    -> Val Identity Value_r t
    -> Val Identity Value_r s
  knot_prefixes kn i t = case kn of
    Tied nrep     -> prefix_tied nrep i t
    Tie  nrep kn' -> prefix_tie  nrep kn' i t

  -- Compute the entire streams of the knot: the resulting full streams that
  -- are passed to the output continuation.
  knot_streams :: forall s t q i .
       Knot s t q i
    -> Val Identity Value_r i
    -> Val Identity Value_r t
    -> Val Identity Value_r q
  knot_streams kn i t = case kn of
    Tied nrep     -> streams_tied nrep i t
    Tie  nrep kn' -> streams_tie  nrep kn' i t

  prefix_tied
    :: forall n a .
       NatRep ('S n)
    -> Val Identity Value_r (Vector ('S n) (Obj (Constant a)))
    -> Val Identity Value_r (Obj (Varying 'Z a))
    -> Val Identity Value_r (Obj (Varying n a))
  prefix_tied nrep i r =
    let vec  = vecFromVector (Proxy :: Proxy a) nrep i
        suf  = PrefixList.map fromConstantRep (fromVarying (fromObject r))
        full = PrefixList.fromInitVec_ vec suf
    in  Object (Varying_r (PrefixList.map fromConstant full))

  prefix_tie
    :: forall n a s t q i .
       NatRep ('S n)
    -> Knot s t q i
    -> Val Identity Value_r (Vector ('S n) (Obj (Constant a)) :* i)
    -> Val Identity Value_r (Obj (Varying 'Z a) :* t)
    -> Val Identity Value_r (Obj (Varying  n a) :* s)
  prefix_tie nrep kn ip rp =
    let (i, is) = fromProduct ip
        (r, rs) = fromProduct rp

        vec  = vecFromVector (Proxy :: Proxy a) nrep (runIdentity (getRepr i))
        suf  = PrefixList.map fromConstantRep (fromVarying(fromObject (runIdentity (getRepr r))))
        full = PrefixList.fromInitVec_ vec suf

        here  = Varying_r (PrefixList.map fromConstant full)
        there = knot_prefixes kn (runIdentity (getRepr is)) (runIdentity (getRepr rs))
    in  Language.Pilot.Repr.Product (object here, valuef (Identity there))

  streams_tied
    :: forall n a .
       NatRep ('S n)
    -> Val Identity Value_r (Vector ('S n) (Obj (Constant a)))
    -> Val Identity Value_r (Obj (Varying 'Z a))
    -> Val Identity Value_r (Obj (Varying ('S n) a))
  streams_tied nrep i r =
    let vec  = vecFromVector (Proxy :: Proxy a) nrep i
        suf  = PrefixList.map fromConstantRep (fromVarying (fromObject r))
        full = PrefixList.fromInitVec vec suf
    in  Object (Varying_r (PrefixList.map fromConstant full))

  streams_tie
    :: forall n a s t q i .
       NatRep ('S n)
    -> Knot s t q i
    -> Val Identity Value_r (Vector ('S n) (Obj (Constant a)) :* i)
    -> Val Identity Value_r (Obj (Varying 'Z a) :* t)
    -> Val Identity Value_r (Obj (Varying ('S n) a) :* q)
  streams_tie nrep kn ip rp =
    let (i, is) = fromProduct ip
        (r, rs) = fromProduct rp

        vec  = vecFromVector (Proxy :: Proxy a) nrep (runIdentity (getRepr i))
        suf  = PrefixList.map fromConstantRep (fromVarying(fromObject (runIdentity (getRepr r))))
        full = PrefixList.fromInitVec vec suf

        here  = Varying_r (PrefixList.map fromConstant full)
        there = knot_streams kn (runIdentity (getRepr is)) (runIdentity (getRepr rs))
    in  Language.Pilot.Repr.Product (object here, valuef (Identity there))
