{-|
Module      : Language.Pilot.Meta
Description : Definition of meta-language types.
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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Pilot.Meta
  ( Type (..)
  , Obj
  , Terminal
  , type (:->)
  , type (:*)

  , TypeRep (..)
  , object_t
  , to_object_t
  , arrow_t
  , product_t
  , terminal_t
  , (.->)
  , (.*)
  , pattern Obj
  , pattern (:->)
  , pattern (:*)
  , pattern Terminal

  , type Curry
  , type CurryFull
  , type Uncurry
  , type UncurryFull

  ) where

import Language.Pilot.Types

-- | This data kind adds--to some other kind--products, exponentials, and a
-- terminal object. Suggestive of Cartesian closed category.
data Type (t :: Hask) where
  Object_t   :: t -> Type t
  Arrow_t    :: Type t -> Type t -> Type t
  Product_t  :: Type t -> Type t -> Type t
  Terminal_t :: Type t

type Obj = 'Object_t

type Terminal = 'Terminal_t

type (:->) = Arrow_t
infixr 0 :->

type (:*) = Product_t
infixr 2 :*

data TypeRep (rep :: obj -> Hask) (t :: Type obj) where
  Object_r   :: rep t -> TypeRep rep ('Object_t t)
  Arrow_r    :: TypeRep rep s -> TypeRep rep t -> TypeRep rep ('Arrow_t s t)
  Product_r  :: TypeRep rep s -> TypeRep rep t -> TypeRep rep ('Product_t s t)
  Terminal_r :: TypeRep rep 'Terminal_t

{-# COMPLETE Obj, (:->), (:*), Terminal #-}

pattern Obj t = Object_r t
pattern a :-> b = Arrow_r a b
pattern a :* b  = Product_r a b
pattern Terminal = Terminal_r

decEq :: DecEq rep -> DecEq (TypeRep rep)

decEq eqRep (Object_r x) (Object_r y) = case eqRep x y of
  Nothing -> Nothing
  Just Refl -> Just Refl

decEq eqRep (Arrow_r s t) (Arrow_r q r) = case decEq eqRep s q of
  Nothing -> Nothing
  Just Refl -> case decEq eqRep t r of
    Nothing -> Nothing
    Just Refl -> Just Refl

decEq eqRep (Product_r s t) (Product_r q r) = case decEq eqRep s q of
  Nothing -> Nothing
  Just Refl -> case decEq eqRep t r of
    Nothing -> Nothing
    Just Refl -> Just Refl

decEq _ Terminal_r Terminal_r = Just Refl

decEq _ _ _ = Nothing

instance TestEquality rep => TestEquality (TypeRep rep) where
  testEquality = decEq testEquality

instance Represented t => Represented (Type t) where
  type Rep (Type t) = TypeRep (Rep t)

instance Known t => Known ('Object_t t) where
  known _ = Object_r (known (Proxy :: Proxy t))

instance (Known a, Known b) => Known ('Arrow_t a b) where
  known _ = Arrow_r (known (Proxy :: Proxy a)) (known (Proxy :: Proxy b))

instance (Known a, Known b) => Known ('Product_t a b) where
  known _ = Product_r (known (Proxy :: Proxy a)) (known (Proxy :: Proxy b))

instance (Represented k) => Known ('Terminal_t :: Type k) where
  known _ = Terminal_r

to_object_t :: TypeRep rep ('Object_t t) -> rep t
to_object_t (Object_r orep) = orep

object_t :: rep t -> TypeRep rep ('Object_t t)
object_t orep = Object_r orep

terminal_t :: TypeRep rep 'Terminal_t
terminal_t = Terminal_r

arrow_t :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :-> t)
arrow_t = Arrow_r

infixr 0 .->

(.->) :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :-> t)
(.->) = arrow_t

product_t :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :* t)
product_t = Product_r

infixr 2 .*

(.*) :: TypeRep rep s -> TypeRep rep t -> TypeRep rep (s :* t)
(.*) = product_t

-- | Exactly like the function's type
--
--     curry :: ((a, b) -> c) -> (a -> b -> c)
--
type family Curry (t :: Type object) :: Type object where
  Curry ((a :* b) :-> c) = a :-> b :-> c

-- | Exactly like the function's type
--
--     uncurry :: (a -> b -> c) -> ((a, b) -> c)
--
type family Uncurry (t :: Type object) :: Type object where
  Uncurry (a :-> b :-> c) = (a :* b) :-> c

-- | "Fully" uncurry a function: make it into a single arrow type by replacing
-- all top-level arrows a product.
--
--    a :-> (b :-> c :-> d) :-> (e :* f) :-> g  :-> r
--   _________________________________________________
--   (a :*  (b :-> c :-> d) :*  (e :* f) :*  g) :-> r
--
type family UncurryFull (t :: Type object) :: Type object where
  UncurryFull (a :-> (b :-> c)) = Uncurry (a :-> (UncurryFull (b :-> c)))
  UncurryFull (x :-> Obj b)     = x :-> Obj b
  UncurryFull (x :-> Terminal)  = x :-> Terminal
  UncurryFull (x :-> (a :* b))  = x :-> (a :* b)

-- | Inverts 'UncurryFull'
type family CurryFull (t :: Type object) :: Type object where
  CurryFull ((a :* b) :-> c) = a :-> (CurryFull (b :-> c))
  CurryFull (x :-> Obj b)    = x :-> Obj b
  CurryFull (x :-> Terminal) = x :-> Terminal
  CurryFull (x :-> (a :* b)) = x :-> (a :* b)
