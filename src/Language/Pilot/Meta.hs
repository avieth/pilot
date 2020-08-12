{-|
Module      : Language.Pilot.Meta
Description : Definition of meta-language forms over EDSLs.
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

module Language.Pilot.Meta
  ( Type (..)
  , Obj
  , Terminal
  , type (:->)
  , type (:*)

  , Form (..)
  , fun
  , app
  , (<@>)
  , raise
  , lower
  , id
  , compose
  , (<.>)
  , const
  , flip
  , flip_
  , curry
  , uncurry

  , product
  , tuple
  , terminal
  , fst
  , snd
  , (<&)
  , (&>)

  , object

  , Meta_r (..)
  , fromMetaFunctionRep
  , toMetaFunctionRep
  , fromMetaProductRep
  , toMetaProductRep
  , terminalRep
  , toObjectRep
  , fromObjectRep
  , fun_r
  , app_r
  , tuple_r
  , fst_r
  , snd_r

  , metaInterp
  , withObject
  ) where

import Prelude hiding (id, const, curry, uncurry, product, fst, snd, flip, tuple)
import qualified Prelude

import Language.Pilot.Expr
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

data Form (object :: Form_k (Type domain)) (repr :: Repr_k (Type domain)) (t :: Type domain) where
  Terminal_f ::                                 Form object repr Terminal
  Product_f  :: (repr a, repr b)             -> Form object repr (a :* b)
  Fst_f      :: repr (a :* b)                -> Form object repr a
  Snd_f      :: repr (a :* b)                -> Form object repr b
  Fun_f      :: (repr a -> repr b)           -> Form object repr (a :-> b)
  App_f      :: repr (a :-> b)     -> repr a -> Form object repr b
  Object_f   :: object repr t                -> Form object repr t

-- | Meta-language functions on expressions are present in any expression
-- over the 'Meta_r' representation.
fun :: (Expr (Form object) repr a -> Expr (Form object) repr b)
    -> Expr (Form object) repr (a :-> b)
fun f = formal $ \expr value -> Fun_f (\a -> expr (f (value a)))

app :: Expr (Form object) repr (a :-> b)
    -> Expr (Form object) repr a -> Expr (Form object) repr b
app f x = formal $ \expr _ -> App_f (expr f) (expr x)

-- | Left-associative infix version of 'app'. Similar to '<*>'.
(<@>) :: Expr (Form object) repr (a :-> b)
      -> Expr (Form object) repr a -> Expr (Form object) repr b
(<@>) = app

-- 4 because this is the precedence of (<*>)
infixl 4 <@>

-- raise and lower witness an equivalence between Haskell functions and
-- their formal counterparts.

raise :: Expr (Form object) repr (a :-> b)
      -> Expr (Form object) repr a
      -> Expr (Form object) repr b
raise = (<@>)

lower :: (Expr (Form object) repr a -> Expr (Form object) repr b)
      -> Expr (Form object) repr (a :-> b)
lower = fun

id :: Expr (Form object) repr (a :-> a)
id = fun $ \a -> a

compose :: Expr (Form object) repr (a :-> b)
        -> Expr (Form object) repr (b :-> c)
        -> Expr (Form object) repr (a :-> c)
compose f g = fun $ \a -> g <@> (f <@> a)

(<.>) :: Expr (Form object) repr (a :-> b)
      -> Expr (Form object) repr (b :-> c)
      -> Expr (Form object) repr (a :-> c)
(<.>) = compose

-- 9 because this is the precedence of (.)
infixr 9 <.>

const :: Expr (Form object) repr (a :-> b :-> a)
const = fun $ \a -> fun $ \_ -> a

flip :: Expr (Form object) repr (a :-> b :-> c)
     -> Expr (Form object) repr (b :-> a :-> c)
flip f = fun $ \b -> fun $ \a -> f <@> a <@> b

flip_ :: Expr (Form object) repr
  ((a :-> b :-> c) :-> (b :-> a :-> c))
flip_ = lower flip

curry :: Expr (Form object) repr ((a :* b) :-> c)
      -> Expr (Form object) repr (a :-> b :-> c)
curry f = fun $ \a -> fun $ \b -> f <@> (tuple a b)

uncurry :: Expr (Form object) repr (a :-> b :-> c)
        -> Expr (Form object) repr ((a :* b) :-> c)
uncurry f = fun $ \p -> f <@> (fst p) <@> (snd p)

-- | As with meta-language functions (see 'fun' and 'app') we also have
-- meta-language products, or tuples, in any expression over a 'Meta_r'
-- representation.
product :: (Expr (Form object) repr a, Expr (Form object) repr b)
        -> Expr (Form object) repr (a :* b)
product p = formal $ \expr _value -> Product_f (expr (Prelude.fst p), expr (Prelude.snd p))

terminal :: Expr (Form object) repr Terminal
terminal = formal $ \expr _value -> Terminal_f

fst :: Expr (Form object) repr (a :* b)
    -> Expr (Form object) repr a
fst p = formal $ \expr _value -> Fst_f (expr p)

snd :: Expr (Form object) repr (a :* b)
    -> Expr (Form object) repr b
snd p = formal $ \expr _value -> Snd_f (expr p)

tuple :: Expr (Form object) repr a
      -> Expr (Form object) repr b
      -> Expr (Form object) repr (a :* b)
tuple = Prelude.curry product

-- | Right-associative infix version of 'tuple'
(&>) :: Expr (Form object) repr a
     -> Expr (Form object) repr b
     -> Expr (Form object) repr (a :* b)
(&>) = tuple

infixr 2 &>

-- | Left-associative infix version of 'tuple'
(<&) :: Expr (Form object) repr a
     -> Expr (Form object) repr b
     -> Expr (Form object) repr (a :* b)
(<&) = tuple

infixl 2 <&

{-
object
  :: (  (forall x . Expr (Form object) repr x -> repr x)
     -> (forall x . repr x -> Expr (Form object) repr x)
     -> object repr t
     )
  -> Expr (Form object) repr t
object f = formal $ \expr value -> Object_f (f expr value)
-}

-- The idea here is that object forms will not need the `expr` and `value`
-- functions made available to 'formal', since object language forms may use
-- the meta-language abstraction and application forms.
object :: object repr t -> Expr (Form object) repr t
object it = formal $ \_expr _value -> Object_f it

-- | One obvious representation over the `Meta_r t` domain is to use some
-- representation over `t` and add on Haskell functions and products.
data Meta_r (repr :: domain -> Hask) (t :: Type domain) where
  Object_r   :: repr t -> Meta_r repr (Obj t)
  Arrow_r    :: (Meta_r repr s -> Meta_r repr t) -> Meta_r repr (s :-> t)
  Product_r  :: (Meta_r repr s ,  Meta_r repr t) -> Meta_r repr (s :*  t)
  Terminal_r :: Meta_r repr Terminal

withObject :: Meta_r repr (Obj t) -> (repr t -> r) -> r
withObject (Object_r it) k = k it

metaInterp :: Interp form (Meta_r repr) -> Interp (Form form) (Meta_r repr)
metaInterp fobject it = case it of
  Terminal_f -> Terminal_r
  Product_f (a, b) -> Product_r (a, b)
  Fst_f p -> Prelude.fst (toMetaProductRep p)
  Snd_f p -> Prelude.snd (toMetaProductRep p)
  Fun_f f -> Arrow_r f
  App_f f x -> toMetaFunctionRep f x
  Object_f obj -> fobject obj

toMetaFunctionRep :: Meta_r repr (a :-> b) -> Meta_r repr a -> Meta_r repr b
toMetaFunctionRep (Arrow_r f) = f

fromMetaFunctionRep :: (Meta_r repr a -> Meta_r repr b) -> Meta_r repr (a :-> b)
fromMetaFunctionRep = Arrow_r

toMetaProductRep :: Meta_r repr (a :* b) -> (Meta_r repr a, Meta_r repr b)
toMetaProductRep (Product_r p) = p

fromMetaProductRep :: (Meta_r repr a, Meta_r repr b) -> Meta_r repr (a :* b)
fromMetaProductRep = Product_r

terminalRep :: Meta_r repr Terminal
terminalRep = Terminal_r

fromObjectRep :: repr t -> Meta_r repr (Obj t)
fromObjectRep = Object_r

toObjectRep  :: Meta_r repr (Obj t) -> repr t
toObjectRep (Object_r o) = o

fun_r :: (Meta_r repr s -> Meta_r repr t) -> Meta_r repr (s :-> t)
fun_r = fromMetaFunctionRep

app_r :: Meta_r repr (a :-> b) -> Meta_r repr a -> Meta_r repr b
app_r = toMetaFunctionRep

fst_r :: Meta_r repr (a :* b) -> Meta_r repr a
fst_r = Prelude.fst . toMetaProductRep

snd_r :: Meta_r repr (a :* b) -> Meta_r repr b
snd_r = Prelude.snd . toMetaProductRep

tuple_r :: Meta_r repr a -> Meta_r repr b -> Meta_r repr (a :* b)
tuple_r a b = fromMetaProductRep (a, b)
