{-|
Module      : Language.Pilot.Repr
Description : Meta-language functions and products over an arbitrary object-language representation.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pilot.Repr
  (
    -- * Representation types
    Repr (..)
  , Val (..)

  , fromObject
  , fromArrow
  , fromProduct
  , fromTerminal

    -- * Constructing representations
  , repr
  , valuef
  , value
  , objectf
  , object
  , formal

  , fun
  , app
  , (<@>)
  , identity
  , compose
  , const
  , (<.>)
  , flip
  , curry
  , uncurry
  , product
  , (<&)
  , (&>)
  , terminal
  , fst
  , snd

  -- * Interpretation
  , Interpret
  , Interprets (..)
  , E
  ) where

import Prelude hiding (id, const, curry, uncurry, product, fst, snd, flip)
import qualified Prelude
import Language.Pilot.Types
import Language.Pilot.Meta as Meta (Type (..), Obj, Terminal, type (:->), type (:*))
import qualified Language.Pilot.Meta as Meta

import Data.Functor.Identity

-- | This is the target of an EDSL over a given domain. The types `f` and `val`
-- determine the representation, but the meta-language functions and products
-- are always the same, as given by the 'Val' type.
newtype Repr (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta.Type domain) = Repr
  { getRepr :: f (Val f val t) }

-- | A value in the representation of some EDSL target. Haskell functions and
-- products are here, along with some object-language representation
-- determined by `val`.
data Val (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta.Type domain) where
  Object   :: val t -> Val f val (Obj t)
  Arrow    :: (Repr f val s -> Repr f val t) -> Val f val (s :-> t)
  Product  :: (Repr f val s ,  Repr f val t) -> Val f val (s :*  t)
  Terminal :: Val f val Terminal

fromObject :: Val f val (Obj t) -> val t
fromObject (Object v) = v

fromArrow :: Val f val (s :-> t) -> (Repr f val s -> Repr f val t)
fromArrow (Arrow f) = f

fromProduct :: Val f val (s :* t) -> (Repr f val s, Repr f val t)
fromProduct (Product p) = p

fromTerminal :: Val f val Terminal -> ()
fromTerminal Terminal = ()

objectf :: Functor f => f (val t) -> Repr f val (Obj t)
objectf it = Repr (fmap Object it)

object :: Applicative f => val t -> Repr f val (Obj t)
object it = objectf (pure it)

valuef :: f (Val f val t) -> Repr f val t
valuef = Repr

repr :: f (Val f val t) -> Repr f val t
repr = Repr

value :: Applicative f => Val f val t -> Repr f val t
value = valuef . pure

fun :: Applicative f => (Repr f val s -> Repr f val t) -> Repr f val (s :-> t)
fun f = Repr (pure (Arrow f))

-- Does this make sense? In the monad f we have ordered evaluation of the
-- function before that of the argument. But that makes perfect sense: the
-- function takes a Repr, so _it_ may choose when/if to actually evaluate it.
app :: Monad f => Repr f val (s :-> t) -> Repr f val s -> Repr f val t
app fr xr = Repr $ do
  it <- getRepr fr
  getRepr (fromArrow it xr)

(<@>):: Monad f => Repr f val (s :-> t) -> Repr f val s -> Repr f val t
(<@>) = app

infixl 9 <@>

identity :: Applicative f => Repr f val (s :-> s)
identity = fun $ \a -> a

compose :: Monad f => Repr f val ((s :-> t) :-> (t :-> u) :-> (s :-> u))
compose = fun $ \f -> fun $ \g -> fun $ \s -> g <@> (f <@> s)

-- | 'compose' is more useful if we can infix it, but in order to do that we
-- have to bring it out of Repr.
--
-- This one also puts the arguments in the expected order for dot.
(<.>) :: Monad f
      => Repr f val (t :-> u)
      -> Repr f val (s :-> t)
      -> Repr f val (s :-> u)
(<.>) g f = fun $ \s -> g <@> (f <@> s)

infixr 9 <.>

const :: Applicative f => Repr f val (s :-> t :-> s)
const = fun $ \a -> fun $ \_ -> a

flip :: Monad f => Repr f val ((s :-> t :-> u) :-> (t :-> s :-> u))
flip = fun $ \f -> fun $ \t -> fun $ \s -> f <@> s <@> t

curry :: Monad f => Repr f val (((s :* t) :-> u) :-> (s :-> t :-> u))
curry = fun $ \f -> fun $ \s -> fun $ \t -> f <@> (s <& t)

uncurry :: Monad f => Repr f val ((s :-> t :-> u) :-> ((s :* t) :-> u))
uncurry = fun $ \f -> fun $ \p -> f <@> (fst p) <@> (snd p)

product :: Applicative f => (Repr f val s, Repr f val t) -> Repr f val (s :* t)
product p = Repr (pure (Product p))

(<&) :: Applicative f => Repr f val s -> Repr f val t -> Repr f val (s :* t)
(<&) x y = product (x, y)

infixl 2 <&

(&>) :: Applicative f => Repr f val s -> Repr f val t -> Repr f val (s :* t)
(&>) x y = product (x, y)

infixr 2 &>

terminal :: Applicative f => Repr f val Terminal
terminal = Repr (pure Terminal)

fst :: Monad f => Repr f val (s :* t) -> Repr f val s
fst r = Repr $ do
  it <- getRepr r
  getRepr (Prelude.fst (fromProduct it))

snd :: Monad f => Repr f val (s :* t) -> Repr f val t
snd r = Repr $ do
  it <- getRepr r
  getRepr (Prelude.snd (fromProduct it))

type Interpret (form :: Meta.Type domain -> Hask) f val = forall (x :: Meta.Type domain) . Rep (Meta.Type domain) x -> form x -> Repr f val x

class Monad f => Interprets (form :: Meta.Type domain -> Hask) (f :: Hask -> Hask) (val :: domain -> Hask) where
  interp :: Interpret form f val

formal
  :: forall domain form f val (t :: Meta.Type domain) .
     ( Interprets form f val )
  => Rep (Meta.Type domain) t
  -> form t
  -> E form f val t
formal trep frm = interp trep frm

-- | This is the expression type over a given form, in the "tagless final" style
-- using a typeclass, because it allows us to seamlessly include
-- interpreter-specific things.
--
-- Note that the type `form` appears only in the constraint, and so using E
-- where `form` is not a monotype leads to ambiguity. But that's fine, because
-- `E` should only ever be used with `form` as a monotype! After all, if you're
-- writing an expression in some known EDSL, then by definition you also know
-- the form. For expressions which work over any EDSL, we have the meta-language
-- constructions given above, which are not `E` but are more general and will
-- unify with an `E`.
type E form f val t = Interprets form f val => Repr f val t

data EmptyForm (x :: Meta.Type domain)

example_1 :: Applicative f => Repr f val (s :-> t :-> (s :* t))
example_1 = fun $ \x -> fun $ \y -> product (x, y)

example_2 :: E EmptyForm f val (s :-> t :-> (s :* t))
example_2 = example_1

-- Case study:  suppose we define a function behind some let bindings.
-- Whenever we apply the function, those let bindings will affect the context.
-- So applying this function twice induces the let bindings twice.
-- We'd want to allow for the expression of: evaluate the function (inducing
-- the bindings) and then apply the evaluated function multiple times. Can
-- this be done? Maybe what we have to  do is allow for the let form to bind
-- even non-object things? The interpreter would be able to discriminate here:
-- if an object-thing is bound, then make a C assignment statement with the
-- relevant thing... but if a function is bound, include its binding context
-- and give back a function which has no extra context? Seems reasonable...

-- Also NB: we don't even need the repr type in the forms......... that's
-- because we have access to functions and products, so we can express what
-- would otherwise require a repr reference....

data LetDomain where
  LetType :: LetDomain

data LetDomainRep (t :: LetDomain) where
  LetType_r :: LetDomainRep 'LetType

instance Represented LetDomain where
  type Rep LetDomain = LetDomainRep

lettype_t :: LetDomainRep 'LetType
lettype_t = LetType_r

instance Known 'LetType where
  known _ = LetType_r

data LetForm (x :: Meta.Type LetDomain) where
  Datum :: LetForm (Obj 'LetType)
  Let :: LetForm (a :-> (a :-> b) :-> b)

example_3 :: E LetForm f val (Obj 'LetType :* Obj 'LetType)
example_3 = example_1 <@> formal (Meta.object_t lettype_t) Datum
                      <@> formal  auto                     Datum

data DummyVal (t :: LetDomain) where
  DummyVal :: DummyVal 'LetType

instance Interprets LetForm Identity DummyVal where
  interp _ Datum = object DummyVal
  -- In this case, f and x are `Repr Identity DummyVal _`, so we can actually
  -- check what's going on, and special case for values.
  --
  -- Here's an interesting example to keep in mind: the commented-out definition
  -- is different from the given one. The first does nothing special for
  -- let bindings, but the second potentially does save some work.
  --
  --interp Let = fun $ \x -> fun $ \f -> app f x
  interp _ Let = fun $ \x -> fun $ \f -> Repr $ do
    -- Eval the context here ...
    x' <- getRepr x
    -- ... then run the continuation with the context-free Val
    getRepr (app f (value x'))
