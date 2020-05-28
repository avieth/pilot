{-|
Module      : Pilot.EDSL.Expr
Description : Expressions over an arbitrary EDSL, with bindings.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pilot.EDSL.Expr
  ( EDSL
  , Hask
  , ExprM (..)
  , Expr (..)
  , evalExprM
  , special
  , knownValue
  , exprF
  , exprM
  , expr
  , bind
  , name
  , subst
  , local
  ) where

import qualified Data.Kind as Haskell (Type)

type Hask = Haskell.Type

-- | The kind of an EDSL. It's just some "functor" like thing with any kind as
-- its domain. The parameter represents recursion: the EDSL GADT itself is
-- not recursive, but uses this parameter to stand in for expressions of its
-- own form.
--
-- Here just for the hope that it will be useful as communication/documentation.
-- "Kind synonyms" don't seem too useful at the moment.
type EDSL domain = (domain -> Haskell.Type) -> domain -> Haskell.Type

-- | The straightforward, "obvious" way to make an EDSL recursive: plug the
-- hole with the EDSL type itself.
--
-- This is just here to contrast with 'ExprM'.
newtype Fix edsl t = Fix { getFix :: edsl (Fix edsl) t }

-- | This is a monad over a given EDSL which includes a notion of
-- naming/binding.
--
-- An `ExprM edsl val f t` which is free in `val` and and monad `f` is
-- essentially just the recursive EDSL with naming and substitution.
--
-- The `val` type is needed because it takes the EDSL-specific `domain` type
-- to Hask (Haskell types).
newtype ExprM (edsl :: EDSL domain) (val :: domain -> Hask) (f :: Hask -> Hask) (t :: Hask) = ExprM
  { runExprM :: (forall x . edsl (Expr edsl val f) x -> f (val x))
             -- ^ Interpret the (recursive) EDSL in f.
             -> (forall x . val x -> f (val x))
             -- ^ Bind a value to a name in the meta-language (HOAS like).
             -> f t
  }

-- | Like 'ExprM' but with a different kind. The final parameter is in the
-- EDSL's domain, and appears behind a `val` type constructor.
newtype Expr (edsl :: EDSL domain) (val :: domain -> Hask) (f :: Hask -> Hask) (t :: domain) = Expr
  { runExpr :: ExprM edsl val f (val t) }

instance Functor f => Functor (ExprM exprF val f) where
  fmap f m = ExprM $ \interp name -> fmap f (runExprM m interp name)

instance Applicative f => Applicative (ExprM exprF val f) where
  pure x = ExprM $ \_ _ -> pure x
  mf <*> mx = ExprM $ \interp name -> runExprM mf interp name <*> runExprM mx interp name

instance Monad f => Monad (ExprM exprF val f) where
  return = pure
  m >>= k = ExprM $ \interp name -> runExprM m interp name >>= \x ->
    runExprM (k x) interp name

-- | Evaluate an expression into the interpreter context.
evalExprM :: (forall x . edsl (Expr edsl val f) x -> f (val x))
          -> (forall x . val x -> f (val x))
          -> ExprM edsl val f t
          -> f t
evalExprM interp name expr = runExprM expr interp name

-- | Use an interpreter-specific thing in the expression.
--
-- It's called "special" because it fixes the `f` types (and probably `val` as
-- well).
special :: f t -> ExprM edsl val f t
special m = ExprM $ \_ _ -> m

-- | Use a "value" with no interpreter context as an expression.
knownValue :: Applicative f => val t -> Expr edsl val f t
knownValue v = Expr $ special (pure v)

-- | Use a base EDSL term in the expression, yielding a value (in `val`) within
-- the interpreter context (`f`).
--
-- TODO better name? `edsl`? Simply `expr`?
exprF :: forall edsl f val t . edsl (Expr edsl val f) t -> Expr edsl val f t
exprF = Expr . exprM

exprM :: forall edsl f val t . edsl (Expr edsl val f) t -> ExprM edsl val f (val t)
exprM exprf = ExprM $ \interp _ -> interp exprf

expr :: Expr edsl val f t -> ExprM edsl val f (val t)
expr = runExpr

name :: Monad f => Expr edsl val f t -> ExprM edsl val f (val t)
name exp = ExprM $ \interp name -> runExprM (runExpr exp) interp name >>= name

subst :: Applicative f => val t -> Expr edsl val f t
subst = knownValue

-- | Names the expression and gives a reference to it.
bind :: Monad f => Expr edsl val f t -> ExprM edsl val f (Expr edsl val f t)
bind = fmap subst . name

-- | Variant on name/subst/bind that uses a continuation instead of monadic
-- bind.
local :: ( Monad f )
      => Expr edsl val f t
      -> (Expr edsl val f t -> Expr edsl val f r)
      -> Expr edsl val f r
local e k = Expr $ do
  e' <- bind e
  expr (k e')
