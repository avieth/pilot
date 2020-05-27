{-|
Module      : Pilot.EDSL.Expr
Description : 
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
  , value
  , known
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
newtype Fix edsl t = Fix { getFix :: edsl (Fix edsl) t }

-- Why don't we use `Fix edsl` as our expression language?
-- In short: we want to represent what we know about the _interpreter_ in the
-- type of the expression. Usually this will be universally quantified, i.e.
-- we know/assume nothing about it (except maybe that it's a monad), and we get
-- what is essentially `Fix edsl`.
--
-- 1. The notion of "identity" and of "bindings" within the EDSL.
--    This is kind of like HOAS. We want to use the meta-language binding
--    semantics to do bindings in the object-language.
--    Here we let the interpreter decide what that should mean, by taking a
--
--      forall x . val x -> f (val x)
--
--    parameter. What the EDSL programmer will probably deal in is
--
--      bind :: Monad f => Expr edsl val f t -> ExprM edsl val f (Expr edsl val f t)
--
--    Given that `forall val f . Monad f => Expr edsl val f t` is the type of
--    an expression in the EDSL _without_ naming/binding, this seems to make
--    good sense: `bind` gives you another one that can go wherever that one
--    went.
--
--    TODO elaborate
--
-- 2. Being able to "mix-in" features peculiar to an interpreter. The flagship
--    case study of this is copilot's `extern` function, which takes an optional
--    list of Haskell values to serve as simulation data. This is woefully
--    inadequate, because simulation data is not often useful if it cannot
--    depend upon streams in the EDSL. A better approach is say that `extern`
--    is not a part of the EDSL at all! Rather, it's a feature peculiar to the
--    C99 interpreter / code generator.
--    We would have "pure expressions" which are free in the interpreter type
--    parameter, and then expressions like `extern` or `lazyList` which would
--    pick out the interpreter type, allowing the programmer to defer the
--    choice to the boundary of the program.
--
--
--    Memory streams, and _only_ memory streams, may be defined
--    mutually-recursively. How do we allow for this? Making this a MonadFix
--    would be too much, because then we could generate nonsense C with
--    undefined references. The reason it works, in C, for memory streams, is
--    that their names are static.
--    Now _that_ strikes me as something that should be built-in to the stream
--    EDSL itself. Any stream with nonzero prefix index may be used lazily...
--    For this, we would need that it's possible, even in the typical `Fix` of
--    the stream EDSL, to define mutually-recursive memory streams. Seems we
--    would need plenty of CPS...
--
--      Rep a t -> NatRep ('S n) -> Vec ('S n) (expr ('Constant t))
--      ->
--        -- This continuation gets the prefix-only part of the stream and
--        -- must use it to define the rest of the stream...
--         (expr ('Stream n t) -> expr ('Stream 'Z t))
--      -> ExprF pexpr expr ('Stream ('S n) t)
--
--    The problem seems to be that in order for a fix or monad fix style thing
--    to work, a product type is necessary, but we don't have nor want that
--    in the stream type domain. Would a Haskell tuple work at all?
--
--      Fix :: (expr ('Stream n t) -> (expr r, expr ('Stream ('S n) t))) -> ExprF pexpr expr r
--
--    No, because then the `r` and the `Stream` values cannot be computed in
--    the same expr context.
--
--    Is it not enough to do the original idea, in which the memory stream
--    continuation to define its value gets a reference to the stream itself?


-- | This is a monad over a given EDSL which includes a notion of
-- naming/binding.
--
-- An `ExprM edsl val f t` which is free in `val` and and monad `f` is
-- essentially just the recursive EDSL with naming and substitution.
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

{-
-- Actually we do not want MonadFix. Not every EDSL would want to allow for
-- recursion / laziness.
instance MonadFix f => MonadFix (ExprM exprF val f) where
  mfix f = ExprM $ \interp -> mfix (\a -> runExprM (f a) interp)
-}

-- | Evaluate an expression into the interpreter context.
evalExprM :: (forall x . edsl (Expr edsl val f) x -> f (val x))
          -> (forall x . val x -> f (val x))
          -> ExprM edsl val f t
          -> f t
evalExprM interp name expr = runExprM expr interp name

-- | TODO better name
value :: Applicative f => val t -> Expr edsl val f t
value v = known (pure v)

known :: f (val t) -> Expr edsl val f t
known m = Expr $ ExprM $ \_ _ -> m

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
subst = value

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
