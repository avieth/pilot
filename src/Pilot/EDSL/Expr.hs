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
  ( Expr (..)
  , exprF
  , exprF_
  , known
  , value
  , evalExpr
  ) where

import qualified Data.Kind as Haskell (Type)

-- | Represents an expression in some EDSL (represented by `exprF`), interpreted
-- into some backend (represented by `f` and `val`).
--
-- It must be a monad, with the ST binding type parameter trick. Any pure
-- Haskell computation can be used in this monad of course, and the result is
-- something in the parameter f.
--
-- Intuitively, this type means that, if you know how to elaborate ExprF inside
-- f, then you can get an expression inside f. That's to say, whatever this is,
-- it's built atop ExprF and pure meta-language (Haskell) constructs.
--
-- Idea: to make it a monad, just add an STRef analog, call it Val?
-- ExprF recursive parts can take
--
--   f s (Val s t) -> ...
--
-- then what we want in the continuation in Expr is
--
--   forall x y . ExprF f x y -> f x (Val x y)
--
-- ah but damn, Val actually depends upon f, as you might expect, since this is
-- essentially the representation of the expression.
-- One nice option could be to take 2 params: the monad and the STRef/val type.
--
--   (forall x y . ExprF f val x y -> f val x (val x y)) -> f val s t
--
-- and even beyond that, we still don't want to incur any constraints on f
-- until evaluation time, so we need some sort of free structure over it.
--
-- f represents the interpretation. Think of it as code generation or something.
-- s represents the binding context. It's the ST-style parameter used to ensure
-- that what you do in one Expr cannot come out of that context.
-- val represents object-language values, parameterized by the binding context.
-- t is what you expect; this is a functor.
--
newtype Expr exprF (f :: domain -> Haskell.Type) (t :: domain) = Expr
  { getExpr :: (forall x . exprF f x -> f x) -> f t }

-- | Put an existing value into an expression.
--
-- Compare with the continuation which appears in the parameter of 'exprF'.
known :: f t -> Expr exprF f t
known value = Expr $ \_ -> value

-- | Synonym for 'known' that in some cases is a more suggestive choice of name.
value :: f t -> Expr exprF f t
value = known

evalExpr :: (forall x . exprF f x -> f x) -> Expr exprF f t -> f t
evalExpr interpExpr expr = getExpr expr interpExpr

exprF :: forall exprF f t . ((forall x . Expr exprF f x -> f x) -> exprF f t)
      -> Expr exprF f t
exprF k = Expr $ \interp ->
  let run :: forall y . Expr exprF f y -> f y
      run expr = getExpr expr interp
  in  interp (k run)

exprF_ :: forall exprF f t . exprF f t -> Expr exprF f t
exprF_ exprf = Expr $ \interp -> interp exprf
