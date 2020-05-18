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
  , value
  , valueF
  , evalInMonad
  , Static (..)
  ) where

import qualified Control.Monad as Monad (join)
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
-- TODO define this in its own module.
newtype Expr
  (exprF) -- Kind is too long to write.
  (f   :: Haskell.Type -> Haskell.Type -> Haskell.Type)
  (val :: Haskell.Type -> domain -> Haskell.Type)
  (s   :: Haskell.Type)
  (t   :: domain) = Expr
  { getExpr :: (forall x y . exprF f val x y -> f x (val x y))
            -- ^ Interpret expressions
            -> (forall x y z . (y -> z) -> f x y -> f x z)
            -- ^ fmap
            -> (forall x y . y -> f x y)
            -- ^ pure
            -> (forall x y . f x (f x y) -> f x y)
            -- ^ join
            -> f s (val s t)
  }

newtype Static (f :: Haskell.Type -> k -> Haskell.Type) (t :: k) = Static
  { getStatic :: forall x . f x t }

-- | Put an existing value into an expression. Note the `s` parameter, which
-- ensures the value came from within the same expression context, for instance
-- from a `local` binding.
value :: val s t -> Expr exprF f val s t
value v = Expr $ \_interp _map pure' _join -> pure' v

valueF :: f s (val s t) -> Expr exprF f val s t
valueF v = Expr $ \_ _ _ _ -> v

-- TODO TBD whether we actually would want Expr to be a
-- functor/applicative/monad. I don't think it's useful at all.

{-
instance Functor (Expr f val s) where
  fmap f expr = Expr $ \interp' map' pure' join' ->
    map' f (getExpr expr interp' map' pure' join')

instance Applicative (Expr f val s) where
  pure x = Expr $ \_interp _map pure' _join -> pure' x
  (<*>)  = Monad.ap

instance Monad (Expr f val s) where
  return = pure
  expr >>= f = Expr $ \interp' map' pure' join' ->
    join' (map' (\x -> getExpr (f x) interp' map' pure' join') (getExpr expr interp' map' pure' join'))
-}

evalInMonad
  :: forall exprF f val s t.
     ( forall q . Monad (f q) )
  -- TODO use the ST trick later. Not in because I want flexibility for development
  -- => (forall q . Expr f val q t)
  => Expr exprF f val s t
  -> (forall x y . exprF f val x y -> f x (val x y))
  -> f s (val s t)
evalInMonad expr interp = getExpr expr interp fmap pure Monad.join

-- | NB: no constraints appear. A Monad instance is not needed until evaluation
-- time ('evalInMonad') which is nice; `f` and `val` remain truly unconstrained.
exprF :: forall exprF f val s t . exprF f val s t -> Expr exprF f val s t
exprF exprf = Expr $ \f map' pure' join' ->
  let v :: f s (val s t)
      v = f exprf
  in  join' (map' pure' v)
