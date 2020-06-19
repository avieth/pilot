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
  , Expr (..)

  , form
  , edsl
  , value
  , local

  , evalExpr

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
type EDSL domain = (domain -> Hask) -> domain -> Hask

data Term (edsl :: EDSL domain) (val :: domain -> Hask) (ast :: domain -> Hask) (t :: domain) where
  Form  :: edsl ast t                     -> Term edsl val ast t
  Value :: val      t                     -> Term edsl val ast t
  Named ::      ast s -> (ast s -> ast t) -> Term edsl val ast t

-- | Fix point over Term on given edsl and val types.
newtype Expr (edsl :: EDSL domain) (val :: domain -> Hask) (t :: domain) = Expr
  { runExpr :: Term edsl val (Expr edsl val) t }

-- | Evaluate an expression into the interpreter context.
--
-- TODO not sure if this is at all close to ideal. Should use recursion schemes
-- instead no?
evalExpr
  :: (edsl (Expr edsl val) t -> r)
  -> (val                  t -> r)
  -> (forall x . Expr edsl val x -> (Expr edsl val x -> Expr edsl val t) -> r)
  -> Expr edsl val t
  -> r
evalExpr fform fval fnamed (Expr term) = case term of
  Form  x   -> fform  x
  Value x   -> fval   x
  Named x k -> fnamed x k

-- | Use a base EDSL term in the expression.
form :: edsl (Expr edsl val) t -> Expr edsl val t
form = Expr . Form

-- | Alias of 'form'.
edsl :: edsl (Expr edsl val) t -> Expr edsl val t
edsl = form

-- | Use an interpreter-value thing in the expression.
value :: val t -> Expr edsl val t
value = Expr . Value

-- | Like let binding but non-recursive.
local :: Expr edsl f t
      -> (Expr edsl f t -> Expr edsl f r)
      -> Expr edsl f r
local e k = Expr $ Named e k
