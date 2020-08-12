{-|
Module      : Language.Pilot.Expr
Description : Definition of the EDSL expression type.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Expr
  ( Expr (..)
  , Interp
  , formal
  , abstract
  , concrete
  , runExpr
  ) where

import Language.Pilot.Types

-- | An EDSL expression relates a form, a representation, and a domain-specific
-- type. The type `form repr` is assumed to contain implementations of the
-- formal constructions in `repr`. Thus the entire expression is predicated on
-- an implemetation in this representation.
--
-- TODO it's not clear whether there are any advantages/disadvantages between
-- this and the style in which the form is a GADT with constructors for each
-- EDSL form, and we would have
--
--   getExpr :: (forall x . form repr x -> repr x) -> repr t
--
newtype Expr (form :: Form_k domain) (repr :: Repr_k domain) (t :: domain) = Expr
  { getExpr :: Interp form repr -> repr t }

type Interp (form :: Form_k domain) (repr :: Repr_k domain) =
  forall x . form repr x -> repr x

runExpr :: Interp form repr -> Expr form repr t -> repr t
runExpr i e = getExpr e i

-- | Use a formal construction.
formal :: ((forall x . Expr form repr x -> repr x) -> (forall x . repr x -> Expr form repr x) -> form repr t)
       -> Expr form repr t
formal k = Expr $ \interp -> interp (k (\e -> getExpr e interp) (\r -> concrete r))


-- | Synonym for 'formal'
abstract :: ((forall x . Expr form repr x -> repr x) -> (forall x . repr x -> Expr form repr x) -> form repr t)
         -> Expr form repr t
abstract = formal

-- | Use an implementation/representation specific construction.
concrete :: repr t -> Expr form repr t
concrete it = Expr $ \_ -> it
