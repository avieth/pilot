{-|
Module      : Pilot.Interp.Exec
Description : Definition of the Exec monad for interpreting expressions.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Pilot.Interp.Exec
  ( Exec (..)
  , expr
  , impl
  ) where

import Pilot.EDSL.Expr

-- | Within the 'Exec' monad, interpreter-specific things may be introduced and
-- then used within 'Expr's, by way of the `val` type parameter, which serves
-- as the glue between the 'Exec' and the 'Expr'.
--
-- If 'Expr' corresponds to Haskell values, 'Exec' corresponds to an RTS which
-- runs IOs built from 'Expr's.
--
-- Expressions may use values from a given interpretation, and those special
-- values come about within an execution context, which is represented by
-- this type Exec.
newtype Exec (edsl :: EDSL domain) (val :: domain -> Hask) (f :: Hask -> Hask) (t :: Hask) = Exec
  { runExec :: (forall x . Expr edsl val x -> f (val x)) -> f t }

instance Functor f => Functor (Exec edsl val f) where
  fmap f e = Exec $ \interp -> fmap f (runExec e interp)

instance Applicative f => Applicative (Exec edsl val f) where
  pure x = Exec $ \_ -> pure x
  ef <*> ex = Exec $ \interp -> runExec ef interp <*> runExec ex interp

instance Monad f => Monad (Exec edsl val f) where
  return = pure
  ex >>= k = Exec $ \interp -> runExec ex interp >>= \x -> runExec (k x) interp

expr :: Expr edsl val t -> Exec edsl val f (val t)
expr e = Exec $ \interp -> interp e

impl :: f t -> Exec edsl val f t
impl x = Exec $ const x
