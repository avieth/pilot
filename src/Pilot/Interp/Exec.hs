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

-- | This is a monad transformer within which some formal thing `form` can be
-- made into `val`ues within some context `f`.
--
-- This is the glue between formal expressions (see 'Pilot.EDSL.Expr.Expr')
-- and interpreter-specific values. The latter may be constructed within this
-- monad (in general this will require ordering) and then used within the
-- former (which probably does not want any imposed ordering on terms).
--
newtype Exec (form :: (domain -> Hask) -> domain -> Hask)
             (val :: domain -> Hask)
             (f :: Hask -> Hask)
             (t :: Hask) =
  Exec { runExec :: (forall x . form val x -> f (val x)) -> f t }

instance Functor f => Functor (Exec form val f) where
  fmap f e = Exec $ \interp -> fmap f (runExec e interp)

instance Applicative f => Applicative (Exec form val f) where
  pure x = Exec $ \_ -> pure x
  ef <*> ex = Exec $ \interp -> runExec ef interp <*> runExec ex interp

instance Monad f => Monad (Exec form val f) where
  return = pure
  ex >>= k = Exec $ \interp -> runExec ex interp >>= \x -> runExec (k x) interp

expr :: form val t -> Exec form val f (val t)
expr e = Exec $ \interp -> interp e

impl :: f t -> Exec form val f t
impl x = Exec $ const x
