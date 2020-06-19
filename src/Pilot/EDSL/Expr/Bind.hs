{-|
Module      : Pilot.EDSL.Expr.Bind
Description : Import for rebindable syntax on do notation.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

This module exports what you need in order to overloade do notation (using
RebindableSyntax) so that it gives binding/naming in an EDSL expression.

Using (>>) would be really stupid but it has to be there, because this is 100%
an abuse of a feature.
-}

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}

module Pilot.EDSL.Expr.Bind
  ( module Expr
  , (>>=)
  , (>>)
  ) where

import Prelude (const)
import qualified Prelude
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))

import Pilot.EDSL.Expr as Expr

-- | This closed type family allows GHC to figure out which Bind instance to
-- use. Anything which takes a Hask argument we shall assume to be a standard
-- monad. Anything else is called "goofy" and may have a different kind of
-- bind type.
--
-- In order for an overloaded do notation on a goofy kind to work, GHC needs
-- to actually know what that `domain` kind is. But when writing EDSL
-- expressions, the programmer certainly _will_ know this, so it's all good.
type family FStyle (f :: domain -> Hask) :: Style where
  FStyle (f :: Hask   -> Hask) = Standard
  FStyle (f :: domain -> Hask) = Goofy

data Style where
  Standard :: Style
  Goofy    :: Style

{-
class Map (style :: Style) (f :: k -> Hask) where
  type Arrow style f s t :: Hask
  map :: forall s t . Arrow style f s t -> f s -> f t
-}

class Bind (style :: Style) (f :: k -> Hask) where
  type Inner     style f (s :: k) :: Hask
  bind :: forall proxy s t .
          proxy style
       -> f s
       -> (Inner style f s -> f t)
       -> f t

instance Prelude.Monad f => Bind Standard f where
  type Inner     Standard f x = x
  bind _ m k = m Prelude.>>= k

instance Bind Goofy (Expr edsl f) where
  type Inner     Goofy (Expr edsl f) x = Expr edsl f x
  bind _ = Expr.local

(>>=) :: forall f s t .
         (Bind (FStyle f) f)
      => f s
      -> (Inner (FStyle f) f s -> f t)
      -> f t
(>>=) fs k = bind (Proxy :: Proxy (FStyle f)) fs k

(>>) :: (Bind (FStyle f) f) => f s -> f t ->  f t
(>>) a b = a >>= const b
