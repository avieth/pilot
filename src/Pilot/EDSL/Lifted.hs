{-|
Module      : Pilot.EDSL.Lifted
Description : A way to "lift" an ESDL domain in Hask (Haskell types).
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Pilot.EDSL.Lifted
  ( Embed (..)
  , Lifted (..)
  , lift
  , lift1
  , unlift
  ) where

import Pilot.EDSL.Expr (Hask, Expr)
import Pilot.Types.Represented

-- | Gives a representation in `domain` for a Haskell type.
--
-- By way of this class, an EDSL domain can be endowed with a kind of
-- "open world" of user-defined nominal types. The programmer may define
-- two different nominal Haskell types which have the same type in the given
-- EDSL domain, but which, in the "lifted" expression and value semantics, are
-- not the same type.
class ( Represented domain ) => Embed (domain :: Hask) (t :: Hask) where
  type EmbedT domain t :: domain
  embedT :: proxy domain -> proxy t -> Rep domain (EmbedT domain t)

data Lifted (f :: domain -> Hask) (t :: Hask) where
  Lifted :: f (EmbedT domain t) -> Lifted f t

lift :: f (EmbedT domain t) -> Lifted f t
lift = Lifted

unlift :: Lifted f t -> f (EmbedT domain t)
unlift (Lifted f) = f

lift1 :: (a (EmbedT domain x) -> b (EmbedT domain y))
      -> (Lifted a x -> Lifted b y)
lift1 f = lift . f . unlift

liftExpr :: Expr edsl f (EmbedT domain t) -> Lifted (Expr edsl f) t
liftExpr = lift

unliftExpr :: Lifted (Expr edsl f) t -> Expr edsl f (EmbedT domain t)
unliftExpr = unlift
