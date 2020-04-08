{-|
Module      : Pilot.Types.Args
Description : GADT for an argument list for use in the pointwise EDSL.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Pilot.Types.Args
  ( Args (..)
  , mapArgs
  ) where

import qualified Data.Kind as Kind (Type)
import qualified Pilot.Types.Point as Pilot

-- | An argument list of non-function values ('Pilot.Types.Point.Kind.T') in
-- some target. This is used in the 'Pointwise' EDSL to express fully-saturated
-- domain-specific operations.
data Args (target :: Pilot.Kind ty -> Kind.Type) (args :: [ty]) where
  ArgNone :: Args target '[]
  ArgMore :: target (Pilot.T arg) -> Args target args -> Args target (arg ': args)

mapArgs :: (forall t . target t -> target' t) -> Args target args -> Args target' args
mapArgs _   ArgNone          = ArgNone
mapArgs nat (ArgMore f args) = ArgMore (nat f) (mapArgs nat args)
