{-|
Module      : Pilot.Types
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Types
  ( Hask
  , Form_k
  , Repr_k
  , Interp
  , module Nat
  , module Rep
  , module Logic
  ) where

import Data.Kind as Haskell (Type)

import Language.Pilot.Types.Logic as Logic
import Language.Pilot.Types.Nat as Nat
import Language.Pilot.Types.Represented as Rep

type Hask = Haskell.Type

type Form_k (domain :: Hask) = (domain -> Hask) -> domain -> Hask

type Repr_k (domain :: Hask) = domain -> Hask

type Interp (form :: Form_k domain) (repr :: Repr_k domain) =
  forall x . form repr x -> repr x
