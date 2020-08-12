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

module Language.Pilot.Types
  ( Hask
  , Form_k
  , Repr_k
  , module Nat
  , module Rep
  ) where

import Data.Kind as Haskell (Type)

import Language.Pilot.Types.Nat as Nat
import Language.Pilot.Types.Represented as Rep

type Hask = Haskell.Type

type Form_k (domain :: Hask) = (domain -> Hask) -> domain -> Hask

type Repr_k (domain :: Hask) = domain -> Hask
