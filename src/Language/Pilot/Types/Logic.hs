{-|
Module      : Language.Pilot.Types.Logic
Description : Any and All GADTs
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Types.Logic
  ( Some (..)
  , All (..)
  , forAll
  , forAll2
  , allToList
  , allToNonEmpty
  , Not
  , Decision (..)
  ) where

import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import Language.Pilot.Types.Represented

type Not t = forall x . t -> x

data Decision (f :: Type) where
  Yes ::     f -> Decision f
  No  :: Not f -> Decision f

data Some (f :: k -> Type) (ts :: [k]) where
  Some :: f t -> Some f (t ': ts)
  Or   :: Some f ts -> Some f (t ': ts)

data All (f :: k -> Type) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

forAll :: (forall x . f x -> g x) -> All f ts -> All g ts
forAll k All          = All
forAll k (And t alls) = And (k t) (forAll k alls)

forAll2 :: (forall x . f x -> g x -> h x) -> All f ts -> All g ts -> All h ts
forAll2 k All All = All
forAll2 k (And t alls) (And t' alls') = And (k t t') (forAll2 k alls alls')

allToList :: (forall x . f x -> r) -> All f ts -> [r]
allToList k All = []
allToList k (And x all) = k x : allToList k all

allToNonEmpty :: (forall x . f x -> r) -> All f (t ': ts) -> NonEmpty r
allToNonEmpty k (And x All)         = k x NE.:| []
allToNonEmpty k (And x r@(And _ _)) = NE.cons (k x) (allToNonEmpty k r)

instance TestEquality k => TestEquality (All k) where
  testEquality All All = Just Refl
  testEquality (And l ls) (And r rs) = case testEquality l r of
    Nothing -> Nothing
    Just Refl -> case testEquality ls rs of
      Nothing -> Nothing
      Just Refl -> Just Refl
  testEquality (And _ _) All = Nothing
  testEquality All (And _ _) = Nothing
