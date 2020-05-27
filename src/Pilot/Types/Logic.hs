{-|
Module      : Pilot.Types.Logic
Description : The Any and All types
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
{-# LANGUAGE BangPatterns #-}

module Pilot.Types.Logic where

import qualified Data.Kind as Haskell (Type)

data All (f :: k -> Haskell.Type) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

allToList :: (forall t . f t -> r) -> All f ts -> [r]
allToList f All        = []
allToList f (And x xs) = f x : allToList f xs

mapAll :: (forall t . f t -> g t) -> All f ts -> All g ts
mapAll _ All = All
mapAll h (And t as) = And (h t) (mapAll h as)

traverseAll :: Applicative m => (forall t . f t -> m (g t)) -> All f ts -> m (All g ts)
traverseAll _ All = pure All
traverseAll h (And t ts) = And <$> h t <*> traverseAll h ts

zipAll
  :: (forall x . f x -> g x -> h x)
  -> All f ts
  -> All g ts
  -> All h ts
zipAll _ All All = All
zipAll f (And fx fs) (And gx gs) = And (f fx gx) (zipAll f fs gs)

anyOfAll :: (forall t . f t -> Bool) -> All f ts -> Bool
anyOfAll _ All = False
anyOfAll p (And t ts) = p t || anyOfAll p ts

data Any (f :: k -> Haskell.Type) (ts :: [k]) (r :: k) where
  Any :: f t -> Any f (t ': ts) t
  Or  :: Any f ts r -> Any f (t ': ts) r

anyToOne :: forall f ts x r . (forall t . Integer -> f t -> r) -> Any f ts x -> r
anyToOne f xs = go 0 f xs
  where
  go :: forall ts . Integer -> (forall t . Integer -> f t -> r) -> Any f ts x -> r
  go !n f (Any x) = f n x
  go !n f (Or xs) = go (n+1) f xs

mapAny :: (forall t . f t -> g t) -> Any f ts r -> Any g ts r
mapAny h (Any t) = Any (h t)
mapAny h (Or as) = Or (mapAny h as)

traverseAny :: Functor m => (forall t . f t -> m (g t)) -> Any f ts r -> m (Any g ts r)
traverseAny h (Any t) = Any <$> h t
traverseAny h (Or as) = Or <$> traverseAny h as

-- | For each of the conjuncts, pick out that conjunct in a disjunction.
forAll
  :: forall f g ts .
     (forall x . f x -> g x)
  -> All f ts
  -> All (Any g ts) ts
forAll h alls = go alls id
  where
  go :: forall ts' .
        All f ts'
     -> (forall r . Any g ts' r -> Any g ts r)
     -> All (Any g ts) ts'
  go All        _ = All
  go (And t ts) k = And (k (Any (h t))) (go ts (\a -> k (Or a)))
