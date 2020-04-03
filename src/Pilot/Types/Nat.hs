{-|
Module      : Pilot.Types.Nat
Description : Typical inductive Nat type.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Pilot.Types.Nat where

data Nat where
  S :: Nat -> Nat
  Z :: Nat

type family Plus (n :: Nat) (m :: Nat) :: Nat where
  Plus n Z = n
  Plus Z m = m
  Plus (S n) m = S (Plus n m)

type family Minus (n :: Nat) (m :: Nat) :: Nat where
  Minus n Z = n
  Minus (S n) (S m) = Minus n m

type family Min (n :: Nat) (m :: Nat) :: Nat where
  Min n      Z    = Z 
  Min Z      n    = Z
  Min (S n) (S m) = S (Min n m)

type family Minimum (ns :: [Nat]) :: Nat where
  Minimum (n ': ns) = Min n (Minimum ns)

data Index (n :: Nat) where
  Here  :: Index (S n)
  There :: Index n -> Index (S n)
