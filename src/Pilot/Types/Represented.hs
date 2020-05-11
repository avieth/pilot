{-|
Module      : Pilot.Types.Represented
Description : Type family for represented kinds.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Pilot.Types.Represented
  ( Represented (..)
  ) where

import qualified Data.Kind as Haskell (Type)
import Data.Functor.Identity (Identity)

-- | A kind is "represented" if there is a GADT parameterized on it giving its
-- singleton type. For example
--
-- > data BoolRep (b :: Bool) where
-- >   True_t  :: BoolRep 'True
-- >   False_t :: BoolRep 'False
--
-- There is in theory one and only one such representation for any given type,
-- so a class/type family definition like this makes sense.
class Represented (k :: Haskell.Type) where
  type Rep k :: k -> Haskell.Type

instance Represented Haskell.Type where
  type Rep Haskell.Type = Identity