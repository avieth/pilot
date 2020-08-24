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

module Language.Pilot.Types.Logic
  ( Any (..)
  , All (..)
  ) where

import Data.Kind (Type)

data Any (f :: k -> Type) (ts :: [k]) where
  Any :: f t -> Any f (t ': ts)
  Or  :: Any f ts -> Any f (t ': ts)

data All (f :: k -> Type) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

