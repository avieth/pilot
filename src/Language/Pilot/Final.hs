{-|
Module      : Language.Pilot.Final
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Pilot.Final
  ( Interprets (..)
  , formal
  , fromExpr
  ) where

import Language.Pilot.Expr (Expr, getExpr)
import Language.Pilot.Types

class Interprets (repr :: Repr_k domain) (form :: Form_k domain) where
  interp :: Interp form repr

formal :: ( Interprets repr form ) => form repr t -> repr t
formal it = interp it

fromExpr :: ( Interprets repr form ) => Expr form repr t -> repr t
fromExpr it = getExpr it interp
