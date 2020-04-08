{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.EDSL.Streamwise where

import Pilot.Types.Nat
import Pilot.Types.Point (type (:->), type T)
import qualified Pilot.Types.Point as Pilot
import Pilot.EDSL.Pointwise

-- | Streamwise expressions: applicative over Pointwise on a given `point`,
-- `op`, and `target`, with "hold" and "drop" expressions to add/remove known
-- points from the head of a stream.
--
-- This is essentially a `stream target n t` value but abstracted over the
-- 4 combinators:
-- - hold
-- - drop
-- - constant (applicative pure)
-- - ap (applicative <*>)
newtype Streamwise point op target stream n t = Streamwise
  { runStreamwise :: (forall n r . Pointwise point op target r -> stream target n r -> stream target (S n) r)
                  -- ^ Hold a point: put it in front of a stream, effectively
                  -- making the rest of the stream appear to be later.
                  -> (forall n r . stream target (S n) r -> stream target n r)
                  -- ^ Drop a point from a stream, undoing a hold.
                  -> (forall r . Pointwise point op target r -> stream target Z r)
                  -- ^ Make a constant stream from a point.
                  -> (forall m n s t . stream target m (s :-> t) -> stream target n s -> stream target (Min m n) t)
                  -- ^ Apply a function-valued stream to another.
                  -> stream target n t
  }

hold :: Pointwise  point op target              t
     -> Streamwise point op target stream    n  t
     -> Streamwise point op target stream (S n) t
hold pw st = Streamwise $ \ehold edrop epure eap ->
  ehold pw (runStreamwise st ehold edrop epure eap)

next :: Streamwise point op target stream (S n) t
     -> Streamwise point op target stream    n  t
next st = Streamwise $ \ehold edrop epure eap ->
  edrop (runStreamwise st ehold edrop epure eap)

constant :: Pointwise  point op target          t
         -> Streamwise point op target stream Z t
constant pt = Streamwise $ \_ _ epure _ -> epure pt

ap :: Streamwise point op target stream m         (s :-> t)
   -> Streamwise point op target stream n         s
   -> Streamwise point op target stream (Min m n) t
ap stf stx = Streamwise $ \ehold edrop epure eap ->
  eap (runStreamwise stf ehold edrop epure eap)
      (runStreamwise stx ehold edrop epure eap)

fix :: (Streamwise point op target stream n t -> Streamwise point op target stream n t)
    -> Streamwise point op target stream n t
fix k = Streamwise $ \ehold edrop epure eap ->
  let result = runStreamwise (k streamwise) ehold edrop epure eap
      streamwise = Streamwise $ \_ _ _ _ -> result
  in  result

slet :: Streamwise point op target stream n s
     -> (Streamwise point op target stream n s -> Streamwise point op target stream m t)
     -> Streamwise point op target stream m t
slet s k = Streamwise $ \ehold edrop epure eap ->
  let seval = runStreamwise s ehold edrop epure eap
  in  runStreamwise (k (Streamwise $ \_ _ _ _ -> seval)) ehold edrop epure eap
