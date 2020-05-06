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
  { runStreamwise :: ( forall n r .
                          Vec (S n) (point r)
                       -> (stream target n (T r) -> stream target Z (T r))
                       -> stream target (S n) (T r)
                     )
                  -- ^ Hold 1 or more points in front a stream, effectively
                  -- making the rest of the stream appear to be later. You
                  -- cannot hold a function, only a value. This is the only way
                  -- in which a stream may be defined self-referentially: the
                  -- rest of the stream is determined by the result of the
                  -- continuation, which may lazily use that very stream but
                  -- with one fewer prefix (so you can drop all but the last
                  -- known value if you wish). The points given must be literals
                  -- rather than any pointwise computation.
                  -> (forall n r . stream target (S n) r -> stream target n r)
                  -- ^ Drop a point from a stream which has a known point held
                  -- in front of it. This is the way in which a stream created
                  -- by hold can be "moved forward" in time, giving access to
                  -- the more recent values.
                  -> (forall r . Pointwise point op target r -> stream target Z r)
                  -- ^ Make a constant stream from a point. This may be a value
                  -- or a function
                  -> (forall m n s t . stream target m (s :-> t) -> stream target n s -> stream target (Min m n) t)
                  -- ^ Apply a function-valued stream to another.
                  -> (forall m n q r . stream target m (T q) -> (stream target m (T q) -> stream target n r) -> stream target n r)
                  -- ^ Streamwise let bindings
                  -> stream target n t
  }

hold :: Vec (S n) (point t)
     -> (Streamwise point op target stream n (T t) -> Streamwise point op target stream Z (T t))
     -> Streamwise point op target stream (S n) (T t)
hold ps k = Streamwise $ \ehold edrop epure eap elet -> ehold ps $ \stream ->
  runStreamwise (k (Streamwise $ \_ _ _ _ _ -> stream)) ehold edrop epure eap elet

next :: Streamwise point op target stream (S n) t
     -> Streamwise point op target stream    n  t
next st = Streamwise $ \ehold edrop epure eap elet ->
  edrop (runStreamwise st ehold edrop epure eap elet)

constant :: Pointwise  point op target          t
         -> Streamwise point op target stream Z t
constant pt = Streamwise $ \_ _ epure _ _ -> epure pt

ap :: Streamwise point op target stream m         (s :-> t)
   -> Streamwise point op target stream n         s
   -> Streamwise point op target stream (Min m n) t
ap stf stx = Streamwise $ \ehold edrop epure eap elet ->
  eap (runStreamwise stf ehold edrop epure eap elet)
      (runStreamwise stx ehold edrop epure eap elet)

-- Not sure whether fix and slet are needed anymore.
-- If they are, shouldn't slet be just like the pointwise let/local?
-- Aha, fix should certainly not be here, because the only self-referential
-- construction is `hold`. As for slet, yes we may want to demand a
-- stream-target let construct just like for pointwise.
-- Also NB: no fix for pointwise; pointwise expressions must not be recursive
-- or self-referential.
slet :: Streamwise point op target stream n (T q)
     -> (Streamwise point op target stream n (T q) -> Streamwise point op target stream m (T r))
     -> Streamwise point op target stream m (T r)
slet q k = Streamwise $ \ehold edrop epure eap elet ->
  elet (runStreamwise q ehold edrop epure eap elet) $ \q' ->
    runStreamwise (k (Streamwise $ \_ _ _ _ _ -> q')) ehold edrop epure eap elet
