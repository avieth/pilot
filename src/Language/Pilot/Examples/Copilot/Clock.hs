{-|
Module      : Language.Pilot.Examples.Copilot.Clock
Description : Clocks in the style of the copilot library
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Language.Pilot.Examples.Copilot.Clock where

import qualified Prelude
import qualified Data.Word as Haskell
import Language.Pilot

type Phase = Haskell.Word8
type Period = Haskell.Word8

type Clock = Obj (Varying 'Z Bool)

-- | A clock's period is exactly what you think: it repeats after this many
-- steps.
--
-- A clock's phase determines when the "true" or "high" signal comes up. It is
-- taken modulo the period. 0 means the first frame of the period is high.
--
-- If the period is 0, you get constant high.
--
-- How does it work? Create a single-cell memory stream which contains the
-- number of ticks since the last high signal (always less than the period).
--
-- NB: the phase and period are not in the object-language. This defines a
-- family of different object-language clocks, indexed in the meta-language
-- by phase and period.
clock :: Phase -> Period -> E f val (Obj (Program Clock))
clock phase period = if period Prelude.== 0
  then prog_pure auto <@> (constant_auto Zero <@> true)
  else clockPeriodLessOne phase (period Prelude.- 1)

-- | Called with the period minus 1.
--
-- A memory stream (knot) is expressed using the period, and then this stream
-- is transformed into a Varying Z Bool by testing equality on the phase
-- (corrected to be modulo the period + 1)
clockPeriodLessOne :: forall f val . Phase -> Period -> E f val (Obj (Program Clock))
clockPeriodLessOne phase periodLessOne =
  prog_map auto auto <@> (map_auto Zero <@> atPhase) <@> (counter <@> u8 truePeriod)
  where
  atPhase :: E f val (Obj (Constant UInt8) :-> Obj (Constant Bool))
  atPhase = fun $ \count -> count == u8 truePhase
  truePeriod = periodLessOne Prelude.+ 1
  truePhase = phase `Prelude.mod` truePeriod

-- | Uses the 'clockStep' to make a counter. Its value is the number of ticks
-- since the start of the last period. It assumes the period is nonzero.
counter :: forall f val . E f val (Obj (Constant UInt8) :-> Obj (Program (Obj (Varying 'Z UInt8))))
counter = fun $ \period ->
  let recdef = fun $ \prev -> map_auto Zero <@> (clockStep <@> period) <@> prev
  in  prog_map auto auto <@> shift_auto <@> (knot_auto (Tied One auto) <@> recdef <@> u8 0)

-- | Defines the clock step at an instant, where the third parameter is the
-- number of steps since the last high signal.
clockStep :: E f val (Obj (Constant UInt8) :-> Obj (Constant UInt8) :-> Obj (Constant UInt8))
clockStep = fun $ \period -> fun $ \countSoFar ->
  (countSoFar + u8 1) `mod` period
