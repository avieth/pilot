{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

-- {-# LANGUAGE RebindableSyntax #-}
-- 
-- module Main where
-- 
-- import Language.Copilot
-- import Copilot.Compile.C99
-- 
-- -- External temperature as a byte, range of -50C to 100C.
-- temp :: Stream Word8
-- temp = extern "temperature" Nothing
-- 
-- -- Calculate temperature in Celsius.
-- -- We need to cast the Word8 to a Float. Note that it is an unsafeCast, as there
-- -- is no direct relation between Word8 and Float.
-- ctemp :: Stream Float
-- ctemp = (unsafeCast temp) * (150.0 / 255.0) - 50.0
-- 
-- spec = do
--   -- Triggers that fire when the ctemp is too low or too high,
--   -- pass the current ctemp as an argument.
--   trigger "heaton"  (ctemp < 18.0) [arg ctemp]
--   trigger "heatoff" (ctemp > 21.0) [arg ctemp]
-- 
-- -- Compile the spec
-- main = reify spec >>= compile "heater"

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}

module Language.Pilot.Examples.Heater where

import Prelude hiding (Bool, Maybe, (>), (<), (-))

import Language.Pilot

high_threshold :: E f val (Obj (Constant UInt8))
high_threshold = u8 127

low_threshold :: E f val (Obj (Constant UInt8))
low_threshold = u8 64

-- | This function on constants determines when (just) and by how much (the
-- value) some value has exceeded the high threshold.
above :: E f val (Obj (Constant UInt8) :-> Obj (Constant (Maybe UInt8)))
above = fun $ \i -> if_then_else (i > high_threshold)
  (just (i - high_threshold))
  nothing

below :: E f val (Obj (Constant UInt8) :-> Obj (Constant (Maybe UInt8)))
below = fun $ \i -> if_then_else (i < low_threshold)
  (just (low_threshold - i))
  nothing
-- Could use rebindable syntax, but there's a bug in released versions causing
-- a core lint error.
{-
below = fun $ \i ->
  if (i < low_threshold)
  then just (low_threshold - i)
  else nothing
-}

-- Heat on and heat off expressions are functions over the input signal. They
-- are expressed by lifting the corresponding functions over constants, and
-- discarding the extra information inside the Maybe.

heaton :: Known n => E f val (Obj (Varying n UInt8) :-> Obj (Varying n Bool))
heaton = lift_ (Ap Pure) <@> (isJust <.> above)

heatoff :: Known n => E f val (Obj (Varying n UInt8) :-> Obj (Varying n Bool))
heatoff = lift_ (Ap Pure) <@> (isJust <.> below)

-- Next: show how to use heaton and heatoff in pure and in C contexts. Only in
-- the latter do we have a notion of an extern and of a trigger. Should reframe
-- this to show that both triggers can share computation.
