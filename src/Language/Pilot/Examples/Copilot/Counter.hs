{-|
Module      : Language.Pilot.Examples.Copilot.Counter
Description : copilot's counter example
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

-- This gives a counter example similar to the copilot one below.

-- -- | Example showing an implementation of a resettable counter.
-- 
-- {-# LANGUAGE RebindableSyntax #-}
-- 
-- module Main where
-- 
-- import Language.Copilot
-- 
-- -- A resettable counter
-- counter :: Stream Bool -> Stream Bool -> Stream Int32
-- counter inc reset = cnt
--   where
--     cnt = if reset then 0
--           else if inc then z + 1
--                else z
--     z = [0] ++ cnt
-- 
-- -- Counter that resets when it reaches 256
-- bytecounter :: Stream Int32
-- bytecounter = counter true reset where
--   reset = counter true false == 256
-- 
-- spec :: Spec
-- spec = trigger "counter" true [arg $ bytecounter]
-- 
-- main :: IO ()
-- main = interpret 270 spec

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Language.Pilot.Examples.Copilot.Counter where

import Language.Pilot

counter :: E f val
  (   Obj (Varying 'Z Bool)
  :-> Obj (Varying 'Z Bool)
  :-> Obj (Varying ('S 'Z) Int32)
  )
counter = fun $ \inc -> fun $ \reset ->
  let recdef = fun $ \pre ->
        map_auto Z_Rep <@> (uncurry <@> (uncurry <@> counter_step)) <@> (inc <& reset <& pre)
      result = identity
      inputs = i32 0
  in  knot_auto (Tied (S_Rep Z_Rep)) <@> recdef <@> result <@> inputs

-- | This is just like the where clause of "counter" in the copilot variant,
-- except here it's explicitly a function over constants. It will be "lifted"
-- over streams in the definition of the counter itself, once the memory
-- stream is available (will stand in for z).
counter_step :: E f val
  (   Obj (Constant Bool)
  :-> Obj (Constant Bool)
  :-> Obj (Constant Int32)
  :-> Obj (Constant Int32)
  )
counter_step = fun $ \inc -> fun $ \reset -> fun $ \z ->
  if_then_else reset (i32 0) (if_then_else inc (z + i32 1) z)

-- Bug causes core lint errors on released GHCs, but not on HEAD as of
-- August 24, 2020.

{- Fails 
counter_step = fun $ \inc -> fun $ \reset -> fun $ \z ->
  if reset then i32 0
  else if inc then z + i32 1
       else z
-}
{- Passes
counter_step = fun $ \inc -> fun $ \reset -> fun $ \z ->
  ifThenElse reset (i32 (fromInteger (0 :: Integer))) (ifThenElse inc (z + i32 (fromInteger (1 :: Integer))) z)
-}
{- Fails
counter_step = fun $ \inc -> fun $ \reset -> fun $ \z ->
  if reset then (i32 (fromInteger (0 :: Integer)))
  else if inc then z + i32 (fromInteger (1 :: Integer))
       else z
-}
{- Passes
counter_step = fun $ \inc -> fun $ \reset -> fun $ \z ->
  ifThenElse reset (i32 0) (ifThenElse inc (z + i32 1) z)
-}

