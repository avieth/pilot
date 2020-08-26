{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

-- Copy of this copilot example:

-- -- | Example implementing an engine cooling control system.
-- 
-- {-# LANGUAGE RebindableSyntax #-}
-- 
-- module Main where
-- 
-- import Language.Copilot
-- import qualified Prelude as P
-- 
-- {- If the majority of the engine temperature probes exeeds 250 degrees, then
--  - the cooler is engaged and remains engaged until the majority of the engine
--  - temperature probes drop to 250 or below.  Otherwise, trigger an immediate
--  - shutdown of the engine.
-- -}
-- 
-- engineMonitor :: Spec
-- engineMonitor = do
--   trigger "shutoff" (not ok) [arg maj]
-- 
--   where
--   vals     = [ externW8 "tmp_probe_0" two51
--              , externW8 "tmp_probe_1" two51
--              , externW8 "tmp_probe_2" zero]
--   exceed   = map (> 250) vals
--   maj      = majority exceed
--   checkMaj = aMajority exceed maj
--   ok       = alwaysBeen ((maj && checkMaj) ==> extern "cooler" cooler) 
-- 
--   two51  = Just $ [251, 251] P.++ repeat (250 :: Word8)
--   zero   = Just $ repeat (0 :: Word8)
--   cooler = Just $ [True, True] P.++ repeat False
-- 
-- main :: IO ()
-- main = interpret 10 engineMonitor

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pilot.Examples.Engine where

import qualified Prelude
import Language.Pilot
import Language.Pilot.Examples.LTL
import Language.Pilot.Examples.Voting

-- | Engine probe signal.
type Probe f val = Obj (Varying 'Z UInt8)

-- | Engine cooler signal (on or off).
type Cooler f val = Obj (Varying 'Z Bool)

-- | Would use this to decide when to shut off the engine.
--
-- NB: we need to know statically how many probes there are (cannot take a
-- vanilla list).
engineMonitor
  :: forall n f val .
     NatRep n
  -> E f val (Vector n (Probe f val) :-> Cooler f val :-> Obj (Varying 'Z Bool))
engineMonitor numElements = fun $ \probes -> fun $ \cooler ->
  map_auto Z_Rep <@> lnot <@> (engineOk numElements <@> probes <@> cooler)

engineOk
  :: forall n f val .
     NatRep n
  -> E f val (Vector n (Probe f val) :-> Cooler f val :-> Obj (Varying 'Z Bool))
engineOk numElements = fun $ \probes -> fun $ \cooler -> always <@>
  (local_auto (boyerMooreVarying Zero numElements <@> probes) $ \mMaj ->
    (map_auto Z_Rep <@> (uncurry <@> overheatImpliesCooler) <@> (mMaj <& cooler)))

-- | Function on constants, checking at an instant that if a majority of
-- probes show overheating, then the cooler is engaged.
overheatImpliesCooler :: E f val
  (   Obj (Constant (Maybe UInt8))
  :-> Obj (Constant Bool)
  :-> Obj (Constant Bool)
  )
overheatImpliesCooler = fun $ \mMaj -> fun $ \cooler ->
  (isJust <@> mMaj) ==> cooler
