{-|
Module      : Language.Pilot.Examples.Copilot.LTL
Description : Linear temporal logic examples inspired by copilot.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pilot.Examples.Copilot.LTL where

import qualified Prelude
import Language.Pilot

-- Let's talk about past-time linear temporaly logic (PTLTL). In copilot,
-- the 4 characteristic notions are pretty succinct
--
-- > -- | Did @s@ hold in the previous period?
-- > previous :: Stream Bool -> Stream Bool
-- > previous s = [ False ] ++ s
-- > 
-- > 
-- > -- | Has @s@ always held (up to and including the current state)?
-- > alwaysBeen :: Stream Bool -> Stream Bool
-- > alwaysBeen s = s && tmp
-- >     where tmp = [ True ] ++ s && tmp
-- > 
-- > 
-- > -- | Did @s@ hold at some time in the past (including the current state)?
-- > eventuallyPrev :: Stream Bool -> Stream Bool
-- > eventuallyPrev s = s || tmp
-- >   where tmp = [ False ] ++ s || tmp
-- > 
-- > 
-- > -- | Once @s2@ holds, in the following state (period), does @s1@ continuously hold?
-- > since ::  Stream Bool -> Stream Bool -> Stream Bool
-- > since s1 s2 = alwaysBeen ( tmp ==> s1 )
-- >     where tmp = eventuallyPrev $ [ False ] ++ s2
--
-- To write them out directly here in pilot would look a lot more complicated.
-- But, if they're expressed by a common abstraction, they don't look so bad.
--
-- > previous :: E f val (Obj (varying 'Z Bool) :-> Obj (Varying 'Z Bool))
-- > previous = fold <@> (flip <@> const) <@> false
--
-- > alwaysBeen :: E f val (Obj (Varying 'Z Bool) :-> Obj (Varying 'Z Bool))
-- > alwaysBeen = fold <@> land <@> true
--
-- > eventuallyPrev :: E f val (Obj (Varying 'Z Bool) :-> Obj (Varying 'Z Bool))
-- > eventuallyPrev = fold <@> lor <@> false
--
-- > since  :: E f val (Obj (Varying 'Z Bool) :-> Obj (Varying 'Z Bool) :-> Obj (Varying 'Z Bool))
-- > since = fun $ \x -> fun $ \y ->
-- >   always <@> (map_auto Zero <@> (uncurry <@> implies) <@> (eventually <@> (previous <@> y)) <& x)

-- | Here's a direct implementation of "alwaysBeen".
--
-- NB: this is something which cannot be written pointwise and then
-- lifted/mapped, since it is fundamentally about streams, and requires memory.
always :: forall f val . E f val (Obj (Varying 'Z Bool) :-> Obj (Program (Obj (Varying 'Z Bool))))
always = fun $ \bs ->
  -- Type annotations are optional. The top-level annotation (on 'always') is
  -- enough for GHC to figure it out.
  let -- Definition of the tail of the stream in terms of its prefix, for which
      -- only one value is available (the memory stream is of prefix length 1).
      -- The definition is: take the logical AND of the current value (input
      -- stream bs) and the previous value. This becomes the previous value on
      -- the next frame.
      recdef :: E f val (Obj (Varying (Decimal 0) Bool) :-> Obj (Varying (Decimal 0) Bool))
      recdef = fun $ \prev -> map_auto Zero <@> (uncurry <@> land) <@> (prev <& bs)
      -- The initial values. Since there's only one stream in this knot, there's
      -- only one initial value, and we set it to true. If it were false, then
      -- the entire stream would always be false.
      inits :: E f val (Vector (Decimal 1) (Obj (Constant Bool)))
      inits = true
  in  prog_map auto auto <@> shift_auto <@> (knot_auto (Tied One auto) <@> recdef <@> inits)

-- | Just like 'always' except we use || to combine and false to initialize.
-- This is "eventuallyPrev" from PTLTL.
eventually :: forall f val . E f val (Obj (Varying 'Z Bool) :-> Obj (Program (Obj (Varying 'Z Bool))))
eventually = fun $ \bs ->
  let recdef = fun $ \prev -> map_auto Zero <@> (uncurry <@> lor) <@> (prev <& bs)
      inits = false
  in  prog_map auto auto <@> shift_auto <@> (knot_auto (Tied One auto) <@> recdef <@> inits)

-- | Shows how we can express 'always' and 'eventually' using a higher-order
-- function: a fold on memory streams with a single cell of memory.
ltlFold :: forall f val t . (Known t) => E f val
  (   (Obj (Constant t) :-> Obj (Constant t) :-> Obj (Constant t))
  :-> Obj (Constant t)
  :-> Obj (Varying 'Z t)
  :-> Obj (Program (Obj (Varying 'Z t)))
  )
ltlFold = fun $ \f -> fun $ \t -> fun $ \bs ->
  let recdef = fun $ \prev -> map_auto Zero <@> (uncurry <@> f) <@> (prev <& bs)
      inits = t
  in  prog_map auto auto <@> shift_auto <@> (knot_auto (Tied One auto) <@> recdef <@> inits)

-- | Same as 'always' but more succinct.
alwaysBeen :: E f val (Obj (Varying 'Z Bool) :-> Obj (Program (Obj (Varying 'Z Bool))))
alwaysBeen = ltlFold <@> land <@> true

-- | Same as 'eventually' but more succinct.
eventuallyPrev :: E f val (Obj (Varying 'Z Bool) :-> Obj (Program (Obj (Varying 'Z Bool))))
eventuallyPrev = ltlFold <@> lor <@> false

-- | Another PTLTL notion: it's true whenever the parameter was true on the
-- immediately-previous frame.
previous :: E f val (Obj (Varying 'Z Bool) :-> Obj (Program (Obj (Varying 'Z Bool))))
previous = ltlFold <@> (flip <@> const) <@> false

-- | Changed from the copilot presentation: `eventually <@> y` rather than
-- `eventually <@> (previous <@> y)`. Maybe I'm wrong but this one seems to
-- be the proper definition?
since :: E f val
  (   Obj (Varying 'Z Bool)
  :-> Obj (Varying 'Z Bool)
  :-> Obj (Program (Obj (Varying 'Z Bool)))
  )
since = fun $ \x -> fun $ \y ->
  (eventuallyPrev <@> y) >>= (fun $ \y' ->
  (alwaysBeen <@> (map_auto Zero <@> (uncurry <@> implies) <@> (y' <& x))))

-- TODO bounded LTL can be expressed in a type-safe way by using the `Fin`
-- datatype, giving types such as
--
--   next :: E f val (Obj (Varying (S n) Bool) :-> Obj (Varying n Bool)
--   next = drop
--
--   always :: NatRep (S n) -> Fin (S n) -> E f val
--     (Obj (Varying (S n) Bool) :-> Obj (Varying Z Bool))
