{-|
Module      : Examples
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Examples where

import qualified Data.Kind as Haskell (Type)
import Data.Proxy (Proxy (..))
import qualified Data.Word as Haskell
import qualified Data.Int as Haskell

import Pilot.EDSL.Point (Type (..), Cases (..), All (..), Variant (..), ExprF)
import qualified Pilot.EDSL.Point as Point
import Pilot.EDSL.Lifted
import qualified Pilot.C as C

-- Here are some useful definitions of lifted types
--
-- Orphans could be avoided by defining these in the module where Point.Type
-- is defined. Embed instances for application-specific data types would be
-- defined where those types are defined.

instance Embed Point.Type Haskell.Word8 where
  type EmbedT Point.Type Haskell.Word8 = Point.UInt8
  embedT _ _ = Point.uint8_t

instance Embed Point.Type Haskell.Int8 where
  type EmbedT Point.Type Haskell.Int8 = Point.Int8
  embedT _ _ = Point.int8_t

uint8 :: Haskell.Word8 -> Lifted ExprF f val s Haskell.Word8
uint8 = lift . Point.uint8

int8 :: Haskell.Int8 -> Lifted ExprF f val s Haskell.Int8
int8 = lift . Point.int8

instance Embed Point.Type () where
  type EmbedT Point.Type () = Point.Unit
  embedT _ _ = Point.unit_t

unit :: Lifted ExprF f v s ()
unit = lift Point.unit

instance Embed Point.Type Bool where
  type EmbedT Point.Type Bool = Point.Boolean
  embedT _ _ = Point.boolean_t

true :: Lifted ExprF f val s Bool
true = lift Point.true

false :: Lifted ExprF f val s Bool
false = lift Point.false

if_else
  :: forall f val s r .
     (Embed Point.Type r)
  => Lifted ExprF f val s Bool
  -> Lifted ExprF f val s r
  -> Lifted ExprF f val s r
  -> Lifted ExprF f val s r
if_else vb cTrue cFalse = lift $ Point.if_else
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift vb)
  (unlift cTrue)
  (unlift cFalse)

instance Embed Point.Type t => Embed Point.Type (Prelude.Maybe t) where
  type EmbedT Point.Type (Prelude.Maybe t) = Point.Maybe (EmbedT Point.Type t)
  embedT _ _ = Point.maybe_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

nothing
  :: forall f val s t .
     ( Embed Point.Type t )
  => Lifted ExprF f val s (Prelude.Maybe t)
nothing = lift $ Point.nothing
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

just
  :: forall f val s t .
     ( Embed Point.Type t )
  => Lifted ExprF f val s t
  -> Lifted ExprF f val s (Prelude.Maybe t)
just vt = lift $ Point.just
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (unlift vt)

maybe
  :: forall f val s t r .
     ( Embed Point.Type t, Embed Point.Type r )
  => Lifted ExprF f val s (Prelude.Maybe t)
  -> Lifted ExprF f val s r
  -> (Lifted ExprF f val s t -> Lifted ExprF f val s r)
  -> Lifted ExprF f val s r
maybe mx cNothing cJust = lift $ Point.elim_maybe
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))
  (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r))
  (unlift mx)
  (const (unlift cNothing))
  (unlift . cJust . lift)

instance (Embed Point.Type s, Embed Point.Type t) => Embed Point.Type (s, t) where
  type EmbedT Point.Type (s, t) = Point.Pair (EmbedT Point.Type s) (EmbedT Point.Type t)
  embedT _ _ = Point.pair_t (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy s))
                            (embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy t))

pair
  :: forall f val s a b .
     ( Embed Point.Type a, Embed Point.Type b )
  => Lifted ExprF f val s a
  -> Lifted ExprF f val s b
  -> Lifted ExprF f val s (a, b)
pair ea eb = lift $ Point.pair arep brep (unlift ea) (unlift eb)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

fst
  :: forall f val s a b .
     ( Embed Point.Type a, Embed Point.Type b )
  => Lifted ExprF f val s (a, b)
  -> Lifted ExprF f val s a
fst p = lift $ Point.fst arep brep (unlift p)
  where
  arep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy a)
  brep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy b)

-- | Suppose we wanted a custom enum like this
--
--   data MyEnum = A | B | C | D
--
-- We would just define a new nominal type and then give the representation in
-- the Embed instance.
data ApplicationSpecificType

instance Embed Point.Type ApplicationSpecificType where
  -- The embedding is defined by way the embedding of (). We could just as well
  -- have used Point.Unit instead but this shows how a more complex thing might
  -- be defined.
  type EmbedT Point.Type ApplicationSpecificType = 'Sum
    '[ EmbedT Point.Type ()   -- A
     , EmbedT Point.Type ()   -- B
     , EmbedT Point.Type ()   -- C
     , EmbedT Point.Type () ] -- D
  embedT _ _ = Point.Sum_t (And urep $ And urep $ And urep $ And urep $ All)
    where
    urep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ())

variant_A :: Lifted ExprF f val s ApplicationSpecificType
variant_A = lift $ Point.exprF $ Point.IntroSum trep $ (AnyV Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_B :: Lifted ExprF f val s ApplicationSpecificType
variant_B = lift $ Point.exprF $ Point.IntroSum trep $ (OrV $ AnyV Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_C :: Lifted ExprF f val s ApplicationSpecificType
variant_C = lift $ Point.exprF $ Point.IntroSum trep $ (OrV $ OrV $ AnyV Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

variant_D :: Lifted ExprF f val s ApplicationSpecificType
variant_D = lift $ Point.exprF $ Point.IntroSum trep $ (OrV $ OrV $ OrV $ AnyV Point.unit)
  where
  trep :: Point.TypeRep (EmbedT Point.Type ApplicationSpecificType)
  trep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)

-- | Case match to eliminate an ApplicationSpecificType
variant
  :: forall f val s r .
     ( Embed Point.Type r )
  => Lifted ExprF f val s ApplicationSpecificType
  -> Lifted ExprF f val s r -- if A
  -> Lifted ExprF f val s r -- if B
  -> Lifted ExprF f val s r -- if C
  -> Lifted ExprF f val s r -- if D
  -> Lifted ExprF f val s r
variant vv cA cB cC cD = lift $ Point.exprF $ Point.ElimSum srep rrep cases (unlift vv)
  where
  -- The lower-level representation requires type annotations everywhere, but
  -- we can just grab those from the embed instances.
  srep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ApplicationSpecificType)
  rrep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy r)
  urep = embedT (Proxy :: Proxy Point.Type) (Proxy :: Proxy ())
  cases =
      AndC urep (const (unlift cA))
    $ AndC urep (const (unlift cB))
    $ AndC urep (const (unlift cC))
    $ AndC urep (const (unlift cD))
    $ AllC

write_lifted :: String -> Lifted ExprF C.CodeGen C.Val s x -> IO ()
write_lifted fpath = C.write_example fpath . unlift
