{-|
Module      : Language.Pilot
Description :
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Pilot
  ( Point
  , Stream
  , E

  , Meta_k
  , Object_k
  , Meta.Obj
  , Meta.Terminal
  , type (Meta.:->)
  , type (Meta.:*)
  , Repr.fun
  , Repr.app
  , (Repr.<@>)
  , Repr.id
  , Repr.compose
  , (Repr.<.>)
  , Repr.const
  , Repr.flip
  , Repr.curry
  , Repr.uncurry

  , Repr.product
  , Repr.terminal
  , Repr.fst
  , Repr.snd
  , (Repr.<&)
  , (Repr.&>)

  , Point_k
  , Object.Constant
  , Object.Varying

  , Object.UInt8
  , Object.UInt16
  , Object.UInt32
  , Object.UInt64
  , Object.Int8
  , Object.Int16
  , Object.Int32
  , Object.Int64
  , Object.Word8
  , Object.Word16
  , Object.Word32
  , Object.Word64
  , Object.Product
  , Object.Sum
  , Object.Unit
  , Object.Void
  , Object.Bool
  , Object.Cmp
  , Object.Maybe
  , Object.Pair
  , Object.Either

  , Object.Width (..)
  , Object.Signedness (..)

  , Object.shift
  , Object.drop
  , Object.lift
  , Object.lift_
  , Object.knot
  , Object.Knot (..)
  , Object.Lift (..)
  , Object.Fields (..)
  , Object.Variant (..)
  , Object.Selector (..)
  , Object.Cases (..)

  , Object.unit
  , Object.absurd
  , Object.pair
  , Object.true
  , Object.false
  , Object.if_then_else
  , Object.maybe
  , Object.just
  , Object.nothing

  , Object.u8
  , Object.i8
  , Object.plus
  , Object.plus_u8

  , Object.AutoLift
  , Nat (..)
  , Auto
  , repVal
  , NatRep (..)

  ) where

import qualified Language.Pilot.Repr as Repr
import qualified Language.Pilot.Meta as Meta
import qualified Language.Pilot.Object as Object
import Language.Pilot.Types

type Point t = Meta.Obj (Object.Constant t)
type Stream n t = Meta.Obj (Object.Varying n t)
type Form = Object.Form

type E f val t = Repr.E Form f val t

type Meta_k = Meta.Type
type Object_k = Object.Type
type Point_k = Object.Point

-- TODO
--
-- This module should be only the formal language.
-- Another module should be made to facilitate the pure interpretation.
--
-- - Using the Meta_f function forms in the final style? There will be
--   ambiguity, but will it actually be a problem?
--
-- - The C backend representation: what will it be? I'd imagine it's a
--   value type `Meta.Type Object.Type -> Hask` which is `Meta_r C.Expr`,
--   wrapped in a "context" which tracks the necessary C declarations, bindings,
--   etc. which give the expression meaning.
--   Then at the top-level we have a CodeGen monad for declaring I/Os.
--   In fact, CodeGen _is_ the context. We define this to be a proper monad,
--   and then we specialize it to get the representation (which has a different
--   kind).
--
-- Ideas to look into:
--
-- - Meta_f and Meta_r are weird: the form and representation are essentially
--   the same, in that the representation is given in the form. It's not
--   crazy to think that we could always use Meta_r in the representation. But
--   in order to accomodate let bindings which introduce sharing over functions
--   and products, it'd have to be behind some functor, leading us back again
--   to the f/val distinction
--
--     type MRepr (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta_t domain) = f (Meta_r val)
--
--   actually not quite...
--
--     newtype MRepr (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta_t domain) = MRepr
--       { getMRepr :: f (MVal f val t) }
--
--     data MVal (f :: Hask -> Hask) (val :: domain -> Hask) (t :: domain) where
--       MObject   :: val t -> MVal f val (Obj t)
--       MFun      :: (MRepr f val s -> MRepr f val t) -> MVal f val (s :-> t)
--       MProduct  :: (MRepr f val s ,  MRepr f val t) -> MVal f val (s :*: t)
--       MTerminal :: MVal f val Terminal
--
--   Then if everything is done in the final class-based style at MRepr, we're
--   good to go.
--
--     object :: f (val t) -> MRepr f val t
--
--     fun :: (MRepr f val s -> MRepr f val t) -> MRepr f val (s :-> t)
--
--     app :: Monad f => MRepr f val (s :-> t) -> MRepr f val s -> MRepr f val t
--     app frepr xrepr = MRepr $ do
--       MFun f <- getRepr frepr
--            x <- getRepr xrepr
--       f x
--
--   Yeah, we would need f to be a Monad in order to do application. Key
--   question to look into is: does this make any sense / is this reasonable?
--   What makes me skeptical is that it induces an order. Why should we have to
--   "evaluate" the function before the argument? Well, do we?
--
--     app frepr xrepr = MRepr (join (funApply <$> getExpr frepr <*> getExpr xrepr))
--
--   ^ This says that the function and the argument of course must be ordered
--   before the application itself can be known, but it doesn't say how they
--   are ordered w.r.t. one-another.
--
--   Then we'd have
--
--     class Monad f => Interprets form f val where
--       interpet :: forall x . form (MVal f val) x -> MVal f val x
--
--   constructing meta-language functions and products needs only applicative.
--
--     fun :: Applicative f => (MRepr f val s -> MRepr f val t) -> MRepr f val (s :-> t)
--     fun f = MRepr (pure (MFun f))
--
--     product :: Applicative f => MRepr f val s -> MRepr f val t -> MRepr f val (s :*: t)
--     product s t = MRepr (pure (MProduct (s, t)))
--
--   Then, it would seem, let-bindings are monadic binds in f? No, they can't
--   be, since it's too general. They'd be a special kind that only works for
--   objects. And it's here where we actually do want an ordering.
--
-- - Could we get away with putting _all_ of Hask into the meta part?
--
--     Meta_t   :: Hask -> Meta t
--     Object_t :: t    -> Meta t
--
--     Meta_f :: t -> Meta.Type (Meta_t t)
--
--   This way, we could use, say, Haskell records within the EDSL, which could
--   be much nicer than working with binary products only.
--
--   So we would have, as part of the interpeter
--
--     meta_f :: forall (t :: Hask) . t -> repr (Meta_t t)
--
--   which would have to be something quite simple, since we don't know the
--   type. Then I think what we would need is an applicative style thing on
--   the repr
--
--     repr (Meta_t (a -> b)) -> repr (Meta_t a) -> repr (Meta_t b)
--
--
