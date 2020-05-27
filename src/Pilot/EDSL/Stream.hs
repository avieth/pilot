{-|
Module      : Pilot.EDSL.Stream
Description : Definition of the streamwise EDSL
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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Pilot.EDSL.Stream
  ( Type (..)
  , TypeRep (..)
  , ExprF (..)
  , constant
  , drop
  , shift
  , memory
  , liftF
  , liftF_

  , arg
  , ap
  , (<@>)
  , (<&>)
  ) where

import Prelude hiding (drop)
import qualified Data.Kind as Haskell (Type)

import Pilot.EDSL.Expr as Expr
import Pilot.Types.Fun as Fun
import Pilot.Types.Nat
import Pilot.Types.Represented

data Type t where
  -- | A stream with a given number of "prefix" values (memory).
  Stream   :: Nat -> t -> Type t

data TypeRep (t :: Type s) where
  Stream_t   :: NatRep n -> Rep s t -> TypeRep ('Stream n t)

-- | TODO document
data ExprF
  (point  :: a -> Haskell.Type)
  (static :: a -> Haskell.Type)
  (expr   :: Type a -> Haskell.Type)
  (t      :: Type a)
  where

  -- | Any expression in the pointwise EDSL parameter can be made into a stream
  -- by specifying an arbitrary prefix. This is similar to using "pure" on a
  -- zip list.
  ConstantStream :: Rep a t
                 -> NatRep n
                 -> point t
                 -- ^ NB: this is not `pexpr t`, because `pexpr` represents a
                 -- different EDSL, and we want the embedding of that one into
                 -- this one to be represented here (by the `ConstantPoint`
                 -- term).
                 -> ExprF point static expr ('Stream n t)

  -- | Any first-order function within expr can be "lifted" so that all of its
  -- arguments and its results are now streams. It must be fully applied, since
  -- this language does not have functions. Makes sense: all of the other
  -- expressions which take parameters are fully applied (intro/elim,
  -- arithmetic, etc).
  LiftStream :: Args (Rep a) args
             -> Rep a r
             -> NatRep n
             -> (Args point args -> point r)
             -- ^ The function being lifted. NB: the arguments are all point
             -- _expressions_. Problem? You'd think they should be vals but
             -- we don't have the point val constructor.
             -> Args expr (MapArgs ('Stream n) args)
             -- ^ The arguments to the lifted function, but their types now have
             -- Stream n applied out front.
             -- An interpretation of this term therefore must be able to
             -- use `Stream n t` wherever `t` is required, so long as the result
             -- also has `Stream n` in front. This is like applicative functor
             -- style.
             -> ExprF point static expr ('Stream n r)

  -- TODO rename? Drop suggests that we drop x-many things, but the number we
  -- give is (the NatRep) is what the size will be after dropping 1.
  DropStream :: Rep a t
             -> NatRep ('S n)
             -> expr ('Stream ('S n) t)
             -> ExprF point static expr ('Stream n t)

  -- Like DropStream it lowers the nat index, but the value at an instant of the
  -- stream doesn't change. This just says that a stream with more memory can
  -- stand in for a stream with less memory, whereas DropStream says that we
  -- can forget memory.
  ShiftStream :: Rep a t
              -> NatRep ('S n)
              -> expr ('Stream ('S n) t)
              -> ExprF point static expr ('Stream n t)

  MemoryStream :: Rep a t
               -> NatRep ('S n)
               -> Vec ('S n) (static t)
               -- ^ The initial values of the stream must be static constants
               -- (note the kind uses `a`, not `Stream a`). What "static" means
               -- is suggested by connotation, but left up to the interpreter.
               -- Some interpreters may be able to use any pexpr expression
               -- here, some may not be so lenient.
               -> (expr ('Stream n t) -> expr ('Stream 'Z t))
               -- ^ The stream itself may be used to determine the rest of
               -- the stream, but the nat index is one less, so that a cyclic
               -- definition is not possible (only values already known may
               -- be used).
               -> ExprF point static expr ('Stream ('S n) t)

constant
  :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n f t .
     Rep p t
  -> NatRep n
  -> pexpr t
  -> Expr (ExprF pexpr static) val f ('Stream n t)
constant trep nrep p = exprF $ ConstantStream trep nrep p

drop :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n f t .
        Rep p t
     -> NatRep ('S n)
     -> Expr (ExprF pexpr static) val f ('Stream ('S n) t)
     -> Expr (ExprF pexpr static) val f ('Stream     n  t)
drop trep nrep s = exprF $ DropStream trep nrep s

shift :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n f t .
         Rep p t
      -> NatRep ('S n)
      -> Expr (ExprF pexpr static) val f ('Stream ('S n) t)
      -> Expr (ExprF pexpr static) val f ('Stream     n  t)
shift trep nrep s = exprF $ ShiftStream trep nrep s

memory :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n f t .
          Rep p t
       -> NatRep ('S n)
       -> Vec ('S n) (static t)
       -> (Expr (ExprF pexpr static) val f ('Stream n t) -> Expr (ExprF pexpr static) val f ('Stream 'Z t))
       -> Expr (ExprF pexpr static) val f ('Stream ('S n) t)
memory trep nrep inits k = exprF $ MemoryStream trep nrep inits k

-- TODO remove? probably not useful. 'lift' seems like a better type from a
-- usability perspective.
liftF_ :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n args f r .
          Args (Rep p) args
       -> Rep p r
       -> NatRep n
       -> (Args pexpr args -> pexpr r)
       -> Args (Expr (ExprF pexpr static) val f) (MapArgs ('Stream n) args)
       -> Expr (ExprF pexpr static) val f ('Stream n r)
liftF_ argsrep trep nrep f args = exprF $ LiftStream argsrep trep nrep f args

-- | Any first-order function over expressions can be "lifted" over streams:
-- all of the arguments and the result become streams.
--
-- This is like typical applicative functor style in Haskell. Such things cannot
-- be done directly in this EDSL, because it doesn't have functions.
liftF :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) static val n args f r .
         Args (Rep p) args
      -> Rep p r
      -> NatRep n
      -> Fun pexpr ('Sig args r)
      -> Fun (Expr (ExprF pexpr static) val f) (Fun.Lift ('Stream n) ('Sig args r))
liftF argsrep trep nrep f = Fun.unapply (mkStreamRep nrep argsrep) $ \sargs ->
  exprF $ LiftStream argsrep trep nrep (Fun.apply f) sargs

-- | "Lift" the argument type reps into streams for a given prefix length.
mkStreamRep :: NatRep n -> Args (Rep s) ts -> Args TypeRep (MapArgs ('Stream n) ts)
mkStreamRep _    Args            = Args
mkStreamRep nrep (Arg arep args) = Arg (Stream_t nrep arep) (mkStreamRep nrep args)

-- With the following functions you can often write
--
--   ap f <@> arg arg1 <&> ... <&> arg argN
--
-- where f is a pointwise function defined using `fun` and `lit` from
-- Pilot.Types.Fun.

ap :: (KnownArgs args, Auto r, Auto n)
   => Fun pexpr ('Sig args r)
   -> Fun (Expr (ExprF pexpr static) val f) (Fun.Lift ('Stream n) ('Sig args r))
ap f = liftF autoArgs auto auto f

(<#>) :: Fun (Expr (ExprF pexpr static) val f) ('Sig (t ': ts) r)
      -> Expr (ExprF pexpr static) val f t
      -> Fun (Expr (ExprF pexpr static) val f) ('Sig ts r)
(<#>) = Fun.at

arg :: Expr expr val f t
    -> Args (Expr expr val f) ts
    -> Args (Expr expr val f) (t ': ts)
arg e = Arg e

-- NB: only the left is universally quantified on the tail. The right, in
-- repeated right-associative applications, will have a particular tail type.
(<&>) :: (forall xs . Args (Expr expr val f) xs -> Args (Expr expr val f) (t ': xs))
      -> (Args (Expr expr val f) ts -> Args (Expr expr val f) ts')
      -> (Args (Expr expr val f) ts -> Args (Expr expr val f) (t ': ts'))
(<&>) left right args = left (right args)

infixr 2 <&>

(<@>) :: Fun (Expr (ExprF pexpr static) val f) ('Sig args r)
      -> (Args (Expr (ExprF pexpr static) val f) '[] -> Args (Expr (ExprF pexpr static) val f) args)
      -> Expr (ExprF pexpr static) val f r
(<@>) f xs = Fun.apply f (xs Args)

infix 1 <@>
