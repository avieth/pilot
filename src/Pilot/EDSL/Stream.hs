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
  , point
  , constant
  , drop
  , shift
  , memory
  , liftF
  , liftF_
  ) where

import Prelude hiding (drop)
import qualified Data.Kind as Haskell (Type)

import Pilot.EDSL.Expr as Expr
import Pilot.Types.Fun as Fun
import Pilot.Types.Nat
import Pilot.Types.Represented

-- Some observations:
--
-- - The code gen monad CodeGen will be capable of handling points _and_ streams.
--   - A stream is a struct with an array of known size, and an index always
--     modulo that fixed size. The array is always at least size 2, since
--     streams of prefix 0 have a read and a write cell.
--   - Every stream which appears is updated at the end of the step function in
--     a uniform way... so streams must be introduced explicitly.
--   - There must be a setup function which initializes every stream, since not
--     all initial stream values will be statics.
--   - Some streams will in fact be identifiable as constants (they consist
--     only of pointwise computation with no externs).
--
-- - This is all to say: the C code gen module works for point _and_ stream.
--   Its `Val` type ought to accept both of these domains...
--
-- - Future plans: finite streams.
--   Lessons learnt here will be valuable for this extension. Instead of a
--   `Stream n t` type we'll want also `FiniteStream a b t` which is kind of
--   like a category in `a` and `b` which defines a `t` at each frame: give an
--   `a` and you immediately get a `t` at that frame, then at each intermediate
--   frame until you get a `b`. There is no `t` on the last frame when you get
--   a `b`. In Hask it would be like this
--
--     type FiniteStream a b t = a -> Next b t
--     type Next = Either b (t, Next b t)
--
--   note the subtle point that wasn't clear above: if you get a `b` right away
--   then you never get a `t`.
--   Then we'd want to have category composition, as well as the ability to
--   define a loop (we can't use meta-language recursion).
--
--     fsmap :: Point (a :-> b) -> FiniteStream a b s -> FiniteStream a b t
--     compose :: FiniteStream a b t -> FiniteStream b c t -> FiniteStream a c t
--     loop :: FiniteStream a a t -> Stream Z t
--
--
-- Here's the breakdown
--
-- - `Stream n` is like `IO`. You can't "get out" of it, but you can do functor
--   applicative monad with it _inside the EDSL_.
-- - The only non-pure general construction of this is the hold/drop thing.
--   If there is no hold, it's just a "pure" (pointwise) term.
--
--     Vec (S n) (Expr t) -> (Expr (Stream n t) -> Expr (Stream Z t)) -> Expr (Stream (S n) t)
--
--   ^ that says that you can use the stream itself to define the rest of
--   the stream. Note the nat index: if you specify 1 thing, then you can drop
--   once in the result (to get the current thing).
--
--   The nat type parameter determines the amount of static storage required:
--   this many times the size of the underlying representation. Indeed, if it's
--   0, then the stream is represented _on the stack_ of the step function; no
--   more memory needed. To avoid the hazard of out-of-order updates to stateful
--   streams, we can do what Frank suggested for copilot: compute the new values
--   for each stateful stream up-front, before updating any of them, then update
--   them all in one go.
--
--   How about the nat type parameter in the context of dropping? If it's 1,
--   then you shouldn't be able to drop anything, right? Or, no... seems wird.
--   A non-stateful stream obviously cannot be dropped, but you'd think that if
--   it were a 1-stream you could drop once and get the "current" value.
--   It _is_ ok to drop once from a 1-stream: you just replace it with that
--   stream's "next value" expression.
--
--   So, notice that the nat type parameter in the continuation argument is
--   1 less than the vector given. That's important: it signals that you cannot
--   drop past the whole vector to get to the current value (which is the one
--   we are defining).
--   Suppose we gave the vector [0, 1, 2] as the argument.
--
--     +-----------+---------------
--     | 0 | 1 | 2 | The future....
--     +-----------+---------------
--
--   Dropping once would give 1, twice would give 2, and thirce would give the
--   actual "current" as in time value.
--   This is fine once the current as in time value is defined, i.e. once we
--   have the result of the continuation. But within the continuation, we must
--   ensure that we cannot drop more than twice. i.e. '2' must be the latest
--   value.
--
--   In the common example of the integral, we would do something like this
--
--     integral f = state [0] $ \accumulator ->
--       -- cannot drop from accumulator, it has prefix size 0; but, its current
--       -- value is in fact the previous one and can be used to define the
--       -- actual current value.
--       -- Applicative style is used because f and accumulator are streams.
--       plus <$> accumulator <*> f
--
--   How is this treated in code generation?
--
--
--   - ALSO IMPORTANT pure streams should be "infinite memory" i.e. the nat
--     parameter should be forall.
--     To combine streams, they must have the same prefix length. In addition
--     to dropping (moving "forward" in the stream), you can also just decrement
--     the prefix size parameter so that the stream can appear shorter without
--     changing the value.
--     For safety, all we need is that we can never allow an index out of
--     bounds. For that, we simply need to ensure that the nat type index can't
--     grow. No problem. Dropping just means bumping the index modulo the size.
--     But what happens when we drop as many as the size? Then we want to
--     somehow magically replace it with the expression that computes the next
--     thing. So, may as well put that computation in right there at the spot
--     where the stream is defined? Yeah, always allocate on the stack for it,
--     compute the expression there, and then at the end of the step copy it
--     over to the current cell before bumping the index.
--     But this doesn't solve the problem of how to know, given a Drop term,
--     whether the thing.. well, we have the TypeRep don't we? 
--     We want to maintain the invariant that there is always precisely one
--     C expression representing the thing... We could do a macro maybe and put
--
--       DROP <stream_expression>
--
--     ?? Or we could just solve this be making `Val` actually use its type
--     index. If it's a stream with a nonzero size index then it comes with
--     expressions for its memory and for its current value.
--
-- - Specific to the C backend: you can introduce impure streams by way of an
--   extern. You can also introduce pure things (non-streams) by way of an
--   extern const.
-- -   

data Type t where
  Constant :: t -> Type t
  -- | A stream with a given number of "prefix" values (memory).
  Stream   :: Nat -> t -> Type t

data TypeRep (t :: Type s) where
  Constant_t :: Rep s t -> TypeRep ('Constant t)
  Stream_t   :: NatRep n -> Rep s t -> TypeRep ('Stream n t)

-- | TODO document
data ExprF
  (pexpr :: a -> Haskell.Type)
  (expr  :: Type a -> Haskell.Type)
  (t     :: Type a)
  where

  -- | Any expression in the base EDSL may appear in the stream EDSL, with
  -- the "constant" type
  ConstantPoint :: Rep a t
                -> pexpr t
                -> ExprF pexpr expr ('Constant t)

  -- | Any constant value can be made into a stream by specifying an arbitrary
  -- prefix. This is like using "pure" on a zip list.
  ConstantStream :: Rep a t
                 -> NatRep n
                 -> expr ('Constant t)
                 -- ^ NB: this is not `point t`. That's because `point`
                 -- represents a different EDSL, and the embedding of that one
                 -- into this one must be defined as part of the interpretation
                 -- of this term ConstantStream.
                 --
                 -- Ah but this doesn't work because `f` has the wrong kind...
                 --
                 -- Maybe we do need the val type after all???
                 -> ExprF pexpr expr ('Stream n t)

  -- | Any first-order function within expr can be "lifted" so that all of its
  -- arguments and its results are now streams. It must be fully applied, since
  -- this language does not have functions. Makes sense: all of the other
  -- expressions which take parameters are fully applied (intro/elim,
  -- arithmetic, etc).
  --
  -- NB: this also expresses "pure" or constant streams, when the argument list
  -- is empty.
  -- TODO maybe that's not a good idea though?
  LiftStream :: Args (Rep a) args
             -> Rep a r
             -> NatRep n
             -> (Args pexpr args -> pexpr r)
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
             -> ExprF pexpr expr ('Stream n r)

  -- TODO rename? Drop suggests that we drop x-many things, but the number we
  -- give is (the NatRep) is what the size will be after dropping 1.
  --
  -- TODO explain why we use two 'S constructors (it's because of memory
  -- stream and avoiding circular definitions).
  -- NB: shift stream can be just one 'S cosntructor.
  DropStream :: Rep a t
             -> NatRep ('S ('S n))
             -> expr ('Stream ('S ('S n)) t)
             -> ExprF pexpr expr ('Stream ('S n) t)

  -- Like DropStream it lowers the nat index, but the value at an instant of the
  -- stream doesn't change. This just says that a stream with more memory can
  -- stand in for a stream with less memory, whereas DropStream says that we
  -- can forget memory.
  ShiftStream :: Rep a t
              -> NatRep ('S n)
              -> expr ('Stream ('S n) t)
              -> ExprF pexpr expr ('Stream n t)

{-
  -- TODO comment/doc
  MemoryStream :: Rep a t
               -> NatRep ('S n)
               -> Vec ('S n) (expr ('Constant t)) -- ^ NB: initial elements must be constants.
               -> expr ('Stream 'Z t) -- ^ The rest of the stream.
               -> ExprF pexpr expr ('Stream ('S n) t)
-}

  MemoryStream :: Rep a t
               -> NatRep ('S n)
               -> Vec ('S n) (expr ('Constant t))
               -> (expr ('Stream n t) -> expr ('Stream 'Z t))
               -- ^ The stream itself may be used to determine the rest of
               -- the stream, but the nat index is one less, so that a cyclic
               -- definition is not possible (only values already known may
               -- be used).
               -> ExprF pexpr expr ('Stream ('S n) t)

{-
-- This definition of Fix cannot be any good... the stream and the return
-- value aren't in the same expr.

  FixStream :: Rep a t
            -> TypeRep r
            -> NatRep n
            -> (expr ('Stream n t) -> (expr r, expr ('Stream ('S n) t)))
            -> ExprF pexpr expr r

fix :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t r .
       Rep p t
    -> TypeRep r
    -> NatRep n
    -> (Expr (ExprF pexpr) expr f ('Stream n t) -> (Expr (ExprF pexpr) expr f r, Expr (ExprF pexpr) expr f ('Stream ('S n) t)))
    -> Expr (ExprF pexpr) expr f r
fix trep rrep nrep k = exprF $ FixStream trep rrep nrep k
-}

point
  :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) expr f t .
     Rep p t
  -> pexpr t
  -> Expr (ExprF pexpr) expr f ('Constant t)
point trep pexpr = exprF $ ConstantPoint trep pexpr

constant
  :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t .
     Rep p t
  -> NatRep n
  -> Expr (ExprF pexpr) expr f ('Constant t)
  -> Expr (ExprF pexpr) expr f ('Stream n t)
-- NB if we had a NatRep we could do this:
--   constant trep t = Fun.unval (lift nrep Args (Val t))
-- but it wouldn't be good to have to specify a prefix size for constant
-- streams.
constant trep nrep p = exprF $ ConstantStream trep nrep p

drop :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t .
        Rep p t
     -> NatRep ('S ('S n))
     -> Expr (ExprF pexpr) expr f ('Stream ('S ('S n)) t)
     -> Expr (ExprF pexpr) expr f ('Stream ('S n) t)
drop trep nrep s = exprF $ DropStream trep nrep s

shift :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t .
         Rep p t
      -> NatRep ('S n)
      -> Expr (ExprF pexpr) expr f ('Stream ('S n) t)
      -> Expr (ExprF pexpr) expr f ('Stream n t)
shift trep nrep s = exprF $ ShiftStream trep nrep s

{-
memory :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t .
          Rep p t
       -> NatRep ('S n)
       -> Vec ('S n) (Expr (ExprF pexpr) expr f ('Constant t))
       -> Expr (ExprF pexpr) expr f ('Stream 'Z t)
       -> Expr (ExprF pexpr) expr f ('Stream ('S n) t)
memory trep nrep inits rest = exprF $ MemoryStream trep nrep inits rest
-}

memory :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n expr f t .
          Rep p t
       -> NatRep ('S n)
       -> Vec ('S n) (Expr (ExprF pexpr) expr f ('Constant t))
       -> (Expr (ExprF pexpr) expr f ('Stream n t) -> Expr (ExprF pexpr) expr f ('Stream 'Z t))
       -> Expr (ExprF pexpr) expr f ('Stream ('S n) t)
memory trep nrep inits k = exprF $ MemoryStream trep nrep inits k

-- TODO remove? probably not useful. 'lift' seems like a better type from a
-- usability perspective.
liftF_ :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n args expr f r .
          Args (Rep p) args
       -> Rep p r
       -> NatRep n
       -> (Args pexpr args -> pexpr r)
       -> Args (Expr (ExprF pexpr) expr f) (MapArgs ('Stream n) args)
       -> Expr (ExprF pexpr) expr f ('Stream n r)
liftF_ argsrep trep nrep f args = exprF $ LiftStream argsrep trep nrep f args

-- | Any first-order function over expressions can be "lifted" over streams:
-- all of the arguments and the result become streams.
--
-- This is like typical applicative functor style in Haskell. Such things cannot
-- be done directly in this EDSL, because it doesn't have functions.
liftF :: forall (p :: Haskell.Type) (pexpr :: p -> Haskell.Type) n args expr f r .
         Args (Rep p) args
      -> Rep p r
      -> NatRep n
      -> Fun pexpr ('Sig args r)
      -> Fun (Expr (ExprF pexpr) expr f) (Fun.Lift ('Stream n) ('Sig args r))
liftF argsrep trep nrep f = Fun.unapply (mkStreamRep nrep argsrep) $ \sargs ->
  exprF $ LiftStream argsrep trep nrep (Fun.apply f) sargs

-- | "Lift" the argument type reps into streams for a given prefix length.
mkStreamRep :: NatRep n -> Args (Rep s) ts -> Args TypeRep (MapArgs ('Stream n) ts)
mkStreamRep _    Args            = Args
mkStreamRep nrep (Arg arep args) = Arg (Stream_t nrep arep) (mkStreamRep nrep args)
