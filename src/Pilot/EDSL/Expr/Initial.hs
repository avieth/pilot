{-|
Module      : Pilot.EDSL.Expr.Initial
Description : "Initial" style ASTs.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

Definition of an "initial" style AST over a non-recursive EDSL type. This
representation allows for pattern-matching on the AST itself so that the
programmer could, for instance, rearrange it to do optimizations.

We typically think about a DSL and its interpretation(s) as completely
separate things with an impenetrable boundary between them. That's the whole
point of a DSL isn't it? Keep the syntax and the semantics completely
independent, so that we can interpret a given expression in many different
ways. But the choice of interpretation could make new expressions available to
the DSL, making that boundary not so clear.

The motivating real-world example of this phenomenon, from my experience, is the
DSL of copilot. It deals in streams, and it can generate C, but could also be
interpreted in Haskell. In order to get useful C, there must be some notion of
an external stream whose values come ultimately from hardware, so copilot offers
an `extern` term to express these. In order to get a useful Haskell
interpretation, there must be some notion of a pure Haskell value that defines
the stream for each time step, so `extern` also takes an optional list of
values.

> -- Stream is the type of the copilot DSL
> Extern :: Typed a => String -> Maybe [a] -> Stream a

This is actually a part of the _language_ itself, and I believe it marks a
fundamental weakness of copilot: not only does it effectively select two
"sacred" interpretations and integrate them into the language, it doesn't allow
for anything but the simplest Haskell interpretation, because the optional
list of values cannot depend upon other streams expressed within the language.
It is not possible to, for instance, simulate a closed-loop control system.

That said, it's easy to appreciate how this came about. We need _some_ way to
bring a C-interpreter-specific stream into a stream expression, so naturally
it too should be a stream expression. The interpretation does indeed seem to
be a part of the language, because it determines a basic expression. So much
for the impenetrable boundary.

This all suggests a different style of DSL definition. Given that there really
are two parts to the ultimate programmer-facing DSL, expressions in that DSL
are trees over _either_ of these two parts: the interpreter-free part, and the
interpreter-specific part. If these parts appear as type parameters on the
expression type, then extent to which any given expression has committed to a
particular interpretation is reflected in the interpreter-specific type
parameter.

Returning to the example of copilot's `Extern`, we would see this removed from
the `Stream` type, and it would appear in a C-specific type, without the
optional list.

> extern :: Typed a => String -> C a
>
> -- Would actually use an infinite list type
> list_stream :: Typed a => [a] -> H a
>
> plus :: (Num a, Typed a) => Stream interp a -> Stream interp a -> Stream interp a
>
> -- plus can be used in any interpreter, according to its arguments
>
> expr_c :: Stream C Int8
> expr_c = plus (extern "n") (constant 42)
>
> expr_h :: Stream H Int8
> expr_h = plus (list_stream [0..]) (constant 42)

-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Pilot.EDSL.Expr.Initial
  ( AST (..)

  , intra
  , extra
  , let_

  , evalAST

  , Terminal (..)
  ) where

import qualified Data.Kind as Haskell (Type)

type Hask = Haskell.Type

-- | An "initial" AST for a given EDSL (called `intra`) and its interpretation
-- (called `extra`).
--
-- Having the interpretation appear in this type allows for expressions to be
-- defined generically, without reference to any _particular_ interpretation,
-- in such a way that an interpretation-specific term may be used within it.
--
-- Take for example an AST for an EDSL which includes a `Plus` term. One library
-- function could be:
--
-- > plus :: AST ParticularEDSL anyInterpretation Int
-- >      -> AST ParticularEDSL anyInterpretation Int
-- >      -> AST ParticularEDSL anyInterpretation Int
-- > plus x y = Intra (Plus x y)
--
-- Since the interpretation type parameter is universally quantified, we could
-- fulfill these arguments using something peculiar to an interpretation:
--
-- > fortyTwo :: AST anyIntra ParticularInterpretation Int
-- >
-- > eightyFour :: AST ParticularEDSL ParticularInterpretation Int
-- > eightyFour = plus fortyTwo fortyTwo
--
-- The idea is that as much of an AST as possible will be defined parametric in
-- the interpreter parameter, and at the boundary, the programmer will choose an
-- interpretation and use this to fill all of the missing parameters.
data AST (intra :: (domain -> Hask) -> domain -> Hask)
         (extra :: (domain -> Hask) -> domain -> Hask)
         (t :: domain)

  where

  Intra :: intra (AST intra extra) t -> AST intra extra t

  Extra :: extra (AST intra extra) t -> AST intra extra t

  -- | Naming/binding is always here. It _could_ be defined in either the intra
  -- or extra part, but it's here instead because there is always a way to
  -- discharge it without actually doing anything interesting. That's because
  -- this is an _embedded_ DSL, and the meta-language Haskell has a notion of
  -- naming/binding which substitues entire AST subtrees. Thus the `Named`
  -- constructor can be dealt with by using a typical Haskell let, if desired,
  -- so this does not preclude any DSLs from making sense in this type.
  Named :: AST intra extra s
        -> (AST intra extra s -> AST intra extra t)
        -> AST intra extra t

intra :: intra (AST intra extra) t -> AST intra extra t
intra = Intra

extra :: extra (AST intra extra) t -> AST intra extra t
extra = Extra

let_ :: AST intra extra s -> (AST intra extra s -> AST intra extra t) -> AST intra extra t
let_ x k = Named x k

-- | Evaluate the AST by evaluating each of its parts into `f`. The functions
-- will almost certainly call `evalAST` themselves.
--
-- TODO alternatively we could use recursion schemes to take care of all of
-- the recursive calls automatically.
evalAST
  :: (forall x . intra (AST intra extra) x -> f x)
  -> (forall x . extra (AST intra extra) x -> f x)
  -> (forall x y . AST intra extra x -> (AST intra extra x -> AST intra extra y) -> f y)
  -> AST intra extra t
  -> f t
evalAST intraF _      _      (Intra intra) = intraF intra
evalAST _      extraF _      (Extra extra) = extraF extra
evalAST _      _      namedF (Named x k)   = namedF x k

-- | Useful for when the `extra` type in an `AST` is non-recursive
newtype Terminal (f :: domain -> Hask) recursive (t :: domain) = Terminal
  { getTerminal :: f t }
