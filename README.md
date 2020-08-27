# pilot: C EDSL inspired by copilot

## Why?

This is like [copilot](https://github.com/Copilot-Language/copilot) but way more
complex from the user's perspecitve. Why does it exist? Because copilot is
really cool, but

1. It doesn't support algebraic datatypes; control flow quickly becomes
   unwieldly since it all must go by way of numbers as it would in C itself
2. It only supports in-Haskell simulation _on paper_; it's inadequate for
   everything but the most trivial examples
3. All triggers are independent; it is impossible to express sharing between
   them, which can be problematic in larger deployments
4. Stream prefix sizes are not present at the type level; the notions of
   `drop` and `(++)` are not typed, and in my experience this is quite
   error-prone

This project aims to fill in these gaps, and also to explore one further idea.

Programming in copilot is programming with streams. Familiar notions like
arithmetic and bitwise operations are implicitly "lifted" pointwise over
streams, and any "point" or "scalar" value can be made into a stream by way
of the `constant` function. This is all annoyingly reminiscent of an
applicative functor; it's the [ZipList](https://hackage.haskell.org/package/base-4.14.0.0/docs/Control-Applicative.html#t:ZipList), in particular. But within the copilot language itself, there are
no functors or applicatives. There aren't even any _functions_ in the
language--and we don't _want_ functions in the language--so how could we
possibly have functors? The question, then, is whether it is possible to have,
within an EDSL that does not even have functions, a programming style similar
to that of Haskell's `Functor` and `Applicative`?

This project says "Yes!". Read on to find out how.

## Overview

The pilot EDSL is expressed in what is essentially the
["tagless-final" style](http://okmij.org/ftp/tagless-final/index.html), except
that there's a GADT defining the forms, instead of a bunch of typeclass
methods. In the tagless-final style, there's a representation type, which is
made to be an instance of the typeclass which gives the abstract forms. In
pilot, this representation is split into two parts, and Haskell's products,
functions, and terminal object are added into it.

```Haskell
-- Language.Pilot.Repr

import Language.Pilot.Meta as Meta (Type, Terminal, Obj, type (:->), type (:*))

newtype Repr (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta.Type domain) = Repr
  { getRepr :: f (Val f val t) }

data Val (f :: Hask -> Hask) (val :: domain -> Hask) (t :: Meta.Type domain) where
  Object   :: val t -> Val f val (Obj t)
  Arrow    :: (Repr f val s -> Repr f val t) -> Val f val (s :-> t)
  Product  :: (Repr f val s ,  Repr f val t) -> Val f val (s :*  t)
  Terminal :: Val f val Terminal
```

The tagless-final style typeclass therefore looks like this:

```Haskell
-- Language.Pilot.Repr

type Interpret (form :: Meta.Type domain -> Hask) f val = forall (x :: Meta.Type domain) .
  -- The `Rep` is a value-level representation of the type x.
  -- The `form` is a GADT constructor which represents the abstract form; it
  -- can use meta-language functions and products, as well as object-language
  -- types.
  Rep (Meta.Type domain) x -> form x -> Repr f val x

class Monad f => Interprets (form :: Meta.Type domain -> Hask) (f :: Hask -> Hask) (val :: domain -> Hask) where
  interp :: Interpret form f val
```

Why include meta-language functions, products, and terminal object in the
EDSL? Because if we have these things available, then we're able to talk about
applicative functors, even in an object-language which does not have functions.
Also, these are the ingredients of a
[Cartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category),
but enough about that.
