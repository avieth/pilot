{-|
Module      : Language.Pilot.Interp.Pure.PrefixList
Description : Infinite lists with a type-indexed prefix size.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pilot.Interp.Pure.PrefixList
  ( PrefixList (..)
  , repeat
  , cycle
  , map
  , traverse
  , meld
  , fmeld
  , unmeld
  , toList
  , fromList
  , fromInit
  , tail
  , drop
  , shift
  , fromInitVec
  , fromInitVec_

  , splitPrefix
  , prettyPrint
  ) where

import Prelude hiding (repeat, map, zip, unzip, tail, drop, traverse, cycle)
import Data.List (intercalate)

import Language.Pilot.Types

data PrefixList (n :: Nat) (k :: domain -> Hask) (t :: domain) where
  Prefix :: k t -> PrefixList  n k t -> PrefixList ('S n) k t
  Suffix :: k t -> PrefixList 'Z k t -> PrefixList  'Z    k t

splitPrefix :: PrefixList n k t -> ([k t], [k t])
splitPrefix = go []
  where
  go :: forall n k t . [k t] -> PrefixList n k t -> ([k t], [k t])
  go ps (Prefix p next)     = go (p : ps) next
  go ps lst@(Suffix _ _)    = (Prelude.reverse ps, toList lst)

-- | Pretty print the list to at most a given number of suffix places, or
-- the whole thing (infinitely-long) if no limit is given.
prettyPrint :: Maybe Int -> (k t -> String) -> PrefixList n k t -> String
prettyPrint n k pl = mconcat [shownPrefix, " | ", shownSuffix]
  where
  (pre, suf) = splitPrefix pl
  suf' = maybe suf (flip Prelude.take suf) n
  shownPrefix = intercalate ", " (fmap k pre)
  shownSuffix = intercalate ", " (fmap k suf')

repeat :: NatRep n -> k t -> PrefixList n k t
repeat  Z_Rep    pt = Suffix pt (repeat Z_Rep pt)
repeat (S_Rep n) pt = Prefix pt (repeat n     pt)

cycle :: [k t] -> PrefixList 'Z k t
cycle ts = go ts
  where
  go []      = cycle ts
  go (t:ts') = Suffix t (go ts')

map
  :: (k t -> k' t')
  -> PrefixList n k  t
  -> PrefixList n k' t'
map f (Prefix x ps) = Prefix (f x) (map f ps)
map f (Suffix x ps) = Suffix (f x) (map f ps)

traverse
  :: ( Applicative f )
  => (k t -> f (k' t'))
  -> PrefixList n k t
  -> f (PrefixList n k' t')
traverse f (Prefix x ps) = Prefix <$> f x <*> traverse f ps
traverse f (Suffix x ps) = Suffix <$> f x <*> traverse f ps

{-
zip :: NatRep n -> P (PrefixList n k) ts -> PrefixList n (P k) ts
zip nrep U          = repeat nrep U
zip nrep (A pl pls) = meld A pl (zip nrep pls)

unzip :: PrefixList n (P k) ts -> P (PrefixList n k) ts
unzip (Prefix U _) = U
unzip (Suffix U _) = U
unzip p@(Prefix (A _ _) ps) = case unmeld (\(A c cs) -> (c, cs)) p of
  (ps, pss) -> A ps (unzip pss)
unzip p@(Suffix (A _ _) ps) = case unmeld (\(A c cs) -> (c, cs)) p of
  (ps, pss) -> A ps (unzip pss)
-}

meld
  :: (k s -> l t -> m u)
  -> PrefixList n k s
  -> PrefixList n l t
  -> PrefixList n m u
meld f (Prefix a as) (Prefix b bs) = Prefix (f a b) (meld f as bs)
meld f (Suffix a as) (Suffix b bs) = Suffix (f a b) (meld f as bs)

fmeld
  :: ( Applicative f )
  => (k s -> l t -> f (m u))
  -> PrefixList n k s
  -> PrefixList n l t
  -> f (PrefixList n m u)
fmeld f (Prefix a as) (Prefix b bs) = Prefix <$> f a b <*> fmeld f as bs
fmeld f (Suffix a as) (Suffix b bs) = Suffix <$> f a b <*> fmeld f as bs

unmeld
  :: (k s -> (l t, m u))
  -> PrefixList n k s
  -> (PrefixList n l t, PrefixList n m u)
unmeld f (Prefix a as) = (Prefix l ls, Prefix m ms)
  where
  (l,  m)  = f a
  (ls, ms) = unmeld f as
unmeld f (Suffix a as) = (Suffix l ls, Suffix m ms)
  where
  (l,  m)  = f a
  (ls, ms) = unmeld f as
-- NB: the following definition is not the same (is less lazy), but making
-- the case matches lazy (~) would fix it. I prefer the above since it does
-- not require the lazy matches.
{-
unmeld f (Prefix a as) = case (f a, unmeld f as) of
  ((l, m), (ls, ms)) -> (Prefix l ls,  Prefix m ms)
unmeld f (Suffix a as) = case (f a, unmeld f as) of
  ((l, m), (ls, ms)) -> (Suffix l ls, Suffix m ms)
-}

toList :: PrefixList n k t -> [k t]
toList (Prefix ft next) = ft : toList next
toList (Suffix ft next) = ft : toList next

-- | Not total. Will fail if you don't give an infinite list.
fromList :: NatRep n -> [k t] -> PrefixList n k t
fromList            _     [] = error "fromList: list is not infinite in length"
fromList       Z_Rep  (t:ts) = Suffix t (fromList Z_Rep ts)
fromList (S_Rep nrep) (t:ts) = Prefix t (fromList nrep ts)

-- | Like a mix of fromList and fromInitVec. It uses the entire list to fill
-- in the start of the list (not a prefix) and then repeats the second argument
-- forever.
fromInit :: [k t] -> k t -> PrefixList 'Z k t
fromInit []     x = repeat Z_Rep x
fromInit (t:ts) x = Suffix t (fromInit ts x)

tail :: PrefixList 'Z k t -> PrefixList 'Z k t
tail (Suffix _ next) = next

drop :: PrefixList ('S n) k t -> PrefixList n k t
drop (Prefix _ s) = s

-- TODO
-- This is not sufficiently lazy. We have to match on the tail in order to
-- figure out what to do next. Thus, these two forms
--
--   shift . fromInitVec v
--   fromInitVec' v
--
-- do not have the same strictness properties: the second one is more lazy.
shift :: PrefixList ('S n) k t -> PrefixList n k t
shift (Prefix t (Suffix t' ts))  = Suffix t (Suffix t' ts)
shift (Prefix t ts@(Prefix _ _)) = Prefix t (shift ts)

-- | Construct a stream using a given list of known prefix points.
fromInitVec :: Vec n (k t) -> PrefixList 'Z k t -> PrefixList n k t
fromInitVec VNil         suffix = suffix
fromInitVec (VCons t ts) suffix = Prefix t (fromInitVec ts suffix)

-- | Like 'fromInitVec' except that the final element of the vector
-- goes into the suffix of the stream, making it appear as though there is one
-- fewer known prefix element.
fromInitVec_ :: Vec (S n) (k t) -> PrefixList 'Z k t -> PrefixList n k t
fromInitVec_ (VCons t VNil)           suffix = Suffix t suffix
fromInitVec_ (VCons t ts@(VCons _ _)) suffix = Prefix t (fromInitVec_ ts suffix)
