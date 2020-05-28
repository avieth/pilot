{-|
Module      : Pilot.Interp.Pure
Description : The "pure" interpretation of the stream and point EDSLs.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneDeriving #-}

module Pilot.Interp.Pure
  ( Point (..)
  , Stream (..)
  , F
  , streamExprToList
  , eval_point
  , eval_point_
  , eval_stream
  , eval_stream_
  , stream_to_list
  ) where

import Data.Bits
import qualified Data.Int as Haskell
import qualified Data.Word as Haskell
import Data.Functor.Identity
import Data.List (intercalate)

import Pilot.EDSL.Expr
import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Fun
import Pilot.Types.Logic
import Pilot.Types.Nat
import qualified Pilot.Types.Stream as Pure

streamExprToList
  :: Expr (Stream.ExprF (Expr Point.ExprF Point F) (Expr Point.ExprF Point F)) Stream F ('Stream.Stream n t)
  -> [Point t]
streamExprToList expr = streamToList (eval_stream_ expr)

data Point (t :: Point.Type) where

  UInt8  :: Haskell.Word8  -> Point ('Point.Integer 'Point.Unsigned 'Point.Eight)
  UInt16 :: Haskell.Word16 -> Point ('Point.Integer 'Point.Unsigned 'Point.Sixteen)
  UInt32 :: Haskell.Word32 -> Point ('Point.Integer 'Point.Unsigned 'Point.ThirtyTwo)
  UInt64 :: Haskell.Word64 -> Point ('Point.Integer 'Point.Unsigned 'Point.SixtyFour)
  Int8   :: Haskell.Int8   -> Point ('Point.Integer 'Point.Signed 'Point.Eight)
  Int16  :: Haskell.Int16  -> Point ('Point.Integer 'Point.Signed 'Point.Sixteen)
  Int32  :: Haskell.Int32  -> Point ('Point.Integer 'Point.Signed 'Point.ThirtyTwo)
  Int64  :: Haskell.Int64  -> Point ('Point.Integer 'Point.Signed 'Point.SixtyFour)

  Product :: All Point ts   -> Point ('Point.Product ts)
  Sum     :: Any Point ts x -> Point ('Point.Sum ts)

instance Show (Point t) where
  show (UInt8 w)  = show w ++ "u8"
  show (UInt16 w) = show w ++ "u16"
  show (UInt32 w) = show w ++ "u32"
  show (UInt64 w) = show w ++ "u64"
  show (Int8 i)   = show i ++ "i8"
  show (Int16 i)  = show i ++ "i16"
  show (Int32 i)  = show i ++ "i32"
  show (Int64 i)  = show i ++ "i64"
  show (Product fields) = "(" ++ intercalate " x " (allToList show fields) ++ ")"
  show (Sum variant)    = "[" ++ anyToOne (\n s -> show n ++ " " ++ show s) variant ++ "]"

lift_integral_1
  :: (forall n . Integral n => n -> n)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
lift_integral_1 f x = lift_integral_2 g x x
  where
  g :: forall n . Integral n => n -> n -> n
  g _ y = f y

lift_integral_2
  :: (forall n . Integral n => n -> n -> n)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
lift_integral_2 f (UInt8  x) (UInt8  y) = UInt8  $ f x y
lift_integral_2 f (UInt16 x) (UInt16 y) = UInt16 $ f x y
lift_integral_2 f (UInt32 x) (UInt32 y) = UInt32 $ f x y
lift_integral_2 f (UInt64 x) (UInt64 y) = UInt64 $ f x y
lift_integral_2 f (Int8  x)  (Int8  y)  = Int8   $ f x y
lift_integral_2 f (Int16 x)  (Int16 y)  = Int16  $ f x y
lift_integral_2 f (Int32 x)  (Int32 y)  = Int32  $ f x y
lift_integral_2 f (Int64 x)  (Int64 y)  = Int64  $ f x y

lift_bits_1
  :: (forall n . Bits n => n -> n)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
lift_bits_1 f x = lift_bits_2 g x x
  where
  g :: forall n . Bits n => n -> n -> n
  g _ y = f y

lift_bits_2
  :: (forall n . Bits n => n -> n -> n)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
  -> Point ('Point.Integer s w)
lift_bits_2 f (UInt8  x) (UInt8  y) = UInt8  $ f x y
lift_bits_2 f (UInt16 x) (UInt16 y) = UInt16 $ f x y
lift_bits_2 f (UInt32 x) (UInt32 y) = UInt32 $ f x y
lift_bits_2 f (UInt64 x) (UInt64 y) = UInt64 $ f x y
lift_bits_2 f (Int8  x)  (Int8  y)  = Int8   $ f x y
lift_bits_2 f (Int16 x)  (Int16 y)  = Int16  $ f x y
lift_bits_2 f (Int32 x)  (Int32 y)  = Int32  $ f x y
lift_bits_2 f (Int64 x)  (Int64 y)  = Int64  $ f x y

data Stream (t :: Stream.Type Point.Type) where
  Stream   :: Pure.Stream Point n t -> Stream ('Stream.Stream n t)

streamToList :: Stream ('Stream.Stream n t) -> [Point t]
streamToList (Stream stream) = Pure.streamToList stream

type F = Identity

eval_point_bind :: Point t -> F (Point t)
eval_point_bind = pure

eval_stream_bind :: Stream t -> F (Stream t)
eval_stream_bind = pure

eval_point :: Expr Point.ExprF Point F t -> F (Point t)
eval_point = evalExprM eval_point_expr eval_point_bind . runExpr

eval_point_ :: Expr Point.ExprF Point F t -> Point t
eval_point_ = runIdentity . eval_point

eval_stream
  :: Expr (Stream.ExprF (Expr Point.ExprF Point F) (Expr Point.ExprF Point F)) Stream F t
  -> F (Stream t)
eval_stream = evalExprM eval_stream_expr eval_stream_bind . runExpr

eval_stream_
  :: Expr (Stream.ExprF (Expr Point.ExprF Point F) (Expr Point.ExprF Point F)) Stream F t
  -> Stream t
eval_stream_ = runIdentity . eval_stream

stream_to_list
  :: Expr (Stream.ExprF (Expr Point.ExprF Point F) (Expr Point.ExprF Point F)) Stream F ('Stream.Stream n t)
  -> [Point t]
stream_to_list expr = case runIdentity (eval_stream expr) of
  Stream st -> Pure.streamToList st

eval_point_expr :: Point.ExprF (Expr Point.ExprF Point F) t -> F (Point t)

eval_point_expr (Point.IntroInteger _ lit)    = eval_point_literal lit

eval_point_expr (Point.PrimOp primop)         = eval_point_primop primop

eval_point_expr (Point.IntroProduct _ fields) = fmap Product $
  traverseAll eval_point fields

eval_point_expr (Point.IntroSum _ _ variant)  = fmap Sum $
  traverseAny eval_point variant

eval_point_expr (Point.ElimProduct _ _ s p)   = fmap (select s) (eval_point p)
  where
  select :: Any f ts t -> Point ('Point.Product ts) -> Point t
  select (Any _) (Product (And t _)) = t
  select (Or s') (Product (And _ a)) = select s' (Product a)

eval_point_expr (Point.ElimSum _ _ s cs) = eval_point s >>= cases cs
  where
  cases :: All (Point.Case (Expr Point.ExprF Point F) r) variants
        -> Point ('Point.Sum variants)
        -> F (Point r)
  cases (And _ cs)               (Sum (Or s))  = cases cs (Sum s)
  cases (And (Point.Case _ k) _) (Sum (Any t)) = eval_point (k (knownValue t))
  cases All                      (Sum s)       = case s of {}

eval_point_literal :: Point.IntegerLiteral signedness width -> F (Point ('Point.Integer signedness width))
eval_point_literal (Point.UInt8 w)  = pure $ UInt8 w
eval_point_literal (Point.UInt16 w) = pure $ UInt16 w
eval_point_literal (Point.UInt32 w) = pure $ UInt32 w
eval_point_literal (Point.UInt64 w) = pure $ UInt64 w
eval_point_literal (Point.Int8 w)   = pure $ Int8 w
eval_point_literal (Point.Int16 w)  = pure $ Int16 w
eval_point_literal (Point.Int32 w)  = pure $ Int32 w
eval_point_literal (Point.Int64 w)  = pure $ Int64 w

eval_point_primop :: Point.PrimOpF (Expr Point.ExprF Point F) t -> F (Point t)
eval_point_primop (Point.Arithmetic arithop) = eval_point_arithop arithop
eval_point_primop (Point.Bitwise bitop) = eval_point_bitop bitop
eval_point_primop (Point.Relative relop) = eval_point_relop relop

eval_point_arithop :: Point.ArithmeticOpF (Expr Point.ExprF Point F) t -> F (Point t)

eval_point_arithop (Point.AddInteger _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_integral_2 (+) vx vy

eval_point_arithop (Point.SubInteger _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_integral_2 (-) vx vy

eval_point_arithop (Point.MulInteger _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_integral_2 (*) vx vy

eval_point_arithop (Point.DivInteger _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_integral_2 div vx vy

eval_point_arithop (Point.ModInteger _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_integral_2 mod vx vy

eval_point_arithop (Point.NegInteger _ x) = do
  vx <- eval_point x
  pure $ lift_integral_1 negate vx

eval_point_bitop :: Point.BitwiseOpF (Expr Point.ExprF Point F) t -> F (Point t)

eval_point_bitop (Point.AndB _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_bits_2 (.&.) vx vy

eval_point_bitop (Point.OrB _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_bits_2 (.|.) vx vy

eval_point_bitop (Point.XOrB _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  pure $ lift_bits_2 xor vx vy

eval_point_bitop (Point.NotB _ x) = do
  vx <- eval_point x
  pure $ lift_bits_1 complement vx

eval_point_bitop (Point.ShiftR _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  let i = case vy of { UInt8 w -> fromIntegral w }
  pure $ lift_bits_1 (flip shiftR i) vx

eval_point_bitop (Point.ShiftL _ x y) = do
  vx <- eval_point x
  vy <- eval_point y
  let i = case vy of { UInt8 w -> fromIntegral w }
  pure $ lift_bits_1 (flip shiftL i) vx

eval_point_relop :: Point.RelativeOpF (Expr Point.ExprF Point F) t -> F (Point t)
eval_point_relop (Point.Cmp _ _ x y cLT cEQ cGT) = do
  vx <- eval_point x
  vy <- eval_point y
  case cmp vx vy of
    LT -> eval_point cLT
    EQ -> eval_point cEQ
    GT -> eval_point cGT
  where
  cmp :: Point ('Point.Integer s w) -> Point ('Point.Integer s w) -> Ordering
  cmp (UInt8  x) (UInt8  y) = compare x y
  cmp (UInt16 x) (UInt16 y) = compare x y
  cmp (UInt32 x) (UInt32 y) = compare x y
  cmp (UInt64 x) (UInt64 y) = compare x y
  cmp (Int8  x) (Int8  y) = compare x y
  cmp (Int16 x) (Int16 y) = compare x y
  cmp (Int32 x) (Int32 y) = compare x y
  cmp (Int64 x) (Int64 y) = compare x y

eval_stream_expr
  :: forall t .
     Stream.ExprF
       (Expr Point.ExprF Point F)
       (Expr Point.ExprF Point F)
       (Expr (Stream.ExprF (Expr Point.ExprF Point F) (Expr Point.ExprF Point F)) Stream F)
       t
  -> F (Stream t)

eval_stream_expr (Stream.ConstantStream _ nrep expr) = do
  point <- eval_point expr
  pure $ Stream $ Pure.streamRepeat nrep point

eval_stream_expr (Stream.LiftStream argsrep _ nrep f args) = do
  evaldArgs <- traverseArgs eval_stream args
  let q = make_args argsrep evaldArgs
      s = Pure.streamApply nrep f q
  pure $ Stream $ Pure.streamMap (runIdentity . eval_point) s

  where

  make_args
    :: forall proxy args m .
       Args proxy args
    -> Args Stream (MapArgs ('Stream.Stream m) args)
    -> Args (Pure.Stream (Expr Point.ExprF Point F) m) args
  make_args (Arg _ argsrep) (Arg (Stream st) args) = Arg
    (Pure.streamMap knownValue st) (make_args argsrep args)
  make_args Args            Args                   = Args

eval_stream_expr (Stream.DropStream _ nrep expr) = do
  str <- eval_stream expr
  case str of
    Stream str -> pure $ Stream $ Pure.streamDrop str

eval_stream_expr (Stream.ShiftStream _ nrep expr) = do
  str <- eval_stream expr
  case str of
    Stream str -> pure $ Stream $ Pure.streamShift str

eval_stream_expr (Stream.MemoryStream (_ :: Point.TypeRep s) (_ :: NatRep ('S m)) inits k) = do
  pts <- vecTraverse eval_point inits
  let suffix :: Pure.Stream Point 'Z s
      suffix = case runIdentity (eval_stream (k (knownValue (Stream shifted)))) of
        Stream s -> s
      stream :: Pure.Stream Point ('S m) s
      stream = Pure.streamFromInitVec pts suffix
      -- The continuation `k` does not get access to the full prefix, we need to
      -- shift. Using streamShift or streamDrop does not work though, because
      -- these aren't sufficiently lazy. Instead, streamFromInitVec' will
      -- do what streamFromInitVec does but will include the final point in
      -- the suffix.
      shifted :: Pure.Stream Point m s
      shifted = Pure.streamFromInitVec' pts suffix
  pure $ Stream $ stream
