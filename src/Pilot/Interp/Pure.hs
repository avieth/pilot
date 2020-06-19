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
  , streamExprToList
  , eval_point
  , eval_stream
  , stream_to_list
  ) where

import Data.Bits
import qualified Data.Int as Haskell
import qualified Data.Word as Haskell
import Data.List (intercalate)

import Pilot.EDSL.Expr
import qualified Pilot.EDSL.Point as Point
import Pilot.EDSL.Point (SignednessRep (..), UncheckedCast (..))
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Fun
import Pilot.Types.Logic
import Pilot.Types.Nat
import qualified Pilot.Types.Stream as Pure

streamExprToList
  :: Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream ('Stream.Stream n t)
  -> [Point t]
streamExprToList expr = streamToList (eval_stream expr)

data Point (t :: Point.Type) where

  UInt8  :: Haskell.Word8  -> Point ('Point.Integer 'Point.Unsigned 'Point.Eight)
  UInt16 :: Haskell.Word16 -> Point ('Point.Integer 'Point.Unsigned 'Point.Sixteen)
  UInt32 :: Haskell.Word32 -> Point ('Point.Integer 'Point.Unsigned 'Point.ThirtyTwo)
  UInt64 :: Haskell.Word64 -> Point ('Point.Integer 'Point.Unsigned 'Point.SixtyFour)
  Int8   :: Haskell.Int8   -> Point ('Point.Integer 'Point.Signed   'Point.Eight)
  Int16  :: Haskell.Int16  -> Point ('Point.Integer 'Point.Signed   'Point.Sixteen)
  Int32  :: Haskell.Int32  -> Point ('Point.Integer 'Point.Signed   'Point.ThirtyTwo)
  Int64  :: Haskell.Int64  -> Point ('Point.Integer 'Point.Signed   'Point.SixtyFour)

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

eval_point :: Expr Point.ExprF Point t -> Point t
eval_point = evalExpr eval_point_expr id eval_point_let_binding

eval_stream
  :: Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream t
  -> Stream t
eval_stream = evalExpr eval_stream_expr id eval_stream_let_binding

stream_to_list
  :: Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream ('Stream.Stream n t)
  -> [Point t]
stream_to_list expr = case eval_stream expr of
  Stream st -> Pure.streamToList st

eval_point_expr :: Point.ExprF (Expr Point.ExprF Point) t -> Point t

eval_point_expr (Point.IntroInteger _ lit)    = eval_point_literal lit

eval_point_expr (Point.PrimOp primop)         = eval_point_primop primop

eval_point_expr (Point.UncheckedCastOp _ _ s uc x) =
  eval_point_unchecked_castop s uc (eval_point x)

eval_point_expr (Point.CheckedCastOp _ _ _) = error "eval_point_expr not defined for CheckedCastOp"

eval_point_expr (Point.IntroProduct _ fields) = Product $
  mapAll eval_point fields

eval_point_expr (Point.IntroSum _ variant)    = Sum $
  mapAny eval_point variant

eval_point_expr (Point.ElimProduct _ p s)   = select s (eval_point p)
  where
  select :: Any f ts t -> Point ('Point.Product ts) -> Point t
  select (Any _) (Product (And t _)) = t
  select (Or s') (Product (And _ a)) = select s' (Product a)

eval_point_expr (Point.ElimSum _ _ s cs) = cases cs (eval_point s)
  where
  cases :: All (Point.Case (Expr Point.ExprF Point) r) variants
        -> Point ('Point.Sum variants)
        -> Point r
  -- To evaluate the case, we need to put the evaluated point back into the
  -- AST, as this is what the Haskell function giving the case branch expects.
  -- But we've already evaluated the thing, we wouldn't want to re-encode it
  -- in the DSL. No problem: use the "value" constructor of the AST.
  cases (And (Point.Case _ k) _) (Sum (Any t)) = eval_point (k (value t))
  cases (And _ cs)               (Sum (Or s))  = cases cs (Sum s)
  cases All                      (Sum s)       = case s of {}

eval_point_literal
  :: Point.IntegerLiteral signedness width
  -> Point ('Point.Integer signedness width)
eval_point_literal (Point.UInt8 w)  = UInt8 w
eval_point_literal (Point.UInt16 w) = UInt16 w
eval_point_literal (Point.UInt32 w) = UInt32 w
eval_point_literal (Point.UInt64 w) = UInt64 w
eval_point_literal (Point.Int8 w)   = Int8 w
eval_point_literal (Point.Int16 w)  = Int16 w
eval_point_literal (Point.Int32 w)  = Int32 w
eval_point_literal (Point.Int64 w)  = Int64 w

eval_point_primop
  :: Point.PrimOpF (Expr Point.ExprF Point) t
  -> Point t
eval_point_primop (Point.Arithmetic arithop) = eval_point_arithop arithop
eval_point_primop (Point.Bitwise bitop)      = eval_point_bitop bitop
eval_point_primop (Point.Relative relop)     = eval_point_relop relop

eval_point_arithop
  :: Point.ArithmeticOpF (Expr Point.ExprF Point) t
  -> Point t

eval_point_arithop (Point.AddInteger _ x y) = lift_integral_2 (+) vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_arithop (Point.SubInteger _ x y) = lift_integral_2 (-) vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_arithop (Point.MulInteger _ x y) = lift_integral_2 (*) vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_arithop (Point.DivInteger _ x y) = lift_integral_2 div vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_arithop (Point.ModInteger _ x y) = lift_integral_2 mod vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_arithop (Point.NegInteger _ x) = lift_integral_1 negate (eval_point x)

eval_point_bitop
  :: Point.BitwiseOpF (Expr Point.ExprF Point) t
  -> Point t

eval_point_bitop (Point.AndB _ x y) = lift_bits_2 (.&.) vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_bitop (Point.OrB _ x y) = lift_bits_2 (.|.) vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_bitop (Point.XOrB _ x y) = lift_bits_2 xor vx vy
  where
  vx = eval_point x
  vy = eval_point y

eval_point_bitop (Point.NotB _ x) = lift_bits_1 complement (eval_point x)

eval_point_bitop (Point.ShiftR _ x y) = lift_bits_1 (flip shiftR i) vx
  where
  vx = eval_point x
  vy = eval_point y
  i  = case vy of { UInt8 w -> fromIntegral w }

eval_point_bitop (Point.ShiftL _ x y) = lift_bits_1 (flip shiftL i) vx
  where
  vx = eval_point x
  vy = eval_point y
  i  = case vy of { UInt8 w -> fromIntegral w }

eval_point_relop
  :: Point.RelativeOpF (Expr Point.ExprF Point) t
  -> Point t
eval_point_relop (Point.Cmp _ _ x y cLT cEQ cGT) = case cmp vx vy of
  LT -> eval_point cLT
  EQ -> eval_point cEQ
  GT -> eval_point cGT

  where

  vx = eval_point x
  vy = eval_point y

  cmp :: Point ('Point.Integer s w) -> Point ('Point.Integer s w) -> Ordering
  cmp (UInt8  x) (UInt8  y) = compare x y
  cmp (UInt16 x) (UInt16 y) = compare x y
  cmp (UInt32 x) (UInt32 y) = compare x y
  cmp (UInt64 x) (UInt64 y) = compare x y
  cmp (Int8  x) (Int8  y) = compare x y
  cmp (Int16 x) (Int16 y) = compare x y
  cmp (Int32 x) (Int32 y) = compare x y
  cmp (Int64 x) (Int64 y) = compare x y

eval_point_unchecked_castop
  :: Point.SignednessRep signedness
  -> Point.UncheckedCast w1 w2
  -> Point ('Point.Integer signedness w1)
  -> Point ('Point.Integer signedness w2)

eval_point_unchecked_castop Unsigned_t Cast_Unchecked_Eight_Sixteen (UInt8 w8) =
  UInt16 (fromIntegral w8)
eval_point_unchecked_castop Unsigned_t Cast_Unchecked_Eight_ThirtyTwo (UInt8 w8) =
  UInt32 (fromIntegral w8)
eval_point_unchecked_castop Unsigned_t Cast_Unchecked_Eight_SixtyFour (UInt8 w8) =
  UInt64 (fromIntegral w8)

eval_point_unchecked_castop Unsigned_t Cast_Unchecked_Sixteen_ThirtyTwo (UInt16 w16) =
  UInt32 (fromIntegral w16)
eval_point_unchecked_castop Unsigned_t Cast_Unchecked_Sixteen_SixtyFour (UInt16 w16) =
  UInt64 (fromIntegral w16)

eval_point_unchecked_castop Unsigned_t Cast_Unchecked_ThirtyTwo_SixtyFour (UInt32 w32) =
  UInt64 (fromIntegral w32)

eval_point_unchecked_castop Signed_t Cast_Unchecked_Eight_Sixteen (Int8 i8) =
  Int16 (fromIntegral i8)
eval_point_unchecked_castop Signed_t Cast_Unchecked_Eight_ThirtyTwo (Int8 i8) =
  Int32 (fromIntegral i8)
eval_point_unchecked_castop Signed_t Cast_Unchecked_Eight_SixtyFour (Int8 i8) =
  Int64 (fromIntegral i8)

eval_point_unchecked_castop Signed_t Cast_Unchecked_Sixteen_ThirtyTwo (Int16 i16) =
  Int32 (fromIntegral i16)
eval_point_unchecked_castop Signed_t Cast_Unchecked_Sixteen_SixtyFour (Int16 i16) =
  Int64 (fromIntegral i16)

eval_point_unchecked_castop Signed_t Cast_Unchecked_ThirtyTwo_SixtyFour (Int32 i32) =
  Int64 (fromIntegral i32)

eval_stream_expr
  :: forall t .
     Stream.ExprF
       (Expr Point.ExprF Point)
       (Expr Point.ExprF Point)
       (Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream)
       t
  -> Stream t

eval_stream_expr (Stream.ConstantStream _ nrep expr) = Stream $
  Pure.streamRepeat nrep (eval_point expr)

eval_stream_expr (Stream.LiftStream argsrep _ nrep f args) = Stream $
  Pure.streamMap eval_point s

  where

  evaldArgs = mapArgs eval_stream args
  q = make_args argsrep evaldArgs
  s = Pure.streamApply nrep f q

  make_args
    :: forall proxy args m .
       Args proxy args
    -> Args Stream (MapArgs ('Stream.Stream m) args)
    -> Args (Pure.Stream (Expr Point.ExprF Point) m) args
  make_args Args            Args                   = Args
  make_args (Arg _ argsrep) (Arg (Stream st) args) = Arg
    -- Here, as in case elimination for points, we put the already-evaluated
    -- points back into the AST by way of the "extra" part.
    (Pure.streamMap value st)
    (make_args argsrep args)

eval_stream_expr (Stream.DropStream _ nrep expr) = case eval_stream expr of
  Stream str -> Stream $ Pure.streamDrop str

eval_stream_expr (Stream.ShiftStream _ nrep expr) = case eval_stream expr of
  Stream str -> Stream $ Pure.streamShift str

eval_stream_expr (Stream.MemoryStream (_ :: Point.TypeRep s) (_ :: NatRep ('S m)) inits k) =
  Stream stream

  where

  pts = vecMap eval_point inits

  suffix :: Pure.Stream Point 'Z s
  suffix = case eval_stream (k (value (Stream shifted))) of
    Stream s -> s

  -- The continuation `k` does not get access to the full prefix, we need to
  -- shift. Using streamShift or streamDrop does not work though, because
  -- these aren't sufficiently lazy. Instead, streamFromInitVec' will
  -- do what streamFromInitVec does but will include the final point in
  -- the suffix.
  shifted :: Pure.Stream Point m s
  shifted = Pure.streamFromInitVec' pts suffix

  stream :: Pure.Stream Point ('S m) s
  stream = Pure.streamFromInitVec pts suffix

eval_point_let_binding
  ::  Expr Point.ExprF Point x
  -> (Expr Point.ExprF Point x -> Expr Point.ExprF Point t)
  -> Point t
eval_point_let_binding x k = eval_point (k x)

eval_stream_let_binding
  ::  Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream x
  -> (Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream x ->
      Expr (Stream.ExprF (Expr Point.ExprF Point) (Expr Point.ExprF Point)) Stream t)
  -> Stream t
eval_stream_let_binding x k = eval_stream (k x)
