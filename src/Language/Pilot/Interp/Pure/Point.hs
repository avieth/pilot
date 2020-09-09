{-|
Module      : Language.Pilot.Interp.Pure.Point
Description : Representation of the point domain in Haskell.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Interp.Pure.Point
  ( Point (..)
  , Integer (..)
  , Bytes (..)
  , Some (..)
  , All (..)

  , u8
  , u16
  , u32
  , u64
  , i8
  , i16
  , i32
  , i64

  , add
  , subtract
  , multiply
  , divide
  , modulo
  , negate
  , abs
  , compare

  , and
  , or
  , xor
  , complement
  , shiftl
  , shiftr

  , prettyPrint
  ) where

import Prelude hiding (Integer, subtract, or, and, negate, abs, compare)

import qualified Data.Bits as Bits
import qualified Data.Int as Haskell
import qualified Data.Ord as Ord (compare)
import qualified Data.Word as Haskell

import Language.Pilot.Types
import Language.Pilot.Object (Width (..), Signedness (..))
import qualified Language.Pilot.Object as Object
import qualified Language.Pilot.Object.Point as Object.Point

data Integer signedness width where
  UInt8  :: Haskell.Word8  -> Integer 'Unsigned_t 'W_One_t
  UInt16 :: Haskell.Word16 -> Integer 'Unsigned_t 'W_Two_t
  UInt32 :: Haskell.Word32 -> Integer 'Unsigned_t 'W_Four_t
  UInt64 :: Haskell.Word64 -> Integer 'Unsigned_t 'W_Eight_t
  Int8  :: Haskell.Int8  -> Integer 'Signed_t 'W_One_t
  Int16 :: Haskell.Int16 -> Integer 'Signed_t 'W_Two_t
  Int32 :: Haskell.Int32 -> Integer 'Signed_t 'W_Four_t
  Int64 :: Haskell.Int64 -> Integer 'Signed_t 'W_Eight_t

data Bytes width where
  Word8  :: Haskell.Word8  -> Bytes 'W_One_t
  Word16 :: Haskell.Word16 -> Bytes 'W_Two_t
  Word32 :: Haskell.Word32 -> Bytes 'W_Four_t
  Word64 :: Haskell.Word64 -> Bytes 'W_Eight_t

data Point (t :: Object.Point.Type) where
  Integer :: Integer signedness width -> Point (Object.Point.Integer_t signedness width)
  Bytes   :: Bytes width -> Point (Object.Point.Bytes_t width)
  Sum_r     :: Some Point types -> Point (Object.Sum types)
  Product_r :: All  Point types -> Point (Object.Product types)

prettyPrint :: Point t -> String
prettyPrint (Integer i) = prettyPrintInteger i
prettyPrint (Bytes b) = prettyPrintBytes b
prettyPrint (Sum_r v) = prettyPrintSum v
prettyPrint (Product_r fs) = prettyPrintProduct fs

-- TODO print them in hex, with a 0x prefix.
prettyPrintBytes :: Bytes w -> String
prettyPrintBytes (Word8 w)  = hex [w]
prettyPrintBytes (Word16 w) = hex
  [ fromIntegral (w `Bits.shiftR` 8)
  , fromIntegral w
  ]
prettyPrintBytes (Word32 w) = hex
  [ fromIntegral (w `Bits.shiftR` 24)
  , fromIntegral (w `Bits.shiftR` 16)
  , fromIntegral (w `Bits.shiftR` 8)
  , fromIntegral w
  ]
prettyPrintBytes (Word64 w) = hex
  [ fromIntegral (w `Bits.shiftR` 56)
  , fromIntegral (w `Bits.shiftR` 48)
  , fromIntegral (w `Bits.shiftR` 40)
  , fromIntegral (w `Bits.shiftR` 32)
  , fromIntegral (w `Bits.shiftR` 24)
  , fromIntegral (w `Bits.shiftR` 16)
  , fromIntegral (w `Bits.shiftR` 8)
  , fromIntegral w
  ]

hex :: [Haskell.Word8] -> String
hex ws = "0x" ++ concatMap hexDigits ws
  where
  hexDigits :: Haskell.Word8 -> String
  hexDigits w8 = [hexDigit hb, hexDigit lb]
    where 
    hb = w8 `Bits.shiftR` 4
    lb = w8 Bits..&. 0x0F
  -- Assumes it's in [0,15]
  hexDigit :: Haskell.Word8 -> Char
  hexDigit 0 = '0'
  hexDigit 1 = '1'
  hexDigit 2 = '2'
  hexDigit 3 = '3'
  hexDigit 4 = '4'
  hexDigit 5 = '5'
  hexDigit 6 = '6'
  hexDigit 7 = '7'
  hexDigit 8 = '8'
  hexDigit 9 = '9'
  hexDigit 10 = 'A'
  hexDigit 11 = 'B'
  hexDigit 12 = 'C'
  hexDigit 13 = 'D'
  hexDigit 14 = 'E'
  hexDigit 15 = 'F'
  hexDigit _ = error "doesn't happen"

prettyPrintInteger :: Integer s w -> String
prettyPrintInteger (UInt8 w)  = show w ++ "u8"
prettyPrintInteger (UInt16 w) = show w ++ "u16"
prettyPrintInteger (UInt32 w) = show w ++ "u32"
prettyPrintInteger (UInt64 w) = show w ++ "u64"
prettyPrintInteger (Int8 i)  = show i ++ "i8"
prettyPrintInteger (Int16 i) = show i ++ "i16"
prettyPrintInteger (Int32 i) = show i ++ "i32"
prettyPrintInteger (Int64 i) = show i ++ "i64"

prettyPrintSum :: Some Point types -> String
prettyPrintSum v = mconcat
  [ "S["
  , prettyPrintVariant 0 v
  , "]"
  ]
  where
  prettyPrintVariant :: forall types . Int -> Some Point types -> String
  prettyPrintVariant n (Or any) = prettyPrintVariant (n+1) any
  prettyPrintVariant n (Some p)  = mconcat
    [ show n
    , " "
    , prettyPrint p
    ]

prettyPrintProduct :: All Point types -> String
prettyPrintProduct fs = mconcat
  [ "P["
  , prettyPrintFields fs
  , "]"
  ]
  where
  prettyPrintFields :: forall types . All Point types -> String
  prettyPrintFields All = ""
  prettyPrintFields (And p All) = mconcat ["(", prettyPrint p, ")"]
  prettyPrintFields (And p all) = mconcat ["(", prettyPrint p, "), "] ++ prettyPrintFields all

u8 :: Haskell.Word8 -> Point ('Object.Point.Integer_t 'Unsigned_t 'W_One_t)
u8 w = Integer (UInt8 w)

u16 :: Haskell.Word16 -> Point ('Object.Point.Integer_t 'Unsigned_t 'W_Two_t)
u16 w = Integer (UInt16 w)

u32 :: Haskell.Word32 -> Point ('Object.Point.Integer_t 'Unsigned_t 'W_Four_t)
u32 w = Integer (UInt32 w)

u64 :: Haskell.Word64 -> Point ('Object.Point.Integer_t 'Unsigned_t 'W_Eight_t)
u64 w = Integer (UInt64 w)

i8 :: Haskell.Int8 -> Point ('Object.Point.Integer_t 'Signed_t 'W_One_t)
i8 w = Integer (Int8 w)

i16 :: Haskell.Int16 -> Point ('Object.Point.Integer_t 'Signed_t 'W_Two_t)
i16 w = Integer (Int16 w)

i32 :: Haskell.Int32 -> Point ('Object.Point.Integer_t 'Signed_t 'W_Four_t)
i32 w = Integer (Int32 w)

i64 :: Haskell.Int64 -> Point ('Object.Point.Integer_t 'Signed_t 'W_Eight_t)
i64 w = Integer (Int64 w)

integer_f
  :: (forall n . Integral n => n -> n -> n)
  -> Integer s w
  -> Integer s w
  -> Integer s w
integer_f f (UInt8 x)  (UInt8 y)  = UInt8 (f x y)
integer_f f (UInt16 x) (UInt16 y) = UInt16 (f x y)
integer_f f (UInt32 x) (UInt32 y) = UInt32 (f x y)
integer_f f (UInt64 x) (UInt64 y) = UInt64 (f x y)
integer_f f (Int8 x)  (Int8 y)  = Int8  (f x y)
integer_f f (Int16 x) (Int16 y) = Int16 (f x y)
integer_f f (Int32 x) (Int32 y) = Int32 (f x y)
integer_f f (Int64 x) (Int64 y) = Int64 (f x y)

add :: Point ('Object.Point.Integer_t s w)
    -> Point ('Object.Point.Integer_t s w)
    -> Point ('Object.Point.Integer_t s w)
add (Integer x) (Integer y) = Integer (integer_f (+) x y)

subtract :: Point ('Object.Point.Integer_t s w)
         -> Point ('Object.Point.Integer_t s w)
         -> Point ('Object.Point.Integer_t s w)
subtract (Integer x) (Integer y) = Integer (integer_f (\x y -> x - y) x y)

multiply :: Point ('Object.Point.Integer_t s w)
         -> Point ('Object.Point.Integer_t s w)
         -> Point ('Object.Point.Integer_t s w)
multiply (Integer x) (Integer y) = Integer (integer_f (*) x y)

divide :: Point ('Object.Point.Integer_t s w)
       -> Point ('Object.Point.Integer_t s w)
       -> Point ('Object.Point.Integer_t s w)
divide (Integer x) (Integer y) = Integer (integer_f div x y)

modulo :: Point ('Object.Point.Integer_t s w)
       -> Point ('Object.Point.Integer_t s w)
       -> Point ('Object.Point.Integer_t s w)
modulo (Integer x) (Integer y) = Integer (integer_f mod x y)

negate :: Point ('Object.Point.Integer_t s w) -> Point ('Object.Point.Integer_t s w)
negate (Integer x) = Integer (integer_f (\x _ -> (-x)) x x)

abs :: Point ('Object.Point.Integer_t 'Signed_t w) -> Point ('Object.Point.Integer_t 'Unsigned_t w)
abs (Integer (Int8  i8))  = Integer $ UInt8  (fromIntegral i8)
abs (Integer (Int16 i16)) = Integer $ UInt16 (fromIntegral i16)
abs (Integer (Int32 i32)) = Integer $ UInt32 (fromIntegral i32)
abs (Integer (Int64 i64)) = Integer $ UInt64 (fromIntegral i64)

compare :: Point r
        -> Point r
        -> Point r
        -> Point ('Object.Point.Integer_t s w)
        -> Point ('Object.Point.Integer_t s w)
        -> Point r
compare lt eq gt (Integer (UInt8 x))  (Integer (UInt8 y))  = compare_ lt eq gt x y
compare lt eq gt (Integer (UInt16 x)) (Integer (UInt16 y)) = compare_ lt eq gt x y
compare lt eq gt (Integer (UInt32 x)) (Integer (UInt32 y)) = compare_ lt eq gt x y
compare lt eq gt (Integer (UInt64 x)) (Integer (UInt64 y)) = compare_ lt eq gt x y
compare lt eq gt (Integer (Int8 x))  (Integer (Int8 y))  = compare_ lt eq gt x y
compare lt eq gt (Integer (Int16 x)) (Integer (Int16 y)) = compare_ lt eq gt x y
compare lt eq gt (Integer (Int32 x)) (Integer (Int32 y)) = compare_ lt eq gt x y
compare lt eq gt (Integer (Int64 x)) (Integer (Int64 y)) = compare_ lt eq gt x y

compare_ :: Ord n => r -> r -> r -> n -> n -> r
compare_ lt eq gt x y = case Ord.compare x y of
  LT -> lt
  EQ -> eq
  GT -> gt

bits_f
  :: (forall b . Bits.Bits b => b -> b -> b)
  -> Point ('Object.Point.Bytes_t w)
  -> Point ('Object.Point.Bytes_t w)
  -> Point ('Object.Point.Bytes_t w)
bits_f f (Bytes (Word8  x)) (Bytes (Word8  y)) = Bytes (Word8 (f x y))
bits_f f (Bytes (Word16 x)) (Bytes (Word16 y)) = Bytes (Word16 (f x y))
bits_f f (Bytes (Word32 x)) (Bytes (Word32 y)) = Bytes (Word32 (f x y))
bits_f f (Bytes (Word64 x)) (Bytes (Word64 y)) = Bytes (Word64 (f x y))

or :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w)
or = bits_f (Bits..|.)

and :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w)
and = bits_f (Bits..&.)

xor :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w)
xor = bits_f Bits.xor

complement :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t w)
complement b = bits_f (\b _ -> Bits.complement b) b b

shiftl :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t 'W_One_t) -> Point (Object.Point.Bytes_t w)
shiftl b (Bytes (Word8 w8)) = bits_f (\b _ -> Bits.shiftL b (fromIntegral w8)) b b

shiftr :: Point (Object.Point.Bytes_t w) -> Point (Object.Point.Bytes_t 'W_One_t) -> Point (Object.Point.Bytes_t w)
shiftr b (Bytes (Word8 w8)) = bits_f (\b _ -> Bits.shiftR b (fromIntegral w8)) b b
