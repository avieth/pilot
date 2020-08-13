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
  ( Point_r (..)
  , Integer_r (..)
  , Bytes_r (..)
  , Any (..)
  , All (..)

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

import Prelude hiding (subtract, or, and, negate, abs, compare)

import qualified Data.Bits as Bits
import qualified Data.Int as Haskell
import qualified Data.Ord as Ord (compare)
import qualified Data.Word as Haskell

import Language.Pilot.Types
import Language.Pilot.Object (Width (..), Signedness (..))
import qualified Language.Pilot.Object as Object

data Integer_r signedness width where
  UInt8  :: Haskell.Word8  -> Integer_r 'Unsigned_t 'W_One_t
  UInt16 :: Haskell.Word16 -> Integer_r 'Unsigned_t 'W_Two_t
  UInt32 :: Haskell.Word32 -> Integer_r 'Unsigned_t 'W_Four_t
  UInt64 :: Haskell.Word64 -> Integer_r 'Unsigned_t 'W_Eight_t
  Int8  :: Haskell.Int8  -> Integer_r 'Signed_t 'W_One_t
  Int16 :: Haskell.Int16 -> Integer_r 'Signed_t 'W_Two_t
  Int32 :: Haskell.Int32 -> Integer_r 'Signed_t 'W_Four_t
  Int64 :: Haskell.Int64 -> Integer_r 'Signed_t 'W_Eight_t

data Bytes_r width where
  Word8  :: Haskell.Word8  -> Bytes_r 'W_One_t
  Word16 :: Haskell.Word16 -> Bytes_r 'W_Two_t
  Word32 :: Haskell.Word32 -> Bytes_r 'W_Four_t
  Word64 :: Haskell.Word64 -> Bytes_r 'W_Eight_t

data Any (f :: k -> Hask) (ts :: [k]) where
  Any :: f t -> Any f (t ': ts)
  Or  :: Any f ts -> Any f (t ': ts)

data All (f :: k -> Hask) (ts :: [k]) where
  All :: All f '[]
  And :: f t -> All f ts -> All f (t ': ts)

data Point_r (t :: Object.Point) where
  Integer_r :: Integer_r signedness width -> Point_r (Object.Integer_t signedness width)
  Bytes_r   :: Bytes_r width -> Point_r (Object.Bytes_t width)
  Sum_r     :: Any Point_r types -> Point_r (Object.Sum types)
  Product_r :: All Point_r types -> Point_r (Object.Product types)

prettyPrint :: Point_r t -> String
prettyPrint (Integer_r i) = prettyPrintInteger i
prettyPrint (Bytes_r b) = prettyPrintBytes b
prettyPrint (Sum_r v) = prettyPrintSum v
prettyPrint (Product_r fs) = prettyPrintProduct fs

-- TODO print them in hex, with a 0x prefix.
prettyPrintBytes :: Bytes_r w -> String
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

prettyPrintInteger :: Integer_r s w -> String
prettyPrintInteger (UInt8 w)  = show w ++ "u8"
prettyPrintInteger (UInt16 w) = show w ++ "u16"
prettyPrintInteger (UInt32 w) = show w ++ "u32"
prettyPrintInteger (UInt64 w) = show w ++ "u64"
prettyPrintInteger (Int8 i)  = show i ++ "i8"
prettyPrintInteger (Int16 i) = show i ++ "i16"
prettyPrintInteger (Int32 i) = show i ++ "i32"
prettyPrintInteger (Int64 i) = show i ++ "i64"

prettyPrintSum :: Any Point_r types -> String
prettyPrintSum v = mconcat
  [ "S["
  , prettyPrintVariant 0 v
  , "]"
  ]
  where
  prettyPrintVariant :: forall types . Int -> Any Point_r types -> String
  prettyPrintVariant n (Or any) = prettyPrintVariant (n+1) any
  prettyPrintVariant n (Any p)  = mconcat
    [ show n
    , " "
    , prettyPrint p
    ]

prettyPrintProduct :: All Point_r types -> String
prettyPrintProduct fs = mconcat
  [ "P["
  , prettyPrintFields fs
  , "]"
  ]
  where
  prettyPrintFields :: forall types . All Point_r types -> String
  prettyPrintFields All = ""
  prettyPrintFields (And p All) = mconcat ["(", prettyPrint p, ")"]
  prettyPrintFields (And p all) = mconcat ["(", prettyPrint p, "), "] ++ prettyPrintFields all

integer_f
  :: (forall n . Integral n => n -> n -> n)
  -> Integer_r s w
  -> Integer_r s w
  -> Integer_r s w
integer_f f (UInt8 x)  (UInt8 y)  = UInt8 (f x y)
integer_f f (UInt16 x) (UInt16 y) = UInt16 (f x y)
integer_f f (UInt32 x) (UInt32 y) = UInt32 (f x y)
integer_f f (UInt64 x) (UInt64 y) = UInt64 (f x y)
integer_f f (Int8 x)  (Int8 y)  = Int8  (f x y)
integer_f f (Int16 x) (Int16 y) = Int16 (f x y)
integer_f f (Int32 x) (Int32 y) = Int32 (f x y)
integer_f f (Int64 x) (Int64 y) = Int64 (f x y)

add :: Integer_r s w -> Integer_r s w -> Integer_r s w
add = integer_f (+)

subtract :: Integer_r s w -> Integer_r s w -> Integer_r s w
subtract = integer_f (\x y -> x - y)

multiply :: Integer_r s w -> Integer_r s w -> Integer_r s w
multiply = integer_f (*)

divide :: Integer_r s w -> Integer_r s w -> Integer_r s w
divide = integer_f div

modulo :: Integer_r s w -> Integer_r s w -> Integer_r s w
modulo = integer_f mod

negate :: Integer_r s w -> Integer_r s w
negate x = integer_f (\x _ -> (-x)) x x

abs :: Integer_r 'Signed_t w -> Integer_r 'Unsigned_t w
abs (Int8  i8)  = UInt8  (fromIntegral i8)
abs (Int16 i16) = UInt16 (fromIntegral i16)
abs (Int32 i32) = UInt32 (fromIntegral i32)
abs (Int64 i64) = UInt64 (fromIntegral i64)

compare :: Integer_r s w -> Integer_r s w -> Point_r Object.Cmp
compare (UInt8 x)  (UInt8 y)  = compare_ x y
compare (UInt16 x) (UInt16 y) = compare_ x y
compare (UInt32 x) (UInt32 y) = compare_ x y
compare (UInt64 x) (UInt64 y) = compare_ x y
compare (Int8 x)  (Int8 y)  = compare_ x y
compare (Int16 x) (Int16 y) = compare_ x y
compare (Int32 x) (Int32 y) = compare_ x y
compare (Int64 x) (Int64 y) = compare_ x y

compare_ :: Ord n => n -> n -> Point_r Object.Cmp
compare_ x y = case Ord.compare x y of
  LT -> Sum_r (Any (Product_r All))
  EQ -> Sum_r (Or (Any (Product_r All)))
  GT -> Sum_r (Or (Or (Any (Product_r All))))

bits_f
  :: (forall b . Bits.Bits b => b -> b -> b)
  -> Bytes_r w
  -> Bytes_r w
  -> Bytes_r w
bits_f f (Word8  x) (Word8  y) = Word8 (f x y)
bits_f f (Word16 x) (Word16 y) = Word16 (f x y)
bits_f f (Word32 x) (Word32 y) = Word32 (f x y)
bits_f f (Word64 x) (Word64 y) = Word64 (f x y)

or :: Bytes_r w -> Bytes_r w -> Bytes_r w
or = bits_f (Bits..|.)

and :: Bytes_r w -> Bytes_r w -> Bytes_r w
and = bits_f (Bits..&.)

xor :: Bytes_r w -> Bytes_r w -> Bytes_r w
xor = bits_f Bits.xor

complement :: Bytes_r w -> Bytes_r w
complement b = bits_f (\b _ -> Bits.complement b) b b

shiftl :: Bytes_r w -> Bytes_r 'W_One_t -> Bytes_r w
shiftl b (Word8 w8) = bits_f (\b _ -> Bits.shiftL b (fromIntegral w8)) b b

shiftr :: Bytes_r w -> Bytes_r 'W_One_t -> Bytes_r w
shiftr b (Word8 w8) = bits_f (\b _ -> Bits.shiftR b (fromIntegral w8)) b b
