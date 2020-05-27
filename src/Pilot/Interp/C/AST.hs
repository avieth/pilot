{-|
Module      : Pilot.Interp.C.AST
Description : Utilities for working with the C AST library.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.Interp.C.AST where

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Numeric.Natural (Natural)

import Language.C99.AST as C

-- | Put a reference unary op onto an expression.
reference :: C.CondExpr -> C.CondExpr
reference cexpr = unaryExprIsCondExpr $
  C.UnaryOp C.UORef (condExprIsCastExpr cexpr)

-- | Put a dereference unary op onto an expression.
dereference :: C.CondExpr -> C.CondExpr
dereference cexpr = unaryExprIsCondExpr $
  C.UnaryOp C.UODeref (condExprIsCastExpr cexpr)

-- | Apply as many dereference operators to strip all pointers.
dereferenceAll :: Maybe C.Ptr -> C.CondExpr -> C.CondExpr
dereferenceAll Nothing                  expr = expr
dereferenceAll (Just (C.PtrBase _))     expr = dereference expr
dereferenceAll (Just (C.PtrCons _ ptr)) expr = dereference (dereferenceAll (Just ptr) expr)

dereferenceIf :: Bool -> C.CondExpr -> C.CondExpr
dereferenceIf False = id
dereferenceIf True  = dereference

condExprIsAddExpr :: C.CondExpr -> C.AddExpr
condExprIsAddExpr = C.AddMult . condExprIsMultExpr

condExprIsMultExpr :: C.CondExpr -> C.MultExpr
condExprIsMultExpr = C.MultCast . C.CastUnary . C.UnaryPostfix . C.PostfixPrim .
  C.PrimExpr . C.ExprAssign . C.AssignCond

condExprIsAndExpr :: C.CondExpr -> C.AndExpr
condExprIsAndExpr = C.AndEq . condExprIsEqExpr

condExprIsXOrExpr :: C.CondExpr -> C.XOrExpr
condExprIsXOrExpr = C.XOrAnd . condExprIsAndExpr

condExprIsOrExpr :: C.CondExpr -> C.OrExpr
condExprIsOrExpr = C.OrXOr . condExprIsXOrExpr

condExprIsEqExpr :: C.CondExpr -> C.EqExpr
condExprIsEqExpr = C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimExpr . condExprIsExpr

condExprIsShiftExpr :: C.CondExpr -> C.ShiftExpr
condExprIsShiftExpr = C.ShiftAdd . condExprIsAddExpr

condExprIsRelExpr :: C.CondExpr -> C.RelExpr
condExprIsRelExpr = C.RelShift . condExprIsShiftExpr

condExprIsLAndExpr :: C.CondExpr -> C.LAndExpr
condExprIsLAndExpr = C.LAndOr . condExprIsOrExpr

condExprIsLOrExpr :: C.CondExpr -> C.LOrExpr
condExprIsLOrExpr = C.LOrAnd . condExprIsLAndExpr

addExprIsCondExpr :: C.AddExpr -> C.CondExpr
addExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd

addExprIsMultExpr :: C.AddExpr -> C.MultExpr
addExprIsMultExpr = condExprIsMultExpr . addExprIsCondExpr

multExprIsExpr :: C.MultExpr -> C.Expr
multExprIsExpr = C.ExprAssign . C.AssignCond . multExprIsCondExpr

multExprIsCondExpr :: C.MultExpr -> C.CondExpr
multExprIsCondExpr = addExprIsCondExpr . multExprIsAddExpr

multExprIsAddExpr :: C.MultExpr -> C.AddExpr
multExprIsAddExpr = C.AddMult

multExprIsAssignExpr :: C.MultExpr -> C.AssignExpr
multExprIsAssignExpr = condExprIsAssignExpr . addExprIsCondExpr . C.AddMult

lorExprIsCondExpr :: C.LOrExpr -> C.CondExpr
lorExprIsCondExpr = C.CondLOr

landExprIsCondExpr :: C.LAndExpr -> C.CondExpr
landExprIsCondExpr = lorExprIsCondExpr . C.LOrAnd

orExprIsCondExpr :: C.OrExpr -> C.CondExpr
orExprIsCondExpr = landExprIsCondExpr . C.LAndOr

xorExprIsCondExpr :: C.XOrExpr -> C.CondExpr
xorExprIsCondExpr = orExprIsCondExpr . C.OrXOr

andExprIsCondExpr :: C.AndExpr -> C.CondExpr
andExprIsCondExpr = xorExprIsCondExpr . C.XOrAnd

shiftExprIsCondExpr :: C.ShiftExpr -> C.CondExpr
shiftExprIsCondExpr = relExprIsCondExpr . C.RelShift

relExprIsCondExpr :: C.RelExpr -> C.CondExpr
relExprIsCondExpr = eqExprIsCondExpr . C.EqRel

eqExprIsCondExpr :: C.EqExpr -> C.CondExpr
eqExprIsCondExpr = andExprIsCondExpr . C.AndEq

eqExprIsLOrExpr :: C.EqExpr -> C.LOrExpr
eqExprIsLOrExpr = C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd . C.AndEq

relExprIsLOrExpr :: C.RelExpr -> C.LOrExpr
relExprIsLOrExpr = eqExprIsLOrExpr . C.EqRel

identIsConstExpr :: C.Ident -> C.ConstExpr
identIsConstExpr = C.Const . identIsCondExpr

identIsExpr :: C.Ident -> C.Expr
identIsExpr = condExprIsExpr . identIsCondExpr

identIsCondExpr :: C.Ident -> C.CondExpr
identIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

identIsAssignExpr :: C.Ident -> C.AssignExpr
identIsAssignExpr = condExprIsAssignExpr . identIsCondExpr

identIsRelExpr :: C.Ident -> C.RelExpr
identIsRelExpr = C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

identIsUnaryExpr :: C.Ident -> C.UnaryExpr
identIsUnaryExpr = C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

identIsPostfixExpr :: C.Ident -> C.PostfixExpr
identIsPostfixExpr = condExprIsPostfixExpr . identIsCondExpr

identIsAddExpr :: C.Ident -> C.AddExpr
identIsAddExpr = C.AddMult . C.MultCast . C.CastUnary . identIsUnaryExpr

postfixExprIsCondExpr :: C.PostfixExpr -> C.CondExpr
postfixExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix

postfixExprIsUnaryExpr :: C.PostfixExpr -> C.UnaryExpr
postfixExprIsUnaryExpr = C.UnaryPostfix

postfixExprIsAssignExpr :: C.PostfixExpr -> C.AssignExpr
postfixExprIsAssignExpr = C.AssignCond . postfixExprIsCondExpr

postfixExprIsExpr :: C.PostfixExpr -> C.Expr
postfixExprIsExpr = C.ExprAssign . C.AssignCond . postfixExprIsCondExpr

postfixExprIsEqExpr :: C.PostfixExpr -> C.EqExpr
postfixExprIsEqExpr = C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult .
  C.MultCast . C.CastUnary . C.UnaryPostfix

primExprIsCondExpr :: C.PrimExpr -> C.CondExpr
primExprIsCondExpr = postfixExprIsCondExpr . primExprIsPostfixExpr

primExprIsPostfixExpr :: C.PrimExpr -> C.PostfixExpr
primExprIsPostfixExpr = C.PostfixPrim

condExprIsAssignExpr :: C.CondExpr -> C.AssignExpr
condExprIsAssignExpr = C.AssignCond

condExprIsExpr :: C.CondExpr -> C.Expr
condExprIsExpr = C.ExprAssign . C.AssignCond

condExprIsPostfixExpr :: C.CondExpr -> C.PostfixExpr
condExprIsPostfixExpr = C.PostfixPrim . C.PrimExpr . C.ExprAssign . C.AssignCond

condExprIsCastExpr :: C.CondExpr -> C.CastExpr
condExprIsCastExpr = C.CastUnary . C.UnaryPostfix . condExprIsPostfixExpr

postfixExprIsCastExpr :: C.PostfixExpr -> C.CastExpr
postfixExprIsCastExpr = C.CastUnary . C.UnaryPostfix

constIsCondExpr :: C.Const -> C.CondExpr
constIsCondExpr = postfixExprIsCondExpr . C.PostfixPrim . C.PrimConst

constIsCastExpr :: C.Const -> C.CastExpr
constIsCastExpr = C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimConst

constIsAssignExpr :: C.Const -> C.AssignExpr
constIsAssignExpr = condExprIsAssignExpr . constIsCondExpr

constIsMultExpr :: C.Const -> C.MultExpr
constIsMultExpr = C.MultCast . constIsCastExpr

constIsAddExpr :: C.Const -> C.AddExpr
constIsAddExpr = C.AddMult . C.MultCast . constIsCastExpr

unaryExprIsCondExpr :: C.UnaryExpr -> C.CondExpr
unaryExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary

ident_designator :: C.Ident -> C.Design
ident_designator = C.Design . C.DesigrBase . C.DesigrIdent

-- | const and restrict qualifiers. Used for initialzied bindings to pointer
-- types.
const_restrict :: C.TypeQualList
const_restrict = C.TypeQualCons
  (C.TypeQualBase C.QConst)
  C.QRestrict

-- | Make a const restrict pointer to something by prepending *const restrict.
const_restrict_ptr_to :: Maybe C.Ptr -> C.Ptr
const_restrict_ptr_to Nothing    = C.PtrBase $ Just const_restrict
const_restrict_ptr_to (Just ptr) = C.PtrCons (Just const_restrict) ptr

-- | All numbers are put out in hex. C decimals are just harder to work with,
-- since 0 is not a decimal number, but rather an octal one.
hex_const :: Natural -> C.HexConst
hex_const = hexConst . hexDigits

assertValidStringIdentifier :: String -> C.Ident
assertValidStringIdentifier str = case stringIdentifier str of
  Nothing -> error ("assertValidStringIdentifier: bad identifier " ++ str)
  Just id -> id

assertValidIdentifier :: String -> Maybe C.Ident -> C.Ident
assertValidIdentifier msg Nothing  = error msg
assertValidIdentifier _   (Just i) = i

assertValidDesignator :: String -> String -> C.Design
assertValidDesignator msg str =
  let !ident = assertValidIdentifier msg (stringIdentifier str)
  in  C.Design $ C.DesigrBase $ C.DesigrIdent ident

-- | Make a C identifier from a string. Will fail if the string is malformed
-- w.r.t. valid C identifiers.
stringIdentifier :: String -> Maybe C.Ident
stringIdentifier []       = Nothing
stringIdentifier (c : cs) = go (NE.reverse (c NE.:| cs))
  where
  go :: NonEmpty Char -> Maybe C.Ident
  -- First character (end of list) must not be a digit).
  go (c' NE.:| []) = fmap (C.IdentBase . C.IdentNonDigit) (cNonDigit c')
  -- Any other character (not the first) can be a digit or non digit.
  go (c' NE.:| (d : cs')) =
    let !it = cDigitOrNonDigit c'
    in  case it of
          Nothing -> Nothing
          Just (Left digit) ->
            let !mRest = go (d NE.:| cs')
            in  fmap (\rest -> C.IdentCons rest digit) mRest
          Just (Right nonDigit) ->
            let !mRest = go (d NE.:| cs')
            in  fmap (\rest -> C.IdentConsNonDigit rest (C.IdentNonDigit nonDigit)) mRest

cDigitOrNonDigit :: Char -> Maybe (Either C.Digit C.NonDigit)
cDigitOrNonDigit c =
  let !mDigit = fmap Left (cDigit c)
  in  case mDigit of
        Just d -> Just d
        Nothing -> fmap Right (cNonDigit c)

cNonDigit :: Char -> Maybe C.NonDigit
cNonDigit c = case c of
  '_' -> pure $ C.NDUnderscore
  'a' -> pure $ C.NDa
  'b' -> pure $ C.NDb
  'c' -> pure $ C.NDc
  'd' -> pure $ C.NDd
  'e' -> pure $ C.NDe
  'f' -> pure $ C.NDf
  'g' -> pure $ C.NDg
  'h' -> pure $ C.NDh
  'i' -> pure $ C.NDi
  'j' -> pure $ C.NDj
  'k' -> pure $ C.NDk
  'l' -> pure $ C.NDl
  'm' -> pure $ C.NDm
  'n' -> pure $ C.NDn
  'o' -> pure $ C.NDo
  'p' -> pure $ C.NDp
  'q' -> pure $ C.NDq
  'r' -> pure $ C.NDr
  's' -> pure $ C.NDs
  't' -> pure $ C.NDt
  'u' -> pure $ C.NDu
  'v' -> pure $ C.NDv
  'w' -> pure $ C.NDw
  'x' -> pure $ C.NDx
  'y' -> pure $ C.NDy
  'z' -> pure $ C.NDz
  'A' -> pure $ C.NDA
  'B' -> pure $ C.NDB
  'C' -> pure $ C.NDC
  'D' -> pure $ C.NDD
  'E' -> pure $ C.NDE
  'F' -> pure $ C.NDF
  'G' -> pure $ C.NDG
  'H' -> pure $ C.NDH
  'I' -> pure $ C.NDI
  'J' -> pure $ C.NDJ
  'K' -> pure $ C.NDK
  'L' -> pure $ C.NDL
  'M' -> pure $ C.NDM
  'N' -> pure $ C.NDN
  'O' -> pure $ C.NDO
  'P' -> pure $ C.NDP
  'Q' -> pure $ C.NDQ
  'R' -> pure $ C.NDR
  'S' -> pure $ C.NDS
  'T' -> pure $ C.NDT
  'U' -> pure $ C.NDU
  'V' -> pure $ C.NDV
  'W' -> pure $ C.NDW
  'X' -> pure $ C.NDx
  'Y' -> pure $ C.NDZ
  'Z' -> pure $ C.NDZ
  _   -> Nothing

cDigit :: Char -> Maybe C.Digit
cDigit c = case c of
  '0' -> pure $ C.DZero
  '1' -> pure $ C.DOne
  '2' -> pure $ C.DTwo
  '3' -> pure $ C.DThree
  '4' -> pure $ C.DFour
  '5' -> pure $ C.DFive
  '6' -> pure $ C.DSix
  '7' -> pure $ C.DSeven
  '8' -> pure $ C.DEight
  '9' -> pure $ C.DNine
  _   -> Nothing

-- TODO
-- making decimal digits is surprising difficult to do without partial
-- functions, since the C99 lexcial structure does not allow leading 0s, and
-- GHC doesn't know that the most significant digit is 0 iff the number is 0.
-- Oh well, we just use hex everywhere.

{-
-- | Make a constant for an arbitrary natural number.
-- 0 is always an octal literal, as per the C99 spec.
-- Negative numbers get a minus sign out front, they are not treated at
-- constants in the C99 spec.
natConst :: Natural -> C.IntConst
natConst 0 = C.IntOc C.Oc0 Nothing
natConst n = nonZeroNatDecConst (decimalDigits n)

natDecConst n = case decimalDigits n of
  d NE.:| [] -> case d of
    -- This case can only happen if `n` is 0: the most significant digit cannot
    -- be 0.
    C.DZero  -> C.IntOc C.Oc0 Nothing
    C.DOne   -> C.IntDec (C.DecBase C.NZOne) Nothing
    C.DTwo   -> C.IntDec (C.DecBase C.NZTwo) Nothing
    C.DThree -> C.IntDec (C.DecBase C.NZThree) Nothing
    C.DFour  -> C.IntDec (C.DecBase C.NZFour) Nothing
    C.DFive  -> C.IntDec (C.DecBase C.NZFive) Nothing
    C.DSix   -> C.IntDec (C.DecBase C.NZSix) Nothing
    C.DSeven -> C.IntDec (C.DecBase C.NZSeven) Nothing
    C.DEight -> C.IntDec (C.DecBase C.NZEight) Nothing
    C.DNine  -> C.IntDec (C.DecBase C.NZNine) Nothing
  d NE.:| (d ': ds) -> case 

-- | Get the decimal digits of the number in reverse order (first element of the
-- list is the least significant digit).
-- The last element of the list is 0 iff this is the only element in the list
-- i.e. the input is 0. This is a useful property in 'natDecConst'.
decimalDigits :: Natural -> NonEmpty C.Digit
decimalDigits 0 = C.DZero NE.:| []
decimalDigits n = m NE.:| ms
  where
  (q, r) = divMod n 10
  ms = if q == 0 then [] else NE.toList (decimalDigits q)
  !m = case r of
    0 -> C.DZero
    1 -> C.DOne
    2 -> C.DTwo
    3 -> C.DThree
    4 -> C.DFour
    5 -> C.DFive
    6 -> C.DSix
    7 -> C.DSeven
    8 -> C.DEight
    9 -> C.DNine
    _ -> error "decimalDigits impossible case"
-}

hexConst :: NonEmpty C.HexDigit -> C.HexConst
hexConst (h NE.:| [])      = C.HexBase C.OX h
hexConst (h NE.:| (h':hs)) = C.HexCons (hexConst (h' NE.:| hs)) h

-- | Hex digits in little-endian style order.
hexDigits :: Natural -> NonEmpty C.HexDigit
hexDigits 0 = C.HexZero NE.:| []
hexDigits n = m NE.:| ms
  where
  (q, r) = divMod n 16
  ms = if q == 0 then [] else NE.toList (hexDigits q)
  !m = case r of
    0 -> C.HexZero
    1 -> C.HexOne
    2 -> C.HexTwo
    3 -> C.HexThree
    4 -> C.HexFour
    5 -> C.HexFive
    6 -> C.HexSix
    7 -> C.HexSeven
    8 -> C.HexEight
    9 -> C.HexNine
    10 -> C.HexA
    11 -> C.HexB
    12 -> C.HexC
    13 -> C.HexD
    14 -> C.HexE
    15 -> C.HexF
    _ -> error "hexDigits impossible case"

append_ident :: C.Ident -> C.Ident -> C.Ident
append_ident lft (C.IdentBase idnd) = C.IdentConsNonDigit lft idnd
append_ident lft (C.IdentConsNonDigit rgt idnd) = C.IdentConsNonDigit (append_ident lft rgt) idnd
append_ident lft (C.IdentCons rgt idd) = C.IdentCons (append_ident lft rgt) idd

-- | "uint8_t"
ident_uint8_t :: C.Ident
ident_uint8_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentConsNonDigit
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDu))
              (C.IdentNonDigit C.NDi)
            )
            (C.IdentNonDigit C.NDn)
          )
          (C.IdentNonDigit C.NDt)
        )
        C.DEight
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "uint16_t"
ident_uint16_t :: C.Ident
ident_uint16_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentConsNonDigit
                (C.IdentBase (C.IdentNonDigit C.NDu))
                (C.IdentNonDigit C.NDi)
              )
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DOne
        )
        C.DSix
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "uint32_t"
ident_uint32_t :: C.Ident
ident_uint32_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentConsNonDigit
                (C.IdentBase (C.IdentNonDigit C.NDu))
                (C.IdentNonDigit C.NDi)
              )
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DThree
        )
        C.DTwo
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "uint64_t"
ident_uint64_t :: C.Ident
ident_uint64_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentConsNonDigit
                (C.IdentBase (C.IdentNonDigit C.NDu))
                (C.IdentNonDigit C.NDi)
              )
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DSix
        )
        C.DFour
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "int8_t"
ident_int8_t :: C.Ident
ident_int8_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentConsNonDigit
          (C.IdentConsNonDigit
            (C.IdentBase (C.IdentNonDigit C.NDi))
            (C.IdentNonDigit C.NDn)
          )
          (C.IdentNonDigit C.NDt)
        )
        C.DEight
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "int16_t"
ident_int16_t :: C.Ident
ident_int16_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDi))
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DOne
        )
        C.DSix
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "int32_t"
ident_int32_t :: C.Ident
ident_int32_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDi))
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DThree
        )
        C.DTwo
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

-- | "int64_t"
ident_int64_t :: C.Ident
ident_int64_t =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentCons
        (C.IdentCons
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDi))
              (C.IdentNonDigit C.NDn)
            )
            (C.IdentNonDigit C.NDt)
          )
          C.DSix
        )
        C.DFour
      )
      (C.IdentNonDigit C.NDUnderscore)
    )
    (C.IdentNonDigit C.NDt)

ident_null :: C.Ident
ident_null =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentConsNonDigit
        (C.IdentBase (C.IdentNonDigit C.NDN))
        (C.IdentNonDigit C.NDU)
      )
      (C.IdentNonDigit C.NDL)
    )
    (C.IdentNonDigit C.NDL)

cNULL :: C.CondExpr
cNULL = C.CondLOr $ C.LOrAnd $ C.LAndOr $ C.OrXOr $ C.XOrAnd $ C.AndEq $
  C.EqRel $ C.RelShift $ C.ShiftAdd $ C.AddMult $ C.MultCast $ C.CastUnary $
  C.UnaryPostfix $ C.PostfixPrim $ C.PrimIdent ident_null

-- | NULL casted and dereferenced. Used whenever we have unreachable code.
cVOID :: C.TypeName -> C.UnaryExpr
cVOID typeName = C.UnaryOp C.UODeref (C.Cast typeName' (condExprIsCastExpr cNULL))
  where
  typeName' = case typeName of
    C.TypeName sql Nothing ->
      C.TypeName sql (Just (C.AbstractDeclr (C.PtrBase Nothing)))
    C.TypeName sql (Just (C.AbstractDeclr ptr)) ->
      C.TypeName sql (Just (C.AbstractDeclr (C.PtrCons Nothing ptr)))
    C.TypeName sql (Just (C.AbstractDeclrDirect Nothing dad)) ->
      C.TypeName sql (Just (C.AbstractDeclrDirect (Just (C.PtrBase Nothing)) dad))
    C.TypeName sql (Just (C.AbstractDeclrDirect (Just ptr) dad)) ->
      C.TypeName sql (Just (C.AbstractDeclrDirect (Just (C.PtrCons Nothing ptr)) dad))

-- | "eval", the name of the main function we generate. We don't use main
-- because that would give warnings for any expression type not int.
ident_eval :: C.Ident
ident_eval =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentConsNonDigit
        (C.IdentBase (C.IdentNonDigit C.NDe))
        (C.IdentNonDigit C.NDv)
      )
      (C.IdentNonDigit C.NDa)
    )
    (C.IdentNonDigit C.NDl)

-- | "tag"
ident_tag :: C.Ident
ident_tag =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentBase (C.IdentNonDigit C.NDt))
      (C.IdentNonDigit C.NDa)
    )
    (C.IdentNonDigit C.NDg)

-- | "variant"
ident_variant :: C.Ident
ident_variant =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentConsNonDigit
        (C.IdentConsNonDigit
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDv))
              (C.IdentNonDigit C.NDa)
            )
            (C.IdentNonDigit C.NDr)
          )
          (C.IdentNonDigit C.NDi)
        )
        (C.IdentNonDigit C.NDa)
      )
      (C.IdentNonDigit C.NDn)
    )
    (C.IdentNonDigit C.NDt)

-- | "_shared"
ident__shared :: C.Ident
ident__shared =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentConsNonDigit
        (C.IdentConsNonDigit
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDUnderscore))
              (C.IdentNonDigit C.NDs)
            )
            (C.IdentNonDigit C.NDh)
          )
          (C.IdentNonDigit C.NDa)
        )
        (C.IdentNonDigit C.NDr)
      )
      (C.IdentNonDigit C.NDe)
    )
    (C.IdentNonDigit C.NDd)
