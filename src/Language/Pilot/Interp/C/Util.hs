{-|
Module      : Language.Pilot.Interp.C.Util
Description : Utilities for writing C AST stuff.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Language.Pilot.Interp.C.Util where

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Numeric.Natural (Natural)

import Language.C99.AST as C

-- | All numbers are put out in hex. C decimals are just harder to work with,
-- since 0 is not a decimal number, but rather an octal one.
hexConst :: Natural -> C.HexConst
hexConst = hexConstNE . hexDigits

  where

  hexConstNE :: NonEmpty C.HexDigit -> C.HexConst
  hexConstNE (h NE.:| [])      = C.HexBase C.OX h
  hexConstNE (h NE.:| (h':hs)) = C.HexCons (hexConstNE (h' NE.:| hs)) h

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

blockItemInitialize :: C.TypeName -> C.Ident -> C.Expr -> C.BlockItem
blockItemInitialize tyName name expr = C.BlockItemDecln $
  declnInitialize tyName name expr

declnInitialize :: C.TypeName -> C.Ident -> C.Expr -> C.Decln
declnInitialize tyName@(C.TypeName specQualList mAbsDeclr) name expr = C.Decln
  (specQualListToDeclnSpecs specQualList)
  (Just (declnInitializer mAbsDeclr name expr))

specQualListToDeclnSpecs :: C.SpecQualList -> C.DeclnSpecs
specQualListToDeclnSpecs (C.SpecQualType tySpec Nothing) =
  C.DeclnSpecsType tySpec Nothing
specQualListToDeclnSpecs (C.SpecQualQual tyQual Nothing) =
  C.DeclnSpecsQual tyQual Nothing
specQualListToDeclnSpecs (C.SpecQualType tySpec (Just xs)) =
  C.DeclnSpecsType tySpec (Just (specQualListToDeclnSpecs xs))
specQualListToDeclnSpecs (C.SpecQualQual tyQual (Just xs)) =
  C.DeclnSpecsQual tyQual (Just (specQualListToDeclnSpecs xs))

declnInitializer :: Maybe C.AbstractDeclr -> C.Ident -> C.Expr -> C.InitDeclrList
declnInitializer mAbsDeclr ident expr = C.InitDeclrBase $ C.InitDeclrInitr
  (C.Declr (mAbstractDeclrToPtr mAbsDeclr) (C.DirectDeclrIdent ident))
  (C.InitExpr (exprIsAssignExpr expr))

mAbstractDeclrToPtr :: Maybe C.AbstractDeclr -> Maybe C.Ptr
mAbstractDeclrToPtr it = case it of
  Nothing -> Nothing
  Just (C.AbstractDeclr ptr) -> Just ptr
  Just (C.AbstractDeclrDirect mPtr _) -> mPtr

appendTransUnit :: C.TransUnit -> C.TransUnit -> C.TransUnit
appendTransUnit tu (C.TransUnitBase decln) = C.TransUnitCons tu decln
appendTransUnit tu (C.TransUnitCons tu' decln) = C.TransUnitCons
  (appendTransUnit tu tu')
  decln

appendTransUnitR :: C.TransUnit -> Maybe C.TransUnit -> C.TransUnit
appendTransUnitR tu Nothing = tu
appendTransUnitR tu (Just tu') = appendTransUnit tu tu'

appendTransUnitL :: Maybe C.TransUnit -> C.TransUnit -> C.TransUnit
appendTransUnitL Nothing tu = tu
appendTransUnitL (Just tu') tu = appendTransUnit tu' tu

appendTransUnitLR :: Maybe C.TransUnit -> Maybe C.TransUnit -> Maybe C.TransUnit
appendTransUnitLR Nothing Nothing = Nothing
appendTransUnitLR Nothing (Just tu) = Just tu
appendTransUnitLR (Just tu) Nothing = Just tu
appendTransUnitLR (Just tl) (Just tr) = Just (appendTransUnit tl tr)

-- | Puts these declarations into a translation unit, in reverse order.
transUnitFromDeclns :: [C.Decln] -> Maybe C.TransUnit
transUnitFromDeclns [] = Nothing
transUnitFromDeclns (d:ds) = case transUnitFromDeclns ds of
  Nothing -> Just (C.TransUnitBase (C.ExtDecln d))
  Just tu -> Just (C.TransUnitCons tu (C.ExtDecln d))



appendBlockItemList :: C.BlockItemList -> C.BlockItemList -> C.BlockItemList
appendBlockItemList bl (C.BlockItemBase bi) = C.BlockItemCons bl bi
appendBlockItemList bl (C.BlockItemCons bl' bi) = C.BlockItemCons
  (appendBlockItemList bl bl')
  bi

appendBlockItemListLR
  :: Maybe C.BlockItemList
  -> Maybe C.BlockItemList
  -> Maybe C.BlockItemList
appendBlockItemListLR Nothing Nothing = Nothing
appendBlockItemListLR (Just bl) Nothing = Just bl
appendBlockItemListLR Nothing (Just br) = Just br
appendBlockItemListLR (Just bl) (Just br) = Just (appendBlockItemList bl br)

constIntExpr :: Natural -> C.Expr
constIntExpr n = constIsExpr $ C.ConstInt $
  C.IntHex (hexConst (fromIntegral n)) Nothing

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

castExprIsCondExpr :: C.CastExpr -> C.CondExpr
castExprIsCondExpr = multExprIsCondExpr . C.MultCast

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

constIsExpr :: C.Const -> C.Expr
constIsExpr = condExprIsExpr . constIsCondExpr

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

unaryExprIsExpr :: C.UnaryExpr -> C.Expr
unaryExprIsExpr = C.ExprAssign . C.AssignCond . unaryExprIsCondExpr

exprIsAddExpr :: C.Expr -> C.AddExpr
exprIsAddExpr = C.AddMult . exprIsMultExpr

exprIsMultExpr :: C.Expr -> C.MultExpr
exprIsMultExpr = C.MultCast . exprIsCastExpr

exprIsCastExpr :: C.Expr -> C.CastExpr
exprIsCastExpr = C.CastUnary . exprIsUnaryExpr

exprIsUnaryExpr :: C.Expr -> C.UnaryExpr
exprIsUnaryExpr = C.UnaryPostfix . exprIsPostfixExpr

exprIsPostfixExpr :: C.Expr -> C.PostfixExpr
exprIsPostfixExpr = C.PostfixPrim . exprIsPrimExpr

exprIsPrimExpr :: C.Expr -> C.PrimExpr
exprIsPrimExpr = C.PrimExpr

exprIsAndExpr :: C.Expr -> C.AndExpr
exprIsAndExpr = C.AndEq . exprIsEqExpr

exprIsEqExpr :: C.Expr -> C.EqExpr
exprIsEqExpr = C.EqRel . exprIsRelExpr

exprIsRelExpr :: C.Expr -> C.RelExpr
exprIsRelExpr = C.RelShift . exprIsShiftExpr

exprIsShiftExpr :: C.Expr -> C.ShiftExpr
exprIsShiftExpr = C.ShiftAdd . exprIsAddExpr

exprIsOrExpr :: C.Expr -> C.OrExpr
exprIsOrExpr = C.OrXOr . exprIsXOrExpr

exprIsXOrExpr :: C.Expr -> C.XOrExpr
exprIsXOrExpr = C.XOrAnd . exprIsAndExpr

exprIsCondExpr :: C.Expr -> C.CondExpr
exprIsCondExpr = C.CondLOr . exprIsLOrExpr

exprIsLOrExpr :: C.Expr -> C.LOrExpr
exprIsLOrExpr = C.LOrAnd . exprIsLAndExpr

exprIsLAndExpr :: C.Expr -> C.LAndExpr
exprIsLAndExpr = C.LAndOr . exprIsOrExpr

exprIsAssignExpr :: C.Expr -> C.AssignExpr
exprIsAssignExpr = C.AssignCond . exprIsCondExpr

addExprIsExpr :: C.AddExpr -> C.Expr
addExprIsExpr = condExprIsExpr . addExprIsCondExpr

andExprIsExpr :: C.AndExpr -> C.Expr
andExprIsExpr = condExprIsExpr . andExprIsCondExpr

orExprIsExpr :: C.OrExpr -> C.Expr
orExprIsExpr = condExprIsExpr . orExprIsCondExpr

xorExprIsExpr :: C.XOrExpr -> C.Expr
xorExprIsExpr = condExprIsExpr . xorExprIsCondExpr

shiftExprIsExpr :: C.ShiftExpr -> C.Expr
shiftExprIsExpr = condExprIsExpr . shiftExprIsCondExpr

relExprIsExpr :: C.RelExpr -> C.Expr
relExprIsExpr = condExprIsExpr . relExprIsCondExpr

castExprIsExpr :: C.CastExpr -> C.Expr
castExprIsExpr = condExprIsExpr . castExprIsCondExpr

append_ident :: C.Ident -> C.Ident -> C.Ident
append_ident lft (C.IdentBase idnd) = C.IdentConsNonDigit lft idnd
append_ident lft (C.IdentConsNonDigit rgt idnd) = C.IdentConsNonDigit (append_ident lft rgt) idnd
append_ident lft (C.IdentCons rgt idd) = C.IdentCons (append_ident lft rgt) idd

ident_size_t :: C.Ident
ident_size_t = assertValidStringIdentifier "size_t"

ident_uint8_t :: C.Ident
ident_uint8_t = assertValidStringIdentifier "uint8_t"

ident_uint16_t :: C.Ident
ident_uint16_t = assertValidStringIdentifier "uint16_t"

ident_uint32_t :: C.Ident
ident_uint32_t = assertValidStringIdentifier "uint32_t"

ident_uint64_t :: C.Ident
ident_uint64_t = assertValidStringIdentifier "uint64_t"

ident_int8_t :: C.Ident
ident_int8_t = assertValidStringIdentifier "int8_t"

ident_int16_t :: C.Ident
ident_int16_t = assertValidStringIdentifier "int16_t"

ident_int32_t :: C.Ident
ident_int32_t = assertValidStringIdentifier "int32_t"

ident_int64_t :: C.Ident
ident_int64_t = assertValidStringIdentifier "int64_t"

ident_NULL :: C.Ident
ident_NULL = assertValidStringIdentifier "NULL"

cNULL :: C.CondExpr
cNULL = C.CondLOr $ C.LOrAnd $ C.LAndOr $ C.OrXOr $ C.XOrAnd $ C.AndEq $
  C.EqRel $ C.RelShift $ C.ShiftAdd $ C.AddMult $ C.MultCast $ C.CastUnary $
  C.UnaryPostfix $ C.PostfixPrim $ C.PrimIdent ident_NULL

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

assertValidStringIdentifier :: String -> C.Ident
assertValidStringIdentifier str = case stringIdentifier str of
  Nothing -> error ("assertValidStringIdentifier: bad identifier " ++ str)
  Just id -> id

assertValidIdentifier :: String -> Maybe C.Ident -> C.Ident
assertValidIdentifier msg Nothing  = error msg
assertValidIdentifier _   (Just i) = i

assertValidStringIdentifierM :: Applicative m => (forall t . m t) -> String -> m C.Ident
assertValidStringIdentifierM err str = case stringIdentifier str of
  Nothing  -> err
  Just str -> pure str

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
