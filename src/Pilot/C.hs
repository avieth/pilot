{-|
Module      : Pilot.C
Description : Sink for stuff related to generating C concrete syntax.
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
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE EmptyCase #-}

module Pilot.C where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Functor.Identity

import qualified Data.Int as Haskell
import qualified Data.Kind as Haskell (Type)
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy (Proxy (..))
import qualified Data.Typeable as Haskell
import qualified Data.Word as Haskell
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import Numeric.Natural (Natural)

import qualified Language.C99.AST as C
import Language.C99.Pretty (Pretty, pretty)
import Text.PrettyPrint (render)

import Pilot.EDSL.Point as Point
import Pilot.Types.Nat

-- TODO NEXT STEPS
-- - Define intro/elim expressions.
-- - The CodeGen monad maintains bindings, so use the ST trick? So new type
--   parameter stands in for "binding context" and if it's free that means
--   "no assumptions about bindings".

-- | Useful for debugging.
prettyPrint :: Pretty a => a -> String
prettyPrint = render . pretty

-- |
-- = Type names and type declarations

-- | For integral types we use the C standard explicit types like uint8_t.
--
-- TODO may want this to be in CodeGenM and update state to say which headers
-- we need to include?
integer_ident :: SignednessRep signedness -> WidthRep width -> C.Ident
integer_ident Unsigned_t Eight_t     = ident_uint8_t
integer_ident Unsigned_t Sixteen_t   = ident_uint16_t
integer_ident Unsigned_t ThirtyTwo_t = ident_uint32_t
integer_ident Unsigned_t SixtyFour_t = ident_uint64_t
integer_ident Signed_t Eight_t       = ident_int8_t
integer_ident Signed_t Sixteen_t     = ident_int16_t
integer_ident Signed_t ThirtyTwo_t   = ident_int32_t
integer_ident Signed_t SixtyFour_t   = ident_int64_t

-- | The C type name for a type in the EDSL.
type_name :: TypeRep ty -> CodeGenM C.TypeName

type_name (Integer_t sr wr) =
  let ident = integer_ident sr wr
      tdef = C.TTypedef $ C.TypedefName ident
      specQualList = C.SpecQualType tdef Nothing
  in  pure $ C.TypeName specQualList Nothing

-- TODO support float and double?
type_name Rational_t = codeGenError $
  CodeGenInternalError "fractional numbers not supported at the moment"

type_name p@(Product_t _) = do
  -- Declare is idempotent; ensures there is a C declaration for the
  -- representation of this product, if necessary.
  product_declare p
  product_type_name p

type_name p@(Sum_t _) = do
  sum_declare p
  sum_type_name p

-- | Just like 'product_type_name'. Sums and products are both, at the
-- top-level, represented by structs.
sum_type_name :: TypeRep ('Sum tys) -> CodeGenM C.TypeName
sum_type_name (Sum_t AllF) = pure $ C.TypeName
  (C.SpecQualType C.TVoid Nothing)
  (Just (C.AbstractDeclr (C.PtrBase Nothing)))
sum_type_name trep@(Sum_t tys@(AndF _ _)) = do
  specQual <- sum_spec_qual trep
  pure $ C.TypeName specQual (Just (C.AbstractDeclr (C.PtrBase Nothing)))

-- | The type to use for a product.
-- For empty products we use void*.
-- For non-empty products we use the name of the corresponding struct (found
-- in the state). The type is a pointer to it.
product_type_name :: TypeRep ('Product tys) -> CodeGenM C.TypeName
product_type_name (Product_t AllF) = pure $ C.TypeName
  (C.SpecQualType C.TVoid Nothing)
  (Just (C.AbstractDeclr (C.PtrBase Nothing)))
product_type_name trep@(Product_t (AndF _ _)) = do
  specQual <- product_spec_qual trep
  pure $ C.TypeName specQual (Just (C.AbstractDeclr (C.PtrBase Nothing)))
    

-- | The product type for use with initialization of its struct.
product_spec_qual :: TypeRep ('Product (t ': ts)) -> CodeGenM C.SpecQualList
product_spec_qual (Product_t tys) = do
  -- We use the Haskell TypeRep as a key in a map to get the name.
  let haskellTypeRep :: Haskell.TypeRep
      haskellTypeRep = Haskell.typeOf tys
  prodMap <- CodeGenM $ lift $ gets cgsProducts
  case Map.lookup haskellTypeRep prodMap of
    Just pdeclr -> pure $ C.SpecQualType
      (C.TStructOrUnion (C.StructOrUnionForwDecln C.Struct (pdStructIdent pdeclr)))
      Nothing
    Nothing -> codeGenError $ CodeGenInternalError $
      "product_spec_qual_type not found " ++ show haskellTypeRep

-- | The sum type for use with initialization of its struct. The enum and
-- union inside it do not need to be named (the C compiler can infer them).
sum_spec_qual :: TypeRep ('Sum (t ': ts)) -> CodeGenM C.SpecQualList
sum_spec_qual (Sum_t tys) = do
  -- We use the Haskell TypeRep as a key in a map to get the name.
  let haskellTypeRep :: Haskell.TypeRep
      haskellTypeRep = Haskell.typeOf tys
  sumMap <- CodeGenM $ lift $ gets cgsSums
  case Map.lookup haskellTypeRep sumMap of
    Just sdeclr -> pure $ C.SpecQualType
      (C.TStructOrUnion (C.StructOrUnionForwDecln C.Struct (sdStructIdent sdeclr)))
      Nothing
    Nothing -> codeGenError $ CodeGenInternalError $
      "sum_spec_qual_type not found " ++ show haskellTypeRep

-- | Stateful CodeGen term to declare a product. If it has already been
-- declared (something with the same 'Haskell.TypeRep' was declared) then
-- nothing happens. Otherwise, we generate a new identifier, and include its
-- struct declaration.
product_declare :: TypeRep ('Product tys) -> CodeGenM ()
-- Unit type: nothing to do, it's void*
product_declare (Product_t AllF) = pure ()
product_declare (Product_t tys@(AndF t ts)) = do
  let haskellTypeRep :: Haskell.TypeRep
      haskellTypeRep = Haskell.typeOf tys
  prodMap <- CodeGenM $ lift $ gets cgsProducts
  case Map.lookup haskellTypeRep prodMap of
    -- Already there; good to go.
    Just _pdeclr -> pure ()
    -- This signature has not been seen yet. Generate a new name and compute
    -- its signature. We can do this because we know there is at least one
    -- conjunct in the product (`AndF t ts`).
    Nothing -> do
      prodDeclns <- field_declns "field_" 0 t ts
      -- NB: map may have changed as a result of field_declns.
      st <- CodeGenM $ lift get
      prodIdent <- maybeError
        -- We know this can't happen.
        (CodeGenInternalError $ "product_declare bad identifier for " ++ show haskellTypeRep)
        (stringIdentifier ("product_" ++ show (Map.size (cgsProducts st))))
      let pdeclr = ProductDeclr
            { pdStructDeclnList = prodDeclns
            , pdStructIdent     = prodIdent
            }
          prodMap' = Map.insert haskellTypeRep pdeclr (cgsProducts st)
          st' = st { cgsProducts = prodMap' }
      CodeGenM $ lift $ put st'

-- | Create and include in state the declarations required for a sum
-- representation. Empty sums are void pointers. Non-empty sums are represented
-- by enum tags, union variants, and a struct containing these two things.
--
-- TODO moving forward, we can special case this for more efficient
-- representations. The boolean type, for instance, could indeed be represented
-- by a byte. Indeed any disjunct that has no fields can be removed from the
-- union declaration, and if the resulting union declaration is empty we can
-- represent the sum directly by the enum.
sum_declare :: TypeRep ('Sum tys) -> CodeGenM ()
-- No declaration; it's void*
sum_declare (Sum_t AllF) = pure ()
sum_declare (Sum_t tys@(AndF t ts)) = do
  let haskellTypeRep :: Haskell.TypeRep
      haskellTypeRep = Haskell.typeOf tys
  sumMap <- CodeGenM $ lift $ gets cgsSums
  case Map.lookup haskellTypeRep sumMap of
    Just _sdeclr -> pure ()
    Nothing -> do

      unionDeclns <- field_declns "variant_" 0 t ts
      enumrList   <- enum_tag_declns 0 t ts

      -- NB: sumMap may have changed as a result of field_declns.
      st <- CodeGenM $ lift get
      let sumMap = cgsSums st

      sumStructIdent <- maybeError
        (CodeGenInternalError $ "sum_declare bad struct identifier for " ++ show haskellTypeRep)
        (stringIdentifier ("sum_" ++ show (Map.size sumMap)))
      sumUnionIdent <- maybeError
        (CodeGenInternalError $ "sum_declare bad union identifier for " ++ show haskellTypeRep)
        (stringIdentifier ("sum_variant_" ++ show (Map.size sumMap)))
      sumEnumIdent <- maybeError
        (CodeGenInternalError $ "sum_declare bad enum identifier for " ++ show haskellTypeRep)
        (stringIdentifier ("sum_tag_" ++ show (Map.size sumMap)))

      -- The sum is
      --
      --   struct sum_n {
      --     enum tag_n tag;
      --     union variant_n variant;
      --   }
      --
      -- NB: they are not pointers.
      let structDeclns = C.StructDeclnCons
            (C.StructDeclnBase $ C.StructDecln
              (C.SpecQualType (C.TEnum (C.EnumSpecForw sumEnumIdent)) Nothing)
              (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_tag))))
            )
            (C.StructDecln
              (C.SpecQualType (C.TStructOrUnion (C.StructOrUnionForwDecln C.Union sumUnionIdent)) Nothing)
              (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_variant))))
            )

      let sdeclr = SumDeclr
            { sdStructIdent     = sumStructIdent
            , sdUnionIdent      = sumUnionIdent
            , sdEnumIdent       = sumEnumIdent
            , sdStructDeclnList = structDeclns
            , sdUnionDeclnList  = unionDeclns
            , sdEnumrList       = enumrList
            }
          sumMap' = Map.insert haskellTypeRep sdeclr (cgsSums st)
          st' = st { cgsSums = sumMap' }
      CodeGenM $ lift $ put st'

-- | Make enum declarations to serve as the tags for a sum representation.
enum_tag_declns :: Natural -> TypeRep ty -> All TypeRep tys -> CodeGenM C.EnumrList
enum_tag_declns n _ AllF = do
  ident <- maybeError
    (CodeGenInternalError $ "enum_tag_declns bad identifier")
    (stringIdentifier ("tag_" ++ show n))
  pure $ C.EnumrBase $ C.Enumr $ C.Enum ident
enum_tag_declns n t (AndF t' ts) = do
  ident <- maybeError
    (CodeGenInternalError $ "enum_tag_declns bad identifier")
    (stringIdentifier ("tag_" ++ show n))
  subList <- enum_tag_declns (n+1) t' ts
  pure $ C.EnumrCons subList $ C.Enumr $ C.Enum ident

-- | This will put the fields in reverse order, since the C declaration list
-- type is defines like a snoc-list. Doesn't really matter though.
field_declns :: String -> Natural -> TypeRep ty -> All TypeRep tys -> CodeGenM C.StructDeclnList

field_declns name n t AllF = do
  -- TODO factor this out so we can re-use in the other case.
  C.TypeName specQualList mAbstractDeclr <- type_name t
  ident <- maybeError
    (CodeGenInternalError $ "field_declns bad identifier")
    (stringIdentifier (name ++ show n))
  let qualList :: C.SpecQualList
      qualList = specQualList
      -- We want the field to be a pointer iff the type of t is a pointer.
      mPtr :: Maybe C.Ptr
      mPtr = mAbstractDeclr >>= \it -> case it of
        C.AbstractDeclr ptr -> Just ptr
        C.AbstractDeclrDirect mPtr' _ -> mPtr'
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr mPtr $ C.DirectDeclrIdent ident
  pure $ C.StructDeclnBase $ C.StructDecln qualList declrList

field_declns name n t (AndF t' ts) = do
  subList <- field_declns name (n+1) t' ts
  C.TypeName specQualList mAbstractDeclr <- type_name t
  ident <- maybeError
    (CodeGenInternalError $ "field_declns bad identifier")
    (stringIdentifier (name ++ show n))
  let qualList :: C.SpecQualList
      qualList = specQualList
      -- We want the field to be a pointer iff the type of t is a pointer.
      mPtr :: Maybe C.Ptr
      mPtr = mAbstractDeclr >>= \it -> case it of
        C.AbstractDeclr ptr -> Just ptr
        C.AbstractDeclrDirect mPtr' _ -> mPtr'
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr mPtr $ C.DirectDeclrIdent ident
  pure $ C.StructDeclnCons subList $ C.StructDecln qualList declrList

-- |
-- = Evaluation of expressions

example_1_1 = eval_intro_product
  (pair_t uint16_t (pair_t int8_t uint64_t))
  ( AndF (eval_intro_integer uint16_t (UInt16 43))
  $ AndF (eval_intro_product (pair_t int8_t uint64_t)
      (AndF (eval_intro_integer int8_t (Int8 (-1))) $ AndF (eval_intro_integer uint64_t (UInt64 65536)) $ AllF))
  $ AllF)

example_1_2 = eval_elim_product
  (pair_t uint8_t uint16_t)
  (OrC (AnyC (\it -> it)))
  (eval_intro_product (pair_t uint8_t uint16_t)
    (AndF (eval_intro_integer uint8_t (UInt8 1)) $ AndF (eval_intro_integer uint16_t (UInt16 2)) $ AllF)
  )

example_2_1 = eval_intro_sum
  (maybe_t (pair_t uint8_t int8_t))
  (AnyF (eval_intro_product unit_t AllF))

example_2_2 = eval_intro_sum
  (maybe_t (pair_t uint8_t int8_t))
  (OrF (AnyF (eval_intro_product (pair_t uint8_t int8_t)
    (AndF (eval_intro_integer uint8_t (UInt8 42)) $ AndF (eval_intro_integer int8_t (Int8 (-42))) $ AllF))))

example_3_1 = eval_elim_sum
  (maybe_t (pair_t uint8_t int8_t))
  int8_t
  (AndC (\_ -> eval_intro_integer int8_t (Int8 (-1))) $ AndC (\x -> eval_elim_product (pair_t uint8_t int8_t) (OrC (AnyC (\it -> it))) x) $ AllC)
  example_2_2

eval_expr :: ExprF CodeGen t -> CodeGen t
eval_expr (IntroInteger tr il) = eval_intro_integer tr il
eval_expr (IntroProduct tr fields) = eval_intro_product tr fields
eval_expr (IntroSum tr variant) = eval_intro_sum tr variant
eval_expr (ElimProduct tr rr sel it) = eval_elim_product tr sel it
eval_expr (ElimSum tr rr cases it) = eval_elim_sum tr rr cases it

eval_intro_integer
  :: TypeRep ('Integer signedness width)
  -> IntegerLiteral signedness width
  -> CodeGen ('Integer signedness width)
eval_intro_integer (Integer_t Unsigned_t _width) il = CodeGen $ pure $
  constIsCondExpr $ C.ConstInt $ C.IntHex (hex_const (absolute_value il)) Nothing
eval_intro_integer (Integer_t Signed_t _width) il = CodeGen $ pure $
  unaryExprIsCondExpr $ C.UnaryOp C.UOMin $ constIsCastExpr $ C.ConstInt $
  C.IntHex (hex_const (absolute_value il)) Nothing

absolute_value :: IntegerLiteral signedness width -> Natural
absolute_value (UInt8 w8)   = fromIntegral w8
absolute_value (UInt16 w16) = fromIntegral w16
absolute_value (UInt32 w32) = fromIntegral w32
absolute_value (UInt64 w64) = fromIntegral w64
absolute_value (Int8 i8)    = fromIntegral (abs i8)
absolute_value (Int16 i16)  = fromIntegral (abs i16)
absolute_value (Int32 i32)  = fromIntegral (abs i32)
absolute_value (Int64 i64)  = fromIntegral (abs i64)

-- | Product intro: give all conjuncts and get the product. Since products are
-- structs, this corresponds to a struct initializer with a field for each
-- conjunct.
--
-- For non-empty products, this is a reference to a struct literal, i.e.
-- something like &(struct product_1){.field_0 ... };
-- Why? Because this way we can put any product literal inside another product
-- or sum by default without having to special case at product construction
-- time.
-- Are there significant downsides to this?
--
-- Special case for the empty product introduction, which is simply NULL.
-- TODO there is no way to eliminate an empty product, so we could probably
-- get away with simply erasing an intro of an empty product.
eval_intro_product :: TypeRep ('Product types) -> All CodeGen types -> CodeGen ('Product types)
eval_intro_product _    AllF = CodeGen $ pure cNULL
eval_intro_product trep (AndF t ts) = CodeGen $ do
  -- This will ensure the composite type is in the code gen state
  () <- product_declare trep
  -- We don't want the product's type name, because that's a pointer. Instead
  -- we just want its type spec and qual list.
  specQual <- product_spec_qual trep
  let typeName = C.TypeName specQual Nothing
  initList <- product_field_inits 0 t ts
  let pexpr = C.PostfixInits typeName initList
      uexpr = C.UnaryOp C.UORef (postfixExprIsCastExpr pexpr)
  pure $ unaryExprIsCondExpr uexpr

-- | Product elimination: an indirect field accessor (->).
--
-- NB: this cannot be an empty product, the 'Selector' GADT does not allow it.
eval_elim_product
  :: TypeRep ('Product types)
  -> Selector CodeGen types r
  -> CodeGen ('Product types)
  -> CodeGen r
eval_elim_product trep selector cgt = CodeGen $ do
  () <- product_declare trep
  pexpr <- condExprIsPostfixExpr <$> getCodeGen cgt
  getCodeGen $ eval_elim_product_with_selector 0 pexpr selector

-- |
--
-- From the field selector we can determine
-- - The name of the field selector to use
-- - A meta-language function to generate the rest of the expression using that
--   object-language selector and struct
--
eval_elim_product_with_selector
  :: Natural
  -> C.PostfixExpr -- ^ The C expression giving the product struct.
  -> Selector CodeGen types r
  -> CodeGen r
eval_elim_product_with_selector n pexpr (OrC sel) = eval_elim_product_with_selector (n+1) pexpr sel
eval_elim_product_with_selector n pexpr (AnyC k) = CodeGen $ do
  fieldIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_product_with_selector bad field " ++ show n)
    (stringIdentifier ("field_" ++ show n))
  let expr = postfixExprIsCondExpr $ C.PostfixArrow pexpr fieldIdent
      arg = CodeGen (pure expr)
  getCodeGen (k arg)

-- |
--
-- Like for empty products, empty sums are also void* so that we can just use
-- NULL and not allocate anything.
eval_intro_sum
  :: TypeRep ('Sum types)
  -> Any CodeGen types
  -> CodeGen ('Sum types)
-- The meta-language doesn't allow for empty sums to be introduced (void type
-- in the algebraic sense).
eval_intro_sum (Sum_t AllF) it = case it of
  {}
eval_intro_sum trep@(Sum_t (AndF _ _)) any = CodeGen $ do
  () <- sum_declare trep
  specQual <- sum_spec_qual trep
  let typeName = C.TypeName specQual Nothing
  initList <- sum_field_inits any
  let pexpr = C.PostfixInits typeName initList
      uexpr = C.UnaryOp C.UORef (postfixExprIsCastExpr pexpr)
  pure $ unaryExprIsCondExpr uexpr

product_field_inits
  :: Natural
  -> CodeGen t
  -> All CodeGen ts
  -> CodeGenM C.InitList
product_field_inits n cgt AllF = do
  expr <- getCodeGen cgt
  designator <- simple_designator ("field_" ++ show n)
  pure $ C.InitBase (Just designator) (C.InitExpr (condExprIsAssignExpr expr))
product_field_inits n cgt (AndF cgt' cgts) = do
  expr <- getCodeGen cgt
  designator <- simple_designator ("field_" ++ show n)
  subList <- product_field_inits (n+1) cgt' cgts
  pure $ C.InitCons subList (Just designator) (C.InitExpr (condExprIsAssignExpr expr))

-- | The init list for a sum struct: its tag and its variant.
sum_field_inits :: Any CodeGen ts -> CodeGenM C.InitList
sum_field_inits any = do
  tagExpr <- condExprIsAssignExpr <$> sum_tag_expr 0 any
  variantInitList <- sum_variant_init_list 0 any
  pure $ C.InitCons
    (C.InitBase (Just (ident_designator ident_tag)) (C.InitExpr tagExpr))
    (Just (ident_designator ident_variant))
    -- Sad naming convention from the spec: it's not initializing an array, it's
    -- just an array of initializers. It's how we get to give an initializer
    -- without specifying the union type name.
    (C.InitArray variantInitList)

-- | The expression for a sum's tag: determined by the offset in the disjuncts
-- in the type signature, and the common "tag_" prefix.
sum_tag_expr :: Natural -> Any f ts -> CodeGenM C.CondExpr
sum_tag_expr n (OrF there) = sum_tag_expr (n+1) there
sum_tag_expr n (AnyF _) = do
  ident <- maybeError
    (CodeGenInternalError $ "sum_tag_expr invalid tag field " ++ show n)
    (stringIdentifier ("tag_" ++ show n))
  pure $ primExprIsCondExpr $ C.PrimIdent ident

-- | The variant expression for a sum: it's a union literal, _without_ a
-- pointer (sums hold their tags and unions directly).
sum_variant_init_list :: Natural -> Any CodeGen ts -> CodeGenM C.InitList
sum_variant_init_list n (OrF there) = sum_variant_init_list (n+1) there
sum_variant_init_list n (AnyF cgt) = do
  expr <- getCodeGen cgt
  designator <- simple_designator ("variant_" ++ show n)
  let initExpr = C.InitExpr (condExprIsAssignExpr expr)
  pure $ C.InitBase (Just designator) initExpr

-- | Sum elimination is a conditional expression (the ? : ternary operator).
--
-- TODO moving forward, we'll need to demarcate scope in the code gen state.
-- If one of the branches does a binding, then we need to factor it into a
-- function so it gets its own scope and is not evaluated too eagerly (and
-- therefore incorrectly/probably wastefully).
eval_elim_sum
  :: TypeRep ('Sum types)
  -> TypeRep r
  -> Cases CodeGen types r
  -> CodeGen ('Sum types)
  -> CodeGen r
eval_elim_sum trep rrep cases cgt = CodeGen $ do
  () <- sum_declare trep
  -- We shall need two expressions: the sum's tag and its variant.
  -- These are taken by way of the indirect accessor. The union, however, will
  -- be accessed using the direct dot accessor.
  pexpr <- condExprIsPostfixExpr <$> getCodeGen cgt
  let tagExpr = postfixExprIsEqExpr $ C.PostfixArrow pexpr ident_tag
      variantExpr = C.PostfixArrow pexpr ident_variant
  getCodeGen $ eval_elim_sum_with_cases 0 rrep tagExpr variantExpr cases

eval_elim_sum_with_cases
  :: Natural
  -> TypeRep r
  -> C.EqExpr -- ^ The tag of the sum
  -> C.PostfixExpr -- ^ The variant of the sum
  -> Cases CodeGen types r
  -> CodeGen r
-- TODO what should we put for eliminating an empty product? The idea is that
-- this code should never be reached in the C executable.
eval_elim_sum_with_cases n rrep tagExpr variantExpr AllC = CodeGen $ do
  typeName <- type_name rrep
  pure $ unaryExprIsCondExpr $ cVOID typeName
eval_elim_sum_with_cases n rrep tagExpr variantExpr (AndC k cases) = CodeGen $ do
  tagIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (stringIdentifier ("tag_" ++ show n))
  variantIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (stringIdentifier ("variant_" ++ show n))
  let valueSelector = C.PostfixDot variantExpr variantIdent
  trueExpr <- getCodeGen $ k (CodeGen (pure (postfixExprIsCondExpr valueSelector)))
  falseExpr <- getCodeGen $ eval_elim_sum_with_cases (n+1) rrep tagExpr variantExpr cases
  let conditionExpr = eqExprIsLOrExpr $ C.EqEq tagExpr (identIsRelExpr tagIdent)
      condExpr = C.Cond conditionExpr (condExprIsExpr trueExpr) falseExpr
  pure condExpr

eqExprIsLOrExpr :: C.EqExpr -> C.LOrExpr
eqExprIsLOrExpr = C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd . C.AndEq

identIsRelExpr :: C.Ident -> C.RelExpr
identIsRelExpr = C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

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

postfixExprIsCondExpr :: C.PostfixExpr -> C.CondExpr
postfixExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix

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

unaryExprIsCondExpr :: C.UnaryExpr -> C.CondExpr
unaryExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary

ident_designator :: C.Ident -> C.Design
ident_designator = C.Design . C.DesigrBase . C.DesigrIdent

simple_designator :: String -> CodeGenM C.Design
simple_designator str = do
  ident <- maybeError
    (CodeGenInternalError $ "simple_designator bad identifier")
    (stringIdentifier str)
  pure $ C.Design $ C.DesigrBase $ C.DesigrIdent ident

-- | All numbers are put out in hex. C decimals are just harder to work with,
-- since 0 is not a decimal number, but rather an octal one.
hex_const :: Natural -> C.HexConst
hex_const = hexConst . hexDigits

-- | The target for generating C abstract syntax (and then concrete, by way of
-- Language.C99.Pretty).
newtype CodeGen (t :: Type) = CodeGen
  { getCodeGen :: CodeGenM C.CondExpr }

data CodeGenError where
  -- | Indicates a bug in this program.
  CodeGenInternalError :: String -> CodeGenError

deriving instance Show CodeGenError

-- | Code generation modifies a CodeGenState from an initial empty state.
-- This state is relative to some C expression which is being built-up (see
-- the `CodeGenM` and `CodeGen` types).
data CodeGenState = CodeGenState
  { -- | Bindings used in the expression.
    -- TODO FIXME we'll have to be very careful about this: bindings made
    -- under a sum elimination must get their own scopes, i.e. they need to
    -- go into function calls.
    cgsBindings :: !(Map VarIdentifier C.CondExpr)
  , cgsProducts :: !(Map TypeIdentifier ProductDeclr)
  , cgsSums     :: !(Map TypeIdentifier SumDeclr)
  }

-- | Get all of the C enum, struct, and union declarations.
-- Order is important. Enums go first, then forward declarations of structs
-- and unions, then declarations. Since all structs and unions are referenced
-- through pointers, this corresponds to legit valid C (all sizes can be known
-- at compile time).
-- For structs representing sums, they must be declared only _after_ the union
-- for the variant, since these structs reference those unions directly (not
-- through a pointer). That invariant is maintained in this list, so respect
-- the order when generating concrete syntax.
codeGenCompoundTypes :: CodeGenState -> [C.TypeSpec]
codeGenCompoundTypes cgs =
       fmap C.TEnum enums
    ++ fmap C.TStructOrUnion forwardDeclns
    ++ fmap C.TStructOrUnion declns
  where
  enums = concatMap sumEnum sums
  forwardDeclns = concatMap productForw products ++ concatMap sumForw sums
  declns = concatMap productDeclns products ++ concatMap sumDeclns sums
  products = Map.elems (cgsProducts cgs)
  sums = Map.elems (cgsSums cgs)
  sumEnum :: SumDeclr -> [C.EnumSpec]
  sumEnum sdeclr = [C.EnumSpec (Just (sdEnumIdent sdeclr)) (sdEnumrList sdeclr)]
  productDeclns :: ProductDeclr -> [C.StructOrUnionSpec]
  productDeclns pdeclr =
    [ C.StructOrUnionDecln C.Struct (Just (pdStructIdent pdeclr)) (pdStructDeclnList pdeclr) ]
  sumDeclns :: SumDeclr -> [C.StructOrUnionSpec]
  sumDeclns sdeclr =
    -- NB: order is actually crucial here. Since the struct references the union
    -- directly (not through a pointer) we must declare the union first.
    [ C.StructOrUnionDecln C.Union  (Just (sdUnionIdent  sdeclr)) (sdUnionDeclnList  sdeclr)
    , C.StructOrUnionDecln C.Struct (Just (sdStructIdent sdeclr)) (sdStructDeclnList sdeclr)
    ]
  productForw :: ProductDeclr -> [C.StructOrUnionSpec]
  productForw pdeclr = [C.StructOrUnionForwDecln C.Struct (pdStructIdent pdeclr)]
  sumForw :: SumDeclr -> [C.StructOrUnionSpec]
  sumForw sdeclr =
    [ C.StructOrUnionForwDecln C.Struct (sdStructIdent sdeclr)
    , C.StructOrUnionForwDecln C.Union (sdUnionIdent sdeclr)
    ]

-- | A nonempty product is represented by a struct.
data ProductDeclr = ProductDeclr
  { pdStructDeclnList :: !C.StructDeclnList
  , pdStructIdent     :: !C.Ident
  }

-- | A nonempty sum is represented by a struct with a union and an enum to
-- disambiguate that union.
data SumDeclr = SumDeclr
  { sdStructIdent :: !C.Ident
  , sdUnionIdent  :: !C.Ident
  , sdEnumIdent   :: !C.Ident
  , sdStructDeclnList :: !C.StructDeclnList
  , sdUnionDeclnList  :: !C.StructDeclnList
  , sdEnumrList       :: !C.EnumrList
  }

type TypeIdentifier = Haskell.TypeRep
type VarIdentifier = String

-- | A monad to ease the expression of code generation, which carries some
-- state and may exit early with error cases.
newtype CodeGenM (t :: Haskell.Type) = CodeGenM
  { runCodeGenM :: ExceptT CodeGenError (StateT CodeGenState Identity) t }

deriving instance Functor CodeGenM
deriving instance Applicative CodeGenM
deriving instance Monad CodeGenM

evalCodeGenM :: CodeGenM t -> (Either CodeGenError t, CodeGenState)
evalCodeGenM cgm = runIdentity (runStateT (runExceptT (runCodeGenM cgm)) initialState)
  where
  initialState = CodeGenState
    { cgsBindings = mempty
    , cgsProducts = mempty
    , cgsSums     = mempty
    }

codeGenError :: CodeGenError -> CodeGenM x
codeGenError err = CodeGenM (throwE err)

maybeError :: CodeGenError -> CodeGenM (Maybe x) -> CodeGenM x
maybeError err act = do
  x <- act
  maybe (codeGenError err) pure x

-- | Make a C identifier from a string. Will fail if the string is malformed
-- w.r.t. valid C identifiers.
stringIdentifier :: String -> CodeGenM (Maybe C.Ident)
stringIdentifier [] = pure Nothing
stringIdentifier (c : cs) = go (NE.reverse (c NE.:| cs))
  where
  go :: NonEmpty Char -> CodeGenM (Maybe C.Ident)
  -- First character (end of list) must not be a digit).
  go (c NE.:| []) = (fmap . fmap) (C.IdentBase . C.IdentNonDigit) (cNonDigit c)
  -- Any other character (not the first) can be a digit or non digit.
  go (c NE.:| (d : cs)) = do
    it <- cDigitOrNonDigit c
    case it of
      Nothing -> pure Nothing
      Just (Left digit) -> do
        mRest <- go (d NE.:| cs)
        pure $ fmap (\rest -> C.IdentCons rest digit) mRest
      Just (Right nonDigit) -> do
        mRest <- go (d NE.:| cs)
        pure $ fmap (\rest -> C.IdentConsNonDigit rest (C.IdentNonDigit nonDigit)) mRest

symbolIdentifier :: forall name . KnownSymbol name => Proxy name -> CodeGenM (Maybe C.Ident)
symbolIdentifier p = stringIdentifier (symbolVal p)

cDigitOrNonDigit :: Char -> CodeGenM (Maybe (Either C.Digit C.NonDigit))
cDigitOrNonDigit c = do
  mDigit <- (fmap . fmap) Left (cDigit c)
  case mDigit of
    Just d -> pure (Just d)
    Nothing -> (fmap . fmap) Right (cNonDigit c)

cNonDigit :: Char -> CodeGenM (Maybe C.NonDigit)
cNonDigit c = case c of
  '_' -> pure . pure $ C.NDUnderscore
  'a' -> pure . pure $ C.NDa
  'b' -> pure . pure $ C.NDb
  'c' -> pure . pure $ C.NDc
  'd' -> pure . pure $ C.NDd
  'e' -> pure . pure $ C.NDe
  'f' -> pure . pure $ C.NDf
  'g' -> pure . pure $ C.NDg
  'h' -> pure . pure $ C.NDh
  'i' -> pure . pure $ C.NDi
  'j' -> pure . pure $ C.NDj
  'k' -> pure . pure $ C.NDk
  'l' -> pure . pure $ C.NDl
  'm' -> pure . pure $ C.NDm
  'n' -> pure . pure $ C.NDn
  'o' -> pure . pure $ C.NDo
  'p' -> pure . pure $ C.NDp
  'q' -> pure . pure $ C.NDq
  'r' -> pure . pure $ C.NDr
  's' -> pure . pure $ C.NDs
  't' -> pure . pure $ C.NDt
  'u' -> pure . pure $ C.NDu
  'v' -> pure . pure $ C.NDv
  'w' -> pure . pure $ C.NDw
  'x' -> pure . pure $ C.NDx
  'y' -> pure . pure $ C.NDy
  'z' -> pure . pure $ C.NDz
  'A' -> pure . pure $ C.NDA
  'B' -> pure . pure $ C.NDB
  'C' -> pure . pure $ C.NDC
  'D' -> pure . pure $ C.NDD
  'E' -> pure . pure $ C.NDE
  'F' -> pure . pure $ C.NDF
  'G' -> pure . pure $ C.NDG
  'H' -> pure . pure $ C.NDH
  'I' -> pure . pure $ C.NDI
  'J' -> pure . pure $ C.NDJ
  'K' -> pure . pure $ C.NDK
  'L' -> pure . pure $ C.NDL
  'M' -> pure . pure $ C.NDM
  'N' -> pure . pure $ C.NDN
  'O' -> pure . pure $ C.NDO
  'P' -> pure . pure $ C.NDP
  'Q' -> pure . pure $ C.NDQ
  'R' -> pure . pure $ C.NDR
  'S' -> pure . pure $ C.NDS
  'T' -> pure . pure $ C.NDT
  'U' -> pure . pure $ C.NDU
  'V' -> pure . pure $ C.NDV
  'W' -> pure . pure $ C.NDW
  'X' -> pure . pure $ C.NDx
  'Y' -> pure . pure $ C.NDZ
  'Z' -> pure . pure $ C.NDZ
  _   -> pure Nothing

cDigit :: Char -> CodeGenM (Maybe C.Digit)
cDigit c = case c of
  '0' -> pure . pure $ C.DZero
  '1' -> pure . pure $ C.DOne
  '2' -> pure . pure $ C.DTwo
  '3' -> pure . pure $ C.DThree
  '4' -> pure . pure $ C.DFour
  '5' -> pure . pure $ C.DFive
  '6' -> pure . pure $ C.DSix
  '7' -> pure . pure $ C.DSeven
  '8' -> pure . pure $ C.DEight
  '9' -> pure . pure $ C.DNine
  _   -> pure Nothing

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

-- | "tag"
ident_tag :: C.Ident
ident_tag =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit (C.IdentBase (C.IdentNonDigit C.NDt)) (C.IdentNonDigit C.NDa))
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


