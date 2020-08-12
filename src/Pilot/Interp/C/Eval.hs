{-|
Module      : Pilot.Interp.C.Eval
Description : Definition of point and stream evaluation in the C CodeGen monad.
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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE BangPatterns #-}

module Pilot.Interp.C.Eval
  ( genTransUnit
  , eval_stream
  , type_info
  ) where

import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.State.Strict (get, gets, modify')

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Sequence as Seq

import Numeric.Natural (Natural)

import qualified Language.C99.AST as C

import Pilot.EDSL.Expr
import Pilot.EDSL.Point (Case (..), Selector (..), Signedness (..), Width (..),
  SignednessRep (..), WidthRep (..))
import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Fun
import Pilot.Types.Logic
import Pilot.Types.Nat
import Pilot.Types.Represented

import qualified Pilot.Interp.Pure as Pure
import Pilot.Interp.C.AST
import Pilot.Interp.C.CodeGen

eval_point :: Expr Point.ExprF (Point s) t -> CodeGen s (Point s t)
eval_point = evalExpr eval_point_expr pure eval_point_bind

eval_stream :: StreamExpr s t -> CodeGen s (Stream s t)
eval_stream = evalExpr eval_stream_expr pure eval_stream_bind

-- | For naming/substitution in the CodeGenM monad: a C declaration is used.
eval_point_bind
  ::  Expr Point.ExprF (Point s) a
  -> (Expr Point.ExprF (Point s) a -> Expr Point.ExprF (Point s) b)
  -> CodeGen s (Point s b)
eval_point_bind pexpr k = do
  pt  <- eval_point pexpr
  pt' <- declare_initialized_point "point_binder" pt
  eval_point (k (value pt'))

-- | Like 'eval_point_bind' but for streams: do the same thing, but behind the
-- offset function.
--
-- TODO ideally, if we make a binding to a memory stream, it doesn't create a
-- new binder, it just uses the name of the static thing.
-- Could do the same for C externs. 
eval_stream_bind
  :: StreamExpr s a
  -> (StreamExpr s a -> StreamExpr s b)
  -> CodeGen s (Stream s b)
eval_stream_bind sexpr k = do
  st  <- eval_stream sexpr
  st' <- declare_initialized_stream "stream_binder" st
  eval_stream (k (value st'))

eval_point_expr
  :: Point.ExprF (Expr Point.ExprF (Point s)) t
  -> CodeGen s (Point s t)
eval_point_expr (Point.IntroInteger tr il)      = eval_intro_integer tr il
eval_point_expr (Point.PrimOp primop)           = eval_primop primop
eval_point_expr (Point.IntroProduct tr fields)  = eval_intro_product tr fields
eval_point_expr (Point.IntroSum tr variant)     = eval_intro_sum tr variant
eval_point_expr (Point.ElimProduct tr sel it)   = eval_elim_product tr it sel
eval_point_expr (Point.ElimSum tr rr it cases)  = eval_elim_sum tr rr it cases

-- Note that the static part must be in the pure interpreter types. With this,
-- we can actually precompute the static parts using the pure interpreter.
--
-- This is essentially a stand-in for universal quantification over the
-- static value and interpreter with a monad constraint on the interpreter (F
-- is Identity). Most expressions will be free in these types so they'll just
-- unify with Pure.Point and Pure.F.

eval_stream_expr :: forall s t . StreamExprF s t -> CodeGen s (Stream s t)
eval_stream_expr (Stream.ConstantStream trep nrep expr)       = eval_constant_stream trep nrep expr
eval_stream_expr (Stream.DropStream trep nrep expr)           = eval_drop_stream trep nrep expr
eval_stream_expr (Stream.ShiftStream trep nrep expr)          = eval_shift_stream trep nrep expr
eval_stream_expr (Stream.MemoryStream trep nrep inits k)      = eval_memory_stream trep nrep inits k
eval_stream_expr (Stream.LiftStream argsrep trep nrep k args) = eval_lift_stream argsrep trep nrep k args

stream_drop
  :: forall s n t .
     Stream s ('Stream.Prefix ('S n) t)
  -> Stream s ('Stream.Prefix     n  t)
stream_drop stream = Stream
  { streamVal       = val
  , streamTypeRep   = typeRep
  , streamCTypeInfo = streamCTypeInfo stream
  }
  where
  typeRep :: Stream.TypeRep Point.TypeRep ('Stream.Prefix n t)
  typeRep = case streamTypeRep stream of
    Stream.Prefix_t (S_t nrep) trep -> Stream.Prefix_t nrep trep

  val :: StreamVal s ('Stream.Prefix n t)
  val = case streamVal stream of
    StreamValNonStatic (VCons _ cs) -> StreamValNonStatic cs
    -- Dropping from a static memory stream: bump the index.
    StreamValStatic   s -> StreamValStatic $ s { ssvOffset = 1 + ssvOffset s }

stream_shift
  :: forall s n t .
     Stream s ('Stream.Prefix ('S n) t)
  -> Stream s ('Stream.Prefix     n  t)
stream_shift stream = Stream
  { streamVal       = val
  , streamTypeRep   = typeRep
  , streamCTypeInfo = streamCTypeInfo stream
  }
  where
  typeRep :: Stream.TypeRep Point.TypeRep ('Stream.Prefix n t)
  typeRep = case streamTypeRep stream of
    Stream.Prefix_t (S_t nrep) trep -> Stream.Prefix_t nrep trep

  val :: StreamVal s ('Stream.Prefix n t)
  val = case streamVal stream of
    StreamValNonStatic vs  -> StreamValNonStatic (vecDropLast vs)
    StreamValStatic   s    -> StreamValStatic s

-- | For integral types we use the C standard explicit types like uint8_t.
--
-- TODO may want this to be in CodeGen and update state to say which headers
-- we need to include?
integer_ident :: SignednessRep signedness -> WidthRep width -> C.Ident
integer_ident Unsigned_t Eight_t     = ident_uint8_t
integer_ident Unsigned_t Sixteen_t   = ident_uint16_t
integer_ident Unsigned_t ThirtyTwo_t = ident_uint32_t
integer_ident Unsigned_t SixtyFour_t = ident_uint64_t
integer_ident Signed_t   Eight_t     = ident_int8_t
integer_ident Signed_t   Sixteen_t   = ident_int16_t
integer_ident Signed_t   ThirtyTwo_t = ident_int32_t
integer_ident Signed_t   SixtyFour_t = ident_int64_t

-- | Get the C type information for a given TypeRep. This includes not only
-- the type specifier but also info about whether it should be taken as a
-- pointer, which is often an important thing to know... Weird that in,
-- "pointer" is not a type specifier, as we might expect from experience in
-- functional languages.
type_info :: CompoundTypeTreatment -> Point.TypeRep t -> CodeGen s CTypeInfo
type_info ctt trep = do
  typeSpec <- declare_type ctt trep
  pure $ CTypeInfo { ctypeSpec = typeSpec, ctypePtr = type_ptr ctt trep }

-- | Use the type rep to fill in the specs and pointer properties of the
-- val record.
--
-- This uses the compound type treatment from the CodeGen context. TODO FIXME
-- this is probably buggy. Must ensure that the expression was generated
-- under the same treatment...
--
-- TODO rename or generalize. This only works for points, not streams.
type_rep_val :: Point.TypeRep ty -> C.CondExpr -> CodeGen s (Point s ty)
type_rep_val trep cexpr = do
  ctt <- compoundTypeTreatment
  tinfo <- type_info ctt trep
  pure $ Point
    { pointExpr      = cexpr
    , pointTypeRep   = trep
    , pointCTypeInfo = tinfo
    }

-- | C pointer information for a given type. If its representation is to be
-- taken always behind a pointer, then this will be Just.
--
-- Empty products and sums are represented using pointers (they are void *).
-- This is true regardless of sharing.
--
-- When in sharing treatment, non-empty sums and products are always pointers.
--
-- This just says whether or not it should be taken by reference. It does
-- not give any C qualifiers on the pointer.

type_ptr :: CompoundTypeTreatment -> Point.TypeRep ty -> Bool

type_ptr _ (Point.Sum_t All)     = True
type_ptr _ (Point.Product_t All) = True

type_ptr Shared (Point.Sum_t (And _ _))     = True
type_ptr Shared (Point.Product_t (And _ _)) = True

type_ptr _ _ = False

-- | The C type specifier. This doesn't include pointer information.
--
-- This must be called before a given type is used, since it ensures that any
-- necessary C declarations will be included.
declare_type :: CompoundTypeTreatment -> Point.TypeRep ty -> CodeGen s C.TypeSpec

-- Integer types use the standard sized variants like uint8_t. These are
-- typedefs.
declare_type _ (Point.Integer_t sr wr) =
  pure $ C.TTypedef $ C.TypedefName (integer_ident sr wr)

-- TODO develop support for rational numbers.
declare_type _ Point.Rational_t = codeGenError $
  CodeGenInternalError "fractional numbers not supported at the moment"

declare_type ctt p@(Point.Product_t _) = declare_product ctt p

declare_type ctt s@(Point.Sum_t _)     = declare_sum ctt s

product_field_prefix :: String
product_field_prefix = "field_"

sum_variant_prefix :: String
sum_variant_prefix = "variant_"

product_field_name :: Natural -> String
product_field_name n = product_field_prefix ++ show n

sum_variant_name :: Natural -> String
sum_variant_name n = sum_variant_prefix ++ show n

-- | Stateful CodeGen term to declare a product. If it has already been
-- declared (something with the same 'Haskell.TypeRep' was declared) then
-- nothing happens.
--
-- Otherwise, we generate a new identifier, and include its struct declaration
-- in the CodeGen declarations list.
declare_product
  :: CompoundTypeTreatment
  -> Point.TypeRep ('Point.Product tys)
  -> CodeGen s C.TypeSpec
declare_product _        (Point.Product_t All)               = pure $ C.TVoid
declare_product ctt trep@(Point.Product_t fields@(And t ts)) = do
  st <- codeGenGet
  let someTypeRep :: Point.SomeTypeRep
      someTypeRep = Point.SomeTypeRep trep
  case Map.lookup someTypeRep (cgsProducts st) of

    -- TODO refactor this and declare_sum (see notes over there).

    Just (SimpleCompoundType ts) -> pure ts

    Just (ComplexCompoundType root tsNotShared tsShared usage) -> case (ctt, usage) of

      (Shared, UsedShared)       -> pure tsShared
      (Shared, UsedBoth)         -> pure tsShared
      (NotShared, UsedNotShared) -> pure tsNotShared
      (NotShared, UsedBoth)      -> pure tsNotShared

      (Shared, UsedNotShared) -> do
        declnList <- field_declns Shared product_field_name 0 (NonEmptyFields fields)
        -- Must generate the union and struct declarations (the enum is already
        -- declared and is shared between shared and not shared representations).
        let !declr' = ComplexCompoundType root tsNotShared tsShared UsedBoth

            suffix :: String
            suffix = "_shared"
            !productIdent = assertValidIdentifier
              ("declare_product bad identifier for " ++ show someTypeRep)
              (stringIdentifier (root ++ suffix))

            productDef = product_defn_type_spec productIdent declnList
            productDecln = C.Decln (C.DeclnSpecsType productDef Nothing) Nothing

            cdeclns = [productDecln]

        codeGenModify $ \st -> 
          st { cgsProducts = Map.insert someTypeRep declr' (cgsProducts st)
             , cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st
             }
        pure tsShared

      (NotShared, UsedShared) -> do
        declnList <- field_declns NotShared product_field_name 0 (NonEmptyFields fields)
        let !declr' = ComplexCompoundType root tsNotShared tsShared UsedBoth

            !productIdent = assertValidIdentifier
              ("declare_product bad identifier for " ++ show someTypeRep)
              (stringIdentifier root)

            productDef = product_defn_type_spec productIdent declnList
            productDecln = C.Decln (C.DeclnSpecsType productDef Nothing) Nothing

            cdeclns = [productDecln]

        codeGenModify $ \st -> 
          st { cgsProducts = Map.insert someTypeRep declr' (cgsProducts st)
             , cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st
             }
        pure tsShared

    Nothing -> do

      let root :: String
          root = "product_" ++ show (Map.size (cgsSums st))
          -- If the type representation is the same for both shared and unshared
          -- then there is only one identifier.
          suffix :: String
          suffix = case ctt of
            Shared    -> if would_share trep then "_shared" else ""
            NotShared -> ""

      -- We always make type specs for both the shared and non-shared
      -- variants, but we don't always put the definitions for both of them into
      -- the CodeGen state.
      let identNotShared = assertValidIdentifier
            ("declare_product bad identifier for " ++ show someTypeRep)
            (stringIdentifier root)
          identShared = assertValidIdentifier
            ("declare_product bad identifier for " ++ show someTypeRep)
            (stringIdentifier (root ++ suffix))

      let typeSpecNotShared = product_decln_type_spec identNotShared
          typeSpecShared = product_decln_type_spec identShared
          usage = case ctt of
            Shared -> UsedShared
            NotShared -> UsedNotShared
          declr =
            if would_share trep
            then ComplexCompoundType root typeSpecNotShared typeSpecShared usage
            else SimpleCompoundType typeSpecNotShared

      codeGenModify $ \st ->
        st { cgsProducts = Map.insert someTypeRep declr (cgsProducts st) }

      declnList <- field_declns ctt product_field_name 0 (NonEmptyFields fields)

      let !productIdent = case ctt of
            NotShared -> identNotShared
            Shared    -> identShared

          productSpec = product_decln_type_spec productIdent
          productDef = product_defn_type_spec productIdent declnList

          productDecln = C.Decln (C.DeclnSpecsType productDef Nothing) Nothing

          cdeclns = [productDecln]

      codeGenModify $ \st ->
        st { cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st }
      pure productSpec

-- | The type spec for the definition of a product, given a name and its fields.
product_decln_type_spec :: C.Ident -> C.TypeSpec
product_decln_type_spec ident = C.TStructOrUnion $
  C.StructOrUnionForwDecln C.Struct ident

product_defn_type_spec :: C.Ident -> C.StructDeclnList -> C.TypeSpec
product_defn_type_spec ident declnList = C.TStructOrUnion $
  C.StructOrUnionDecln C.Struct (Just ident) declnList

-- | Exactly like 'declare_product' but on a different part of the CodeGen
-- state.
declare_sum
  :: CompoundTypeTreatment
  -> Point.TypeRep ('Point.Sum tys)
  -> CodeGen s C.TypeSpec
declare_sum _        (Point.Sum_t All)                 = pure $ C.TVoid
declare_sum ctt trep@(Point.Sum_t variants@(And t ts)) = do
  st <- codeGenGet
  let someTypeRep :: Point.SomeTypeRep
      someTypeRep = Point.SomeTypeRep trep
  case Map.lookup someTypeRep (cgsSums st) of

    -- How's this work exactly?
    --
    -- On first insertion we generate a root name for it (in future could also
    -- take a user-supplied name somehow?) along with the type spec (just
    -- the "struct <name>" part).
    --
    -- We also generate the definitions of the C types needed (an enum, a
    -- union, and a struct) and put them into the CodeGen state so that they
    -- will be declared in the translation unit. Doing this requires recursively
    -- declaring any other compound types in the sum.
    --
    -- If the same type is declared again but with a different variant (shared
    -- or not shared) then we have to add in the missing declarations: the
    -- enum is the same but the union and the struct are different.
    --
    -- TODO factor out the common case of creating and inserting the struct and
    -- union for a given name and declaration list.
    -- Write out the enum definition and insertion once, since it's only done
    -- once.

    Just (SimpleCompoundType ts) -> pure ts

    -- This declaration is already present. We already have the C type specifier
    -- but we may need to add more declarations in case this is first usage of
    -- a shared or unshared variant.
    Just (ComplexCompoundType root tsNotShared tsShared usage) -> case (ctt, usage) of

      (Shared, UsedShared)       -> pure tsShared
      (Shared, UsedBoth)         -> pure tsShared
      (NotShared, UsedNotShared) -> pure tsNotShared
      (NotShared, UsedBoth)      -> pure tsNotShared

      (Shared, UsedNotShared) -> do
        declnList <- field_declns Shared sum_variant_name 0 (NonEmptyFields variants)
        -- Must generate the union and struct declarations (the enum is already
        -- declared and is shared between shared and not shared representations).
        let !declr' = ComplexCompoundType root tsNotShared tsShared UsedBoth

            suffix :: String
            suffix = "_shared"
            !sumIdent = assertValidIdentifier
              ("declare_sum bad identifier for " ++ show someTypeRep)
              (stringIdentifier (root ++ suffix))
            !tagIdent = assertValidIdentifier
              ("declare_sum bad enum identifier for " ++ show someTypeRep)
              (stringIdentifier (root ++ "_tag"))
            !variantIdent = assertValidIdentifier
              ("declare_sum bad union identifier for " ++ show someTypeRep)
              (stringIdentifier (root ++ suffix ++ "_variant"))

            tagSpec = sum_tag_decln_type_spec tagIdent

            variantSpec = sum_variant_decln_type_spec variantIdent
            variantDef = sum_variant_defn_type_spec variantIdent declnList

            sumDef = sum_defn_type_spec sumIdent tagSpec variantSpec

            variantDecln = C.Decln (C.DeclnSpecsType variantDef Nothing) Nothing
            sumDecln = C.Decln (C.DeclnSpecsType sumDef Nothing) Nothing

            cdeclns = [sumDecln, variantDecln]

        codeGenModify $ \st -> 
          st { cgsSums = Map.insert someTypeRep declr' (cgsSums st)
             , cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st
             }
        pure tsShared

      (NotShared, UsedShared) -> do
        declnList <- field_declns NotShared sum_variant_name 0 (NonEmptyFields variants)
        let !declr' = ComplexCompoundType root tsNotShared tsShared UsedBoth

            !sumIdent = assertValidIdentifier
              ("declare_sum bad identifier for " ++ show someTypeRep)
              (stringIdentifier root)
            !tagIdent = assertValidIdentifier
              ("declare_sum bad enum identifier for " ++ show someTypeRep)
              (stringIdentifier root)
            !variantIdent = assertValidIdentifier
              ("declare_sum bad union identifier for " ++ show someTypeRep)
              (stringIdentifier (root ++ "_variant"))

            tagSpec = sum_tag_decln_type_spec tagIdent

            variantSpec = sum_variant_decln_type_spec variantIdent
            variantDef = sum_variant_defn_type_spec variantIdent declnList

            sumDef = sum_defn_type_spec sumIdent tagSpec variantSpec

            variantDecln = C.Decln (C.DeclnSpecsType variantDef Nothing) Nothing
            sumDecln = C.Decln (C.DeclnSpecsType sumDef Nothing) Nothing

            cdeclns = [sumDecln, variantDecln]

        codeGenModify $ \st -> 
          st { cgsSums = Map.insert someTypeRep declr' (cgsSums st)
             , cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st
             }
        pure tsNotShared

    Nothing -> do

      let root :: String
          root = "sum_" ++ show (Map.size (cgsSums st))
          -- If the type representation is the same for both shared and unshared
          -- then there is only one identifier.
          suffix :: String
          suffix = case ctt of
            Shared    -> if would_share trep then "_shared" else ""
            NotShared -> ""

      -- We always make type specs for both the shared and non-shared
      -- variants, but we don't always put the definitions for both of them into
      -- the CodeGen state.
      let identNotShared = assertValidIdentifier
            ("declare_sum bad identifier for " ++ show someTypeRep)
            (stringIdentifier root)
          identShared = assertValidIdentifier
            ("declare_sum bad identifier for " ++ show someTypeRep)
            (stringIdentifier (root ++ suffix))

      let typeSpecNotShared = sum_decln_type_spec identNotShared
          typeSpecShared = sum_decln_type_spec identShared
          usage = case ctt of
            Shared -> UsedShared
            NotShared -> UsedNotShared
          declr =
            if would_share trep
            then ComplexCompoundType root typeSpecNotShared typeSpecShared usage
            else SimpleCompoundType typeSpecNotShared

      codeGenModify $ \st ->
        st { cgsSums = Map.insert someTypeRep declr (cgsSums st) }

      -- This will recursively delcare every type referenced by this one,
      -- updating the CodeGen state to include the necessary C type
      -- declarations.
      declnList <- field_declns ctt sum_variant_name 0 (NonEmptyFields variants)

      -- Now we make the actual definitions of the types.
      -- TODO encapsulate this as it's rather long and will be re-used.
      -- NB: the enum is the same for shared and not shared versions.
      let !sumIdent = case ctt of
            NotShared -> identNotShared
            Shared    -> identShared
          !tagIdent = assertValidIdentifier
            ("declare_sum bad enum identifier for " ++ show someTypeRep)
            (stringIdentifier (root ++ "_tag"))
          !variantIdent = assertValidIdentifier
            ("declare_sum bad union identifier for " ++ show someTypeRep)
            (stringIdentifier (root ++ suffix ++ "_variant"))

          tagSpec = sum_tag_decln_type_spec tagIdent
          tagDef = sum_tag_defn_type_spec tagIdent (NonEmptyFields variants)

          variantSpec = sum_variant_decln_type_spec variantIdent
          variantDef = sum_variant_defn_type_spec variantIdent declnList

          sumSpec = sum_decln_type_spec sumIdent
          sumDef = sum_defn_type_spec sumIdent tagSpec variantSpec

          tagDecln = C.Decln (C.DeclnSpecsType tagDef Nothing) Nothing
          variantDecln = C.Decln (C.DeclnSpecsType variantDef Nothing) Nothing
          sumDecln = C.Decln (C.DeclnSpecsType sumDef Nothing) Nothing

          -- Order is key: they'll appear in the C source in reverse order.
          cdeclns = [sumDecln, variantDecln, tagDecln]

      codeGenModify $ \st ->
        st { cgsTypeDeclns = cdeclns ++ cgsTypeDeclns st }
      pure sumSpec

-- | The type spec for a sum.
sum_decln_type_spec :: C.Ident -> C.TypeSpec
sum_decln_type_spec ident = C.TStructOrUnion $
  C.StructOrUnionForwDecln C.Struct ident

-- | The type spec for the definition of a sum.
sum_defn_type_spec
  :: C.Ident
  -> C.TypeSpec -- ^ Type for the tag.
  -> C.TypeSpec -- ^ Type for the variant.
  -> C.TypeSpec
sum_defn_type_spec ident tagSpec variantSpec = C.TStructOrUnion $
  C.StructOrUnionDecln C.Struct (Just ident) (sum_struct_decln_list tagSpec variantSpec)

-- | A sum is represented by
--
--   struct <name> {
--     enum <tag_name> tag;
--     union <variant_name> variant;
--   };
--
-- Here we define the declaration list (tag and variant) given identifiers for
-- the tag enum and variant union.
sum_struct_decln_list
  :: C.TypeSpec -- ^ Of the tag.
  -> C.TypeSpec -- ^ Of the variant.
  -> C.StructDeclnList
sum_struct_decln_list tagSpec variantSpec = C.StructDeclnCons
  (C.StructDeclnBase $ C.StructDecln
    (C.SpecQualType tagSpec Nothing)
    (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_tag))))
  )
  (C.StructDecln
    (C.SpecQualType variantSpec Nothing)
    (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_variant))))
  )

-- | The type spec for the declaration of a tag for a sum. It's an enum with
-- one variant for each field.
sum_tag_decln_type_spec :: C.Ident -> C.TypeSpec
sum_tag_decln_type_spec ident = C.TEnum $ C.EnumSpecForw ident

sum_tag_defn_type_spec :: C.Ident -> NonEmptyFields -> C.TypeSpec
sum_tag_defn_type_spec ident neFields = C.TEnum $ C.EnumSpec (Just ident) $
  sum_enum_tag_declns 0 neFields

-- | Make enum declarations to serve as the tags for a sum representation.
sum_enum_tag_declns :: Natural -> NonEmptyFields -> C.EnumrList
sum_enum_tag_declns n (NonEmptyFields (And _ All)) =
  let !ident = assertValidIdentifier
        ("sum_enum_tag_declns bad identifier")
        (stringIdentifier ("tag_" ++ show n))
  in  C.EnumrBase $ C.Enumr $ C.Enum ident
sum_enum_tag_declns n (NonEmptyFields (And _ ts@(And _ _))) =
  let !ident = assertValidIdentifier
        ("sum_enum_tag_declns bad identifier")
        (stringIdentifier ("tag_" ++ show n))
      !subList = sum_enum_tag_declns (n+1) (NonEmptyFields ts)
  in  C.EnumrCons subList $ C.Enumr $ C.Enum ident

-- | The type spec for the declaration of the variant for a sum. It's a union
-- with one item for each sum variant.
--
-- Just like 'product_decln_type_spec'
sum_variant_decln_type_spec :: C.Ident -> C.TypeSpec
sum_variant_decln_type_spec ident = C.TStructOrUnion $
  C.StructOrUnionForwDecln C.Union ident

sum_variant_defn_type_spec :: C.Ident -> C.StructDeclnList -> C.TypeSpec
sum_variant_defn_type_spec ident declnList = C.TStructOrUnion $
  C.StructOrUnionDecln C.Union (Just ident) declnList

-- | The struct/union declaration list for product and sum types. For products,
-- this will give the struct fields; for sums, the union variants.
--
-- They will all be qualified with const.
--
-- This will put the fields in reverse order, since the C declaration list
-- type is defines like a snoc-list. Doesn't really matter though.
--
-- If the compound type treatment is Shared, then compound types which appear
-- as fields here will be const restrict pointers.
--
-- TODO consider factoring this: given NonEmptyFields, get CTypeInfo for each,
-- in the CodeGen monad, then another function which takes a NonEmpty CTypeInfo
-- and String and Natural and generates the StructDeclnList.
field_declns
  :: CompoundTypeTreatment
  -> (Natural -> String) -- ^ accessor name constructor
  -> Natural -- ^ Initial disambiguator. Call this will 0.
  -> NonEmptyFields
  -> CodeGen s C.StructDeclnList

field_declns ctt mkName n (NonEmptyFields (And t All)) = do
  info <- type_info ctt t
  let !ident = assertValidIdentifier 
        ("field_declns bad identifier")
        (stringIdentifier (mkName n))
      mPtr :: Maybe C.Ptr
      mPtr = if ctypePtr info
             then Just $ C.PtrBase (Just (C.TypeQualBase C.QRestrict))
             else Nothing
      -- It's _almost_ possible to put const on all struct and union fields,
      -- but for sum elimination, which uses an uninitialized variable for the
      -- result and therefore rules this out.
      qualList :: C.SpecQualList
      qualList = C.SpecQualType (ctypeSpec info) $ Nothing
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr mPtr $
        C.DirectDeclrIdent ident
  pure $ C.StructDeclnBase $ C.StructDecln qualList declrList

field_declns ctt mkName n (NonEmptyFields (And t (And t' ts))) = do
  subList <- field_declns ctt mkName (n+1) (NonEmptyFields (And t' ts))
  info <- type_info ctt t
  let !ident = assertValidIdentifier
        ("field_declns bad identifier")
        (stringIdentifier (mkName n))
      -- NEVER const pointers in structs or unions, since then we cannot have
      -- an uninitialized variable of them.
      mPtr :: Maybe C.Ptr
      mPtr = if ctypePtr info
             then Just $ C.PtrBase (Just (C.TypeQualBase C.QRestrict))
             else Nothing
      qualList :: C.SpecQualList
      qualList = C.SpecQualType (ctypeSpec info) $ Nothing
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr mPtr $
        C.DirectDeclrIdent ident
  pure $ C.StructDeclnCons subList $ C.StructDecln qualList declrList

integer_literal
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Point.IntegerLiteral signedness width
  -> C.CondExpr

integer_literal (Point.Integer_t Unsigned_t _) il = constIsCondExpr $
  C.ConstInt $ C.IntHex (hex_const (absolute_value il)) Nothing

integer_literal (Point.Integer_t Signed_t _) il =
  if is_negative il
  then unaryExprIsCondExpr $ C.UnaryOp C.UOMin $ constIsCastExpr $ C.ConstInt $
        C.IntHex (hex_const (absolute_value il)) Nothing
  else constIsCondExpr $ C.ConstInt $ C.IntHex (hex_const (absolute_value il)) Nothing

eval_intro_integer
  :: forall signedness width s .
     Point.TypeRep ('Point.Integer signedness width)
  -> Point.IntegerLiteral signedness width
  -> CodeGen s (Point s ('Point.Integer signedness width))

eval_intro_integer tr il = type_rep_val tr (integer_literal tr il)

is_negative :: Point.IntegerLiteral 'Signed width -> Bool
is_negative (Point.Int8 i8)   = i8 < 0
is_negative (Point.Int16 i16) = i16 < 0
is_negative (Point.Int32 i32) = i32 < 0
is_negative (Point.Int64 i64) = i64 < 0

absolute_value :: Point.IntegerLiteral signedness width -> Natural
absolute_value (Point.UInt8  w8)  = fromIntegral w8
absolute_value (Point.UInt16 w16) = fromIntegral w16
absolute_value (Point.UInt32 w32) = fromIntegral w32
absolute_value (Point.UInt64 w64) = fromIntegral w64
absolute_value (Point.Int8   i8)  = fromIntegral (abs i8)
absolute_value (Point.Int16  i16) = fromIntegral (abs i16)
absolute_value (Point.Int32  i32) = fromIntegral (abs i32)
absolute_value (Point.Int64  i64) = fromIntegral (abs i64)

eval_primop
  :: Point.PrimOpF (Expr Point.ExprF (Point s)) t
  -> CodeGen s (Point s t)
eval_primop (Point.Arithmetic arithop) = eval_arithop arithop
eval_primop (Point.Bitwise bitop)      = eval_bitop bitop
eval_primop (Point.Relative relop)     = eval_relop relop

eval_arithop
  :: Point.ArithmeticOpF (Expr Point.ExprF (Point s)) t
  -> CodeGen s (Point s t)
eval_arithop (Point.AddInteger tr x y) = eval_add_integer tr x y
eval_arithop (Point.SubInteger tr x y) = eval_sub_integer tr x y
eval_arithop (Point.MulInteger tr x y) = eval_mul_integer tr x y
eval_arithop (Point.DivInteger tr x y) = eval_div_integer tr x y
eval_arithop (Point.ModInteger tr x y) = eval_mod_integer tr x y
eval_arithop (Point.NegInteger tr x)   = eval_neg_integer tr x

-- | The `signedness` and `width` meta-language types ensure that the two
-- integers are of the same type.
eval_add_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_add_integer tr vx vy = do
  x <- eval_point vx
  y <- eval_point vy
  let expr = addExprIsCondExpr $ C.AddPlus
        (condExprIsAddExpr  (pointExpr x))
        (condExprIsMultExpr (pointExpr y))
  type_rep_val tr expr

eval_sub_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_sub_integer tr vx vy = do
  x <- eval_point vx
  y <- eval_point vy
  let expr = addExprIsCondExpr $ C.AddMin
        (condExprIsAddExpr  (pointExpr x))
        (condExprIsMultExpr (pointExpr y))
  type_rep_val tr expr

eval_mul_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_mul_integer tr vx vy = do
  x <- eval_point vx
  y <- eval_point vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultMult
        (condExprIsMultExpr (pointExpr x))
        (condExprIsCastExpr (pointExpr y))
  type_rep_val tr expr

eval_div_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_div_integer tr vx vy = do
  x <- eval_point vx
  y <- eval_point vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultDiv
        (condExprIsMultExpr (pointExpr x))
        (condExprIsCastExpr (pointExpr y))
  type_rep_val tr expr

eval_mod_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_mod_integer tr vx vy = do
  x <- eval_point vx
  y <- eval_point vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultMod
        (condExprIsMultExpr (pointExpr x))
        (condExprIsCastExpr (pointExpr y))
  type_rep_val tr expr

eval_neg_integer
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_neg_integer tr vx = do
  x <- eval_point vx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOMin $
        condExprIsCastExpr (pointExpr x)
  type_rep_val tr expr

eval_bitop
  :: Point.BitwiseOpF (Expr Point.ExprF (Point s)) t
  -> CodeGen s (Point s t)
eval_bitop (Point.AndB tr x y)   = eval_and_bitwise tr x y
eval_bitop (Point.OrB  tr x y)   = eval_or_bitwise  tr x y
eval_bitop (Point.XOrB tr x y)   = eval_xor_bitwise tr x y
eval_bitop (Point.NotB tr x)     = eval_not_bitwise tr x
eval_bitop (Point.ShiftL tr x y) = eval_shiftl_bitwise tr x y
eval_bitop (Point.ShiftR tr x y) = eval_shiftr_bitwise tr x y

eval_and_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_and_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = andExprIsCondExpr $ C.And
        (condExprIsAndExpr (pointExpr x))
        (condExprIsEqExpr  (pointExpr y))
  type_rep_val tr expr

eval_or_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_or_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = orExprIsCondExpr $ C.Or
        (condExprIsOrExpr  (pointExpr x))
        (condExprIsXOrExpr (pointExpr y))
  type_rep_val tr expr

eval_xor_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_xor_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = xorExprIsCondExpr $ C.XOr
        (condExprIsXOrExpr (pointExpr x))
        (condExprIsAndExpr (pointExpr y))
  type_rep_val tr expr

eval_not_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_not_bitwise tr bx = do
  x <- eval_point bx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOBNot
        (condExprIsCastExpr (pointExpr x))
  type_rep_val tr expr

eval_shiftl_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer 'Unsigned 'Eight)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_shiftl_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = shiftExprIsCondExpr $ C.ShiftLeft
        (condExprIsShiftExpr (pointExpr x))
        (condExprIsAddExpr   (pointExpr y))
  type_rep_val tr expr

eval_shiftr_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer 'Unsigned 'Eight)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_shiftr_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = shiftExprIsCondExpr $ C.ShiftRight
        (condExprIsShiftExpr (pointExpr x))
        (condExprIsAddExpr   (pointExpr y))
  type_rep_val tr expr

eval_relop
  :: Point.RelativeOpF (Expr Point.ExprF (Point s)) t
  -> CodeGen s (Point s t)
eval_relop (Point.Cmp trep trepr x y lt eq gt) = eval_cmp trep trepr x y lt eq gt

eval_cmp
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Point.TypeRep r
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) r
  -> Expr Point.ExprF (Point s) r
  -> Expr Point.ExprF (Point s) r
  -> CodeGen s (Point s r)
eval_cmp _trep trepr vx vy lt eq gt = do
  -- TODO what to do here though? The EDSL mandates that compare gives an
  -- ordering, which is a sum type.
  -- I find it weird that any evaluation thing would have to evaluate an
  -- _expression_.
  -- Wouldn't it be better to have Cmp take 2 integers and 3 cases?
  --
  -- We elaborate all 3 cases here.
  -- The ternary operator which we generate ensures that only one of them is
  -- actually evaluated in the object-language
  lessThan    <- eval_point lt
  greaterThan <- eval_point gt
  equalTo     <- eval_point eq
  x <- eval_point vx
  y <- eval_point vy
  let isLt :: C.RelExpr
      isLt = C.RelLT (condExprIsRelExpr (pointExpr x)) (condExprIsShiftExpr (pointExpr y))
      isGt :: C.RelExpr
      isGt = C.RelGT (condExprIsRelExpr (pointExpr x)) (condExprIsShiftExpr (pointExpr y))
      expr = C.Cond (relExprIsLOrExpr isLt) (condExprIsExpr (pointExpr lessThan)) $
             C.Cond (relExprIsLOrExpr isGt) (condExprIsExpr (pointExpr greaterThan)) $
                                            (pointExpr equalTo)
  type_rep_val trepr expr

eval_constant_stream
  :: Point.TypeRep t
  -> NatRep n
  -> Expr Point.ExprF (Point s) t
  -> CodeGen s (Stream s ('Stream.Prefix n t))
eval_constant_stream trep nrep pexpr = do
  point <- eval_point pexpr
  let genPoint = pure (pointExpr point)
      pvec = VCons genPoint (vecReplicate nrep genPoint)
  pure $ Stream
    { streamVal       = StreamValNonStatic pvec
    , streamTypeRep   = Stream.Prefix_t nrep (pointTypeRep point)
    , streamCTypeInfo = pointCTypeInfo point
    }

eval_drop_stream
  :: Point.TypeRep t
  -> NatRep ('S n)
  -> Expr
       (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point))
       (Stream s)
       ('Stream.Prefix ('S n) t)
  -> CodeGen s (Stream s ('Stream.Prefix n t))
eval_drop_stream trep nrep expr = do
  stream <- eval_stream expr
  pure $ stream_drop stream

eval_shift_stream
  :: Point.TypeRep t
  -> NatRep ('S n)
  -> Expr
       (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point))
       (Stream s)
       ('Stream.Prefix ('S n) t)
  -> CodeGen s (Stream s ('Stream.Prefix n t))
eval_shift_stream trep nrep expr = do
  stream <- eval_stream expr
  pure $ stream_shift stream

eval_lift_stream
  :: forall args s n r .
     Args Point.TypeRep args
  -> Point.TypeRep r
  -> NatRep n
  -> (Args (Expr Point.ExprF (Point s)) args -> Expr Point.ExprF (Point s) r)
  -> Args (StreamExpr s) (MapArgs ('Stream.Prefix n) args)
  -> CodeGen s (Stream s ('Stream.Prefix n r))
eval_lift_stream argsrep trep nrep k args = do

  ctt <- compoundTypeTreatment
  tinfo <- type_info ctt trep

  -- Evaluate all of the stream arguments.
  streamArgs :: Args (Stream s) (MapArgs ('Stream.Prefix n) args)
    <- traverseArgs eval_stream args

  -- If this stream has a nonzero prefix, we do not elaborate the code at
  -- all offsets. Instead we use a function
  --   Offset n -> CodeGen s C.CondExpr
  --
  let genAtOffset :: Offset n -> CodeGen s C.CondExpr
      genAtOffset = \offset -> do
        args <- streamArgsToPointArgs offset nrep argsrep streamArgs
        let pexpr = k args
        point <- eval_point pexpr
        return $ pointExpr point

      -- What we need is a vector of CodeGens such that, for each offset,
      -- it runs the function at that offset.
      vec :: Vec ('S n) (CodeGen s C.CondExpr)
      vec = vecGenerateWithOffset nrep genAtOffset

      streamVal :: StreamVal s ('Stream.Prefix n t)
      streamVal = StreamValNonStatic vec

  pure $ Stream
    { streamVal       = streamVal
    , streamTypeRep   = Stream.Prefix_t nrep trep
    , streamCTypeInfo = tinfo
    }

eval_memory_stream
  :: forall s n t .
     Point.TypeRep t
  -> NatRep ('S n)
  -> Vec ('S n) (Expr Point.ExprF Pure.Point t)
  -> (   Expr (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point)) (Stream s) ('Stream.Prefix n t)
      -> Expr (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point)) (Stream s) ('Stream.Prefix 'Z t)
     )
  -> CodeGen s (Stream s ('Stream.Prefix ('S n) t))
eval_memory_stream trep nrep initExprs k = do

  -- Storing in stream: always not shared, since we must copy the entire data
  -- structure to the static area.
  tinfo <- type_info NotShared trep

  -- Evaluate the initial portion and compute things related to its size
  -- Since we require that the "static" parts of the expression unify with
  -- the pure interpreter types, we can actually precompute them using that
  -- interpreter. This means that these expressions will certainly be suitable
  -- for C static array initializers (no function calls, no variable bindings).
  let initPoints :: Vec ('S n) (Pure.Point t)
      !initPoints = vecMap Pure.eval_point initExprs

      arrayLength :: Natural
      !arrayLength = vecLength initPoints

      sizeIntConst :: C.IntConst
      !sizeIntConst = C.IntHex (hex_const (1 + arrayLength)) Nothing

      sizeMinusOneIntConst :: C.IntConst
      !sizeMinusOneIntConst = C.IntHex (hex_const arrayLength) Nothing

      !widthRep =
        if arrayLength <= 0xFE
        then Point.SomeWidthRep Point.Eight_t
        else if arrayLength <= 0xFFFE
        then Point.SomeWidthRep Point.Sixteen_t
        -- Ok, having a vector of this size would cause GHC to implode, but oh
        -- well let's be thorough.
        else if arrayLength <= 0xFFFFFFFE
        then Point.SomeWidthRep Point.ThirtyTwo_t
        else Point.SomeWidthRep Point.SixtyFour_t

  !(arrayPoints :: NonEmpty (Point s t)) <- traverse (pure_point trep) (vecToNonEmpty initPoints)
  let arrayInits :: NonEmpty C.CondExpr
      arrayInits = fmap pointExpr arrayPoints

  -- Using the code gen state we can come up with fresh names for the static
  -- data: array, index, and copy
  -- We compute it from the size of the list of streams, so it's essential that
  -- we update that list before doing any recursion.
  n :: Natural <- codeGenGets $ fromIntegral . Seq.length . cgsStaticStreams

  let !arrayIdentifier = assertValidStringIdentifier ("memory_array_" ++ show n)
      !indexIdentifier = assertValidStringIdentifier ("memory_index_" ++ show n)

      sval :: StaticStreamVal
      sval = StaticStreamVal
        { ssvIndex  = indexIdentifier
        , ssvArray  = arrayIdentifier
        -- Size is 1 plus the init length; the extra cell functions as the
        -- write position.
        , ssvSize   = 1 + arrayLength
        , ssvOffset = 0
        }

      stream :: Stream s ('Stream.Prefix ('S n) t)
      stream = Stream
        { streamVal       = StreamValStatic sval
        , streamTypeRep   = Stream.Prefix_t nrep trep
        , streamCTypeInfo = tinfo
        }

      nrep' :: NatRep n
      nrep' = case nrep of
        S_t n -> n

      -- NB: it's `n`, not `'S n`.
      streamRec :: Stream s ('Stream.Prefix n t)
      streamRec = Stream
        { streamVal       = StreamValStatic sval
        , streamTypeRep   = Stream.Prefix_t nrep' trep
        , streamCTypeInfo = tinfo
        }

      !sms = StaticMemoryStream
        { smsArrayIdent  = arrayIdentifier
        , smsIndexIdent  = indexIdentifier
        , smsCSize       = sizeIntConst
        , smsWriteOffset = sizeMinusOneIntConst
        , smsSizeWidth   = widthRep
        -- The array inits are in reverse order. Just an annoyance of the
        -- C99 AST definitions.
        , smsArrayInits  = NE.reverse arrayInits
        , smsCTypeInfo   = tinfo
        }

  codeGenModify $ \cgs -> cgs
    { cgsStaticStreams = cgsStaticStreams cgs Seq.|> sms
    }

  -- Since we've already updated the streams list, recursive calls will give
  -- unique names to other memory streams.
  sval' <- eval_stream (k (value streamRec))
  nextValueExpr <- streamExprNow (streamVal sval')

  -- This block item updates the stream at the "write index"
  let bi = staticMemoryStreamUpdateArrayBlockItem sms (condExprIsAssignExpr nextValueExpr)

  codeGenModify $ \cgs -> cgs
    { cgsBlockItems    = bi : cgsBlockItems cgs
    }

  pure stream

-- | Make a C Point from a pure evaluation of a point (Pilot.Pure). This
-- is effectively pre-computation / constant folding or whatever.
pure_point :: forall s t . Point.TypeRep t -> Pure.Point t -> CodeGen s (Point s t)

pure_point trep (Pure.UInt8  w8)  = type_rep_val trep $ integer_literal trep (Point.UInt8  w8)
pure_point trep (Pure.UInt16 w16) = type_rep_val trep $ integer_literal trep (Point.UInt16 w16)
pure_point trep (Pure.UInt32 w32) = type_rep_val trep $ integer_literal trep (Point.UInt32 w32)
pure_point trep (Pure.UInt64 w64) = type_rep_val trep $ integer_literal trep (Point.UInt64 w64)

pure_point trep (Pure.Int8  i8)   = type_rep_val trep $ integer_literal trep (Point.Int8   i8)
pure_point trep (Pure.Int16 i16)  = type_rep_val trep $ integer_literal trep (Point.Int16  i16)
pure_point trep (Pure.Int32 i32)  = type_rep_val trep $ integer_literal trep (Point.Int32  i32)
pure_point trep (Pure.Int64 i64)  = type_rep_val trep $ integer_literal trep (Point.Int64  i64)

pure_point trep@(Point.Product_t ts) (Pure.Product ps) = do
  fields <- traverseAll recurse annotated
  intro_product trep fields
  where

  -- For each of the points we take its corresponding TypeRep so that we
  -- can recurse on it with pureExpr.
  annotated = zipAll P ts ps

  recurse
    :: forall x s .
       (Point.TypeRep :*: Pure.Point) x
    -> CodeGen s (Point s x)
  recurse (P trep point) = pure_point trep point

pure_point trep@(Point.Sum_t ts) (Pure.Sum ps) = do
  variant <- traverseAny recurse annotated
  intro_sum trep variant
  where

  annotated = zipAny P ts ps

  recurse
    :: forall x s .
       (Point.TypeRep :*: Pure.Point) x
    -> CodeGen s (Point s x)
  recurse (P trep point) = pure_point trep point

intro_product
  :: Point.TypeRep ('Point.Product fields)
  -> All (Point s) fields
  -> CodeGen s (Point s ('Point.Product fields))

-- Empty products are NULL pointers. You can introduce them but you cannot
-- eliminate them (they contain no information) so it's all good.
intro_product trep All = type_rep_val trep cNULL

intro_product trep@(Point.Product_t (And _ _)) (And t ts) = do
  ctt <- compoundTypeTreatment
  typeSpec <- declare_product ctt trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
      initList = product_field_inits ctt 0 t ts
      pexpr = C.PostfixInits typeName initList
      expr  = case ctt of
        Shared    -> reference (postfixExprIsCondExpr pexpr)
        NotShared -> postfixExprIsCondExpr pexpr
  type_rep_val trep expr

intro_sum
  :: Point.TypeRep ('Point.Sum variants)
  -> Any (Point s) variants variant
  -> CodeGen s (Point s ('Point.Sum variants))

-- The meta-language doesn't allow for empty sums to be introduced (void type
-- in the algebraic sense).
intro_sum (Point.Sum_t All) it = case it of {}

intro_sum trep@(Point.Sum_t ts@(And _ _)) anyt = do
  ctt <- compoundTypeTreatment
  typeSpec <- declare_sum ctt trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
      initList = sum_field_inits ctt ts anyt
      pexpr = C.PostfixInits typeName initList
      expr = case ctt of
        Shared    -> reference (postfixExprIsCondExpr pexpr)
        NotShared -> postfixExprIsCondExpr pexpr
  type_rep_val trep expr

product_field_inits
  :: CompoundTypeTreatment
  -> Natural
  -> Point s t
  -> All (Point s) ts
  -> C.InitList

product_field_inits ctt n point All =
  -- With shared compound type treatment, all compound types which appear in
  -- other compound types are by reference.
  -- TODO think of a way to organize this to be less ad-hoc.
  let !expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep point))
          then reference (pointExpr point)
          else pointExpr point
        NotShared -> pointExpr point
      !designator = assertValidDesignator "product_field" (product_field_name n)
  in  C.InitBase (Just designator) (C.InitExpr (condExprIsAssignExpr expr))

product_field_inits ctt n point (And p ps) =
  let !expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep point))
          then reference (pointExpr point)
          else pointExpr point
        NotShared -> pointExpr point
      !designator = assertValidDesignator "product_field" (product_field_name n)
      !subList = product_field_inits ctt (n+1) p ps
  in C.InitCons subList (Just designator) (C.InitExpr (condExprIsAssignExpr expr))

-- | Product intro: give all conjuncts and get the product. Since products are
-- structs, this corresponds to a struct initializer with a field for each
-- conjunct.
eval_intro_product
  :: Point.TypeRep ('Point.Product types)
  -> All (Expr Point.ExprF (Point s)) types
  -> CodeGen s (Point s ('Point.Product types))
eval_intro_product trep exprs = do
  fields <- traverseAll eval_point exprs
  intro_product trep fields

-- | Product elimination is just a field accessor.
eval_elim_product
  :: forall fields field s .
     Point.TypeRep ('Point.Product fields)
  -> Any Point.Selector fields field
  -> Expr Point.ExprF (Point s) ('Point.Product fields)
  -> CodeGen s (Point s field)
eval_elim_product trep@(Point.Product_t fields) selector t = do
  ctt <- compoundTypeTreatment
  -- We don't need the type spec itself, but we do need to ensure that it is
  -- declared.
  _typeSpec <- declare_product ctt trep
  point <- eval_point t
  let pexpr = condExprIsPostfixExpr $ dereferenceIf (pointPtr point) (pointExpr point)
  eval_elim_product_with_selector ctt trepF 0 pexpr selector
  where
  trepF :: Point.TypeRep field
  trepF = case oneOf fields selector of
    P field _ -> field

-- |
--
-- From the field selector we can determine
-- - The name of the field selector to use
-- - A meta-language function to generate the rest of the expression using that
--   object-language selector and struct
--
eval_elim_product_with_selector
  :: CompoundTypeTreatment
  -> Point.TypeRep field
  -> Natural
  -> C.PostfixExpr -- ^ The C expression giving the product struct, fully dereferenced
                   -- so that the . accessor is appropriate.
  -> Any Selector fields field
  -> CodeGen s (Point s field)

eval_elim_product_with_selector ctt trep n pexpr (Or sel) =
  eval_elim_product_with_selector ctt trep (n+1) pexpr sel

eval_elim_product_with_selector ctt trep n pexpr (Any Selector) = do
  let !fieldIdent = assertValidIdentifier
        ("eval_elim_product_with_selector bad field " ++ show n)
        (stringIdentifier (product_field_name n))
      expr = postfixExprIsCondExpr $ C.PostfixDot pexpr fieldIdent
  type_rep_val trep expr

-- |
--
-- Like for empty products, empty sums are also void* so that we can just use
-- NULL and not allocate anything.
--
eval_intro_sum
  :: Point.TypeRep ('Point.Sum variants)
  -> Any (Expr Point.ExprF (Point s)) variants variant
  -> CodeGen s (Point s ('Point.Sum variants))
eval_intro_sum trep any = do
  variant <- traverseAny eval_point any
  intro_sum trep variant

-- | The init list for a sum struct: its tag and its variant.
sum_field_inits
  :: CompoundTypeTreatment
  -> All Point.TypeRep variants -- ^ So that we can get `Point.TypeRep variant`
  -> Any (Point s) variants variant
  -> C.InitList
sum_field_inits ctt treps anyt = C.InitCons
  (C.InitBase (Just (ident_designator ident_tag)) (C.InitExpr tagExpr))
  (Just (ident_designator ident_variant))
  -- Sad naming convention from the spec: it's not initializing an array, it's
  -- just an array of initializers. It's how we get to give an initializer
  -- without specifying the union type name.
  (C.InitArray variantInitList)
  where
  !tagExpr = condExprIsAssignExpr (sum_tag_expr 0 anyt)
  !variantInitList = sum_variant_init_list ctt treps 0 anyt

-- | The expression for a sum's tag: determined by the offset in the disjuncts
-- in the type signature, and the common "tag_" prefix.
sum_tag_expr :: Natural -> Any f ts t -> C.CondExpr
sum_tag_expr n (Or there) = sum_tag_expr (n+1) there
sum_tag_expr n (Any _) =
  let !ident = assertValidIdentifier
        ("sum_tag_expr invalid tag field " ++ show n)
        (stringIdentifier ("tag_" ++ show n))
  in  primExprIsCondExpr $ C.PrimIdent ident

-- | The variant expression for a sum: it's a union literal, _without_ a
-- pointer (sums hold their tags and unions directly).
sum_variant_init_list
  :: CompoundTypeTreatment
  -> All Point.TypeRep variants
  -> Natural
  -> Any (Point s) variants variant
  -> C.InitList

sum_variant_init_list ctt (And _ treps) n (Or there) =
  sum_variant_init_list ctt treps (n+1) there

sum_variant_init_list ctt trep n (Any point) =
  -- TODO factor out this little pattern here, it's used also in product
  -- introduction.
  let !expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep point))
          then reference (pointExpr point)
          else pointExpr point
        NotShared -> pointExpr point
      !designator = assertValidDesignator "sum_variant_init_list" (sum_variant_name n)
      !initExpr = C.InitExpr (condExprIsAssignExpr expr)
  in  C.InitBase (Just designator) initExpr

-- | Sum elimination is the most complex of the basic expressions. Since each
-- branch may induce bindings, each branch needs its own scope. Thus we cannot
-- get away with using nested ternary expressions here, we have to use if/else
-- or a switch on the tag. We choose a switch.
--
-- We also make two variable declarations:
-- - The scrutinee (the sum itself)
-- - The result (uninitialized)
-- The switch is on the scrutinee tag, each cases statement referencing the
-- relevant enum constructor. Within each case is a compound statement (a new
-- scope) which will use the variant union under an assumed type.
-- Each of these compound statements will, as its final 2 statements, assign the
-- result value, and break out of the switch.
--
-- The resulting expression for this elimination is simply the identifier of
-- the result. The preceding statements go into the CodeGen state.
eval_elim_sum
  :: Point.TypeRep ('Point.Sum types)
  -> Point.TypeRep r
  -> Expr Point.ExprF (Point s) ('Point.Sum types)
  -> All (Case (Expr Point.ExprF (Point s)) r) types
  -> CodeGen s (Point s r)
eval_elim_sum trep rrep t cases = do
  ctt <- compoundTypeTreatment
  -- We don't need the type spec itself, but we do need to ensure that it is
  -- declared.
  _typeSpec <- declare_sum ctt trep
  rinfo <- type_info ctt rrep
  point <- eval_point t
  -- Our two declarations: scrutinee and result.
  -- Declaring the scrutinee is important, so that we don't _ever_ have a case
  -- statement in which the scrutinee is repeatedly constructed at each case.
  scrutineePoint <- declare_initialized_point "scrutinee" point
  resultIdent    <- declare_uninitialized     "result"    rinfo
  let resultPoint = Point
        { pointExpr      = identIsCondExpr resultIdent
        , pointTypeRep   = rrep
        , pointCTypeInfo = rinfo
        }
  -- We take two expressions in the object-language (forgetting their
  -- meta-language types): the sum's tag and its variant. The arrow accessor
  -- is never used, we manually derefernece if needed.
  let tagPostfixExpr :: C.PostfixExpr
      tagPostfixExpr = C.PostfixDot
        (condExprIsPostfixExpr (dereferenceIf (pointPtr scrutineePoint) (pointExpr scrutineePoint)))
        ident_tag
      tagExpr :: C.Expr
      tagExpr = postfixExprIsExpr tagPostfixExpr
      variantExpr = C.PostfixDot
        (condExprIsPostfixExpr (dereferenceIf (pointPtr scrutineePoint) (pointExpr scrutineePoint)))
        ident_variant
  -- If the sum is empty, the result is a switch statement with no cases behind
  -- it. That's a no-op. The result variable will remain undefined.
  -- Should be you can never introduce an empty sum, so this code should not
  -- be reachable.
  (caseBlockItems :: [C.BlockItem]) <- case trep of
    Point.Sum_t All       -> pure []
    Point.Sum_t (And _ _) -> NE.toList <$> eval_elim_sum_cases ctt 0 rrep
      (postfixExprIsEqExpr tagPostfixExpr)
      variantExpr
      resultIdent
      cases
  let casesStmt :: C.Stmt
      casesStmt = C.StmtCompound $ C.Compound $ blockItemList caseBlockItems
      switchItem :: C.BlockItem
      switchItem = C.BlockItemStmt $ C.StmtSelect $ C.SelectSwitch tagExpr casesStmt
  addBlockItem switchItem
  pure resultPoint

-- | Makes the cases in a switch statement for a sum elimination.
eval_elim_sum_cases
  :: forall s r ty tys .
     CompoundTypeTreatment
  -> Natural
  -> Point.TypeRep r
  -> C.EqExpr -- ^ The tag of the sum
  -> C.PostfixExpr -- ^ The variant of the sum
  -> C.Ident -- ^ Identifier of the place to assign the result.
  -> All (Case (Expr Point.ExprF (Point s)) r) (ty ': tys)
  -> CodeGen s (NonEmpty C.BlockItem)
eval_elim_sum_cases ctt n rrep tagExpr variantExpr resultIdent (And (Case trep k) cases) = do
  -- We need the identifiers for the enum tag, and the union variant, at this
  -- case.
  tagIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (pure (stringIdentifier ("tag_" ++ show n)))
  variantIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (pure (stringIdentifier (sum_variant_name n)))
  -- This block item is
  --
  --   case tagIdent:
  --   {
  --     // compute x using scrutinee->variantIdent
  --     ...
  --     result = x;
  --     break;
  --   }
  --
  -- To get the block item list to put before the result and the break, we
  -- have to run the code gen behind the continuation k, with a new scope.
  --
  -- This is always (.) rather than (->) since sum structs always hold their
  -- variants (and their tags) directly.
  let valueSelector :: C.PostfixExpr
      valueSelector = C.PostfixDot variantExpr variantIdent
  valInThisCase :: Point s ty <- type_rep_val trep (postfixExprIsCondExpr valueSelector)
  -- NB: with the new scope we evaluate a _point_ not a stream. That means
  -- that we'll never, for instance, only update a memory stream, or only
  -- update an extern output, within only one case elimination block.
  -- TODO check on that. Should be ok, since `value valInThisCase` will never
  -- elaborate to anything that needs to happen at the top level of the
  -- evaluation function.
  (expr, blockItems) <- withNewScope $ eval_point (k (value valInThisCase))
  let -- Here we have the result assignment and the case break, the final two
      -- statements in the compound statement.
      resultAssignment :: C.BlockItem
      resultAssignment = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $
        C.ExprAssign $ C.Assign
          (identIsUnaryExpr resultIdent)
          C.AEq
          (condExprIsAssignExpr (pointExpr expr))
      caseBreak :: C.BlockItem
      caseBreak = C.BlockItemStmt $ C.StmtJump $ C.JumpBreak
      theBlockItemList :: C.BlockItemList
      theBlockItemList = blockItemListNE (caseBreak NE.:| (resultAssignment : blockItems))
      caseBody :: C.Stmt
      caseBody = C.StmtCompound $ C.Compound $ Just $ theBlockItemList
      blockItem :: C.BlockItem
      blockItem = C.BlockItemStmt $ C.StmtLabeled $ C.LabeledCase
        (identIsConstExpr tagIdent)
        caseBody
  case cases of
    All -> pure $ blockItem NE.:| []
    cases'@(And _ _) -> do
      items <- eval_elim_sum_cases ctt (n+1) rrep tagExpr variantExpr resultIdent cases'
      pure $ NE.cons blockItem items

declare_initialized_point :: String -> Point s t -> CodeGen s (Point s t)
declare_initialized_point prefix point = do
  ident <- declare_initialized prefix (pointExpr point) (pointCTypeInfo point)
  pure $ Point
    { pointExpr      = identIsCondExpr ident
    , pointTypeRep   = pointTypeRep point
    , pointCTypeInfo = pointCTypeInfo point
    }

-- | Make an initialized variable declaration for a stream. How this is done
-- depends upon the nature of the stream. Sometimes it is the same as for
-- points. For memory streams, it's essentially a no-op since these already have
-- static declarations.
--
-- For composite streams with nonzero prefix, a binder is made to the value
-- _now_. Taking a later offset will not give a new binder. You'd have to
-- bind to the dropped thing to get another binder.
declare_initialized_stream :: String -> Stream s t -> CodeGen s (Stream s t)
declare_initialized_stream prefix stream = case streamVal stream of

  -- Nothing needs to be done here; the static stream's representation is...
  -- static... it's already named.
  --
  -- NB: there is no way for the programmer to cache the index computation.
  -- However, since the indices are always statically known, we could precompute
  -- the literals... but why bother? Any decent C compiler will do constant
  -- folding anyway, right?
  StreamValStatic _ -> pure stream

  StreamValNonStatic (VCons cgen cs) -> do
    cexpr <- cgen
    !ident <- declare_initialized prefix cexpr (streamCTypeInfo stream)
    pure $ Stream
      { streamVal       = StreamValNonStatic (VCons (pure (identIsCondExpr ident)) cs)
      , streamTypeRep   = streamTypeRep stream
      , streamCTypeInfo = streamCTypeInfo stream
      }

-- | Make a declaration assigning the given value to a new identifier.
-- The declaration appears in the CodeGen state, and the resulting C identifier
-- may be used to refer to it.
declare_initialized
  :: String
  -> C.CondExpr
  -> CTypeInfo
  -> CodeGen s C.Ident
declare_initialized prefix cexpr tinfo = do
  ident <- freshBinder prefix
  -- Now we must make a block item which assigns the value `it` to the
  -- identifier `ident`.
  --
  --   <typeSpec> <ident> = <rexpr>;
  --   |________| |_____|   |_____|
  --   declnSpecs  decln     init
  --
  let declnSpecs :: C.DeclnSpecs
      declnSpecs = C.DeclnSpecsType (ctypeSpec tinfo) Nothing
      -- Pointer types in initialized bindings are const restrict.
      -- This is OK because indeed the pointers themselves will never change.
      -- However, we can't put const out front (on the thing behind the pointer),
      -- because the possibility of an uninitialized variable (for sum
      -- elimination) means that the struct members cannot be const, means that
      -- no bindings can be const, for we may want to use a binder in a struct
      -- thereby stripping the const and getting a warning.
      --
      -- It may be possible to infer from a completely generated program which
      -- things can be const, but is it worth the effort? Do const annotations
      -- help the compiler significantly?
      ptr :: Maybe C.Ptr
      ptr = if ctypePtr tinfo
            then Just (C.PtrBase (Just const_restrict))
            else Nothing
      declr :: C.Declr
      declr = C.Declr ptr (C.DirectDeclrIdent ident)
      cinit :: C.Init
      cinit = C.InitExpr (condExprIsAssignExpr cexpr);
      initDeclr :: C.InitDeclr
      initDeclr = C.InitDeclrInitr declr cinit
      initDeclrList :: C.InitDeclrList
      initDeclrList = C.InitDeclrBase initDeclr
      blockItem :: C.BlockItem
      blockItem = C.BlockItemDecln $ C.Decln declnSpecs (Just initDeclrList)
  addBlockItem blockItem
  pure ident

-- | Make a declaration without initializing it.
-- Unlike 'declare_initialized', this one will not be a const declaration.
declare_uninitialized
  :: String
  -> CTypeInfo
  -> CodeGen s C.Ident
declare_uninitialized prefix tinfo = do
  ctt <- compoundTypeTreatment
  ident <- freshBinder prefix
  let typeSpec = ctypeSpec tinfo
      -- If this is a pointer type, then we use a restrict, but not const,
      -- pointer.
      ptr = if ctypePtr tinfo
            then Just (C.PtrBase (Just (C.TypeQualBase C.QRestrict)))
            else Nothing
      declnSpecs = C.DeclnSpecsType typeSpec Nothing
      declr :: C.Declr
      declr = C.Declr ptr (C.DirectDeclrIdent ident)
      initDeclr :: C.InitDeclr
      initDeclr = C.InitDeclr declr
      initDeclrList :: C.InitDeclrList
      initDeclrList = C.InitDeclrBase initDeclr
      blockItem :: C.BlockItem
      blockItem = C.BlockItemDecln $ C.Decln declnSpecs (Just initDeclrList)
  addBlockItem blockItem
  pure ident

data IsCompound ty where
  IsNonEmptyProduct :: IsCompound ('Point.Product (t ': ts))
  IsNonEmptySum     :: IsCompound ('Point.Sum (t ': ts))

-- Need to know: given a type, should it be represented by a pointer _from a
-- compound type struct or union_?
-- Easy enough: it's only the non-empty sums and products. But, from an
-- organizational perspective: what should we call this function and ...

-- | Give true if values of this type would be affected by sharing.
-- These are just the compound ADTs which contain compound ADTs.
would_share :: Point.TypeRep ts -> Bool
would_share (Point.Product_t fs) = anyOfAll (isJust . is_compound) fs
would_share (Point.Sum_t fs)     = anyOfAll (isJust . is_compound) fs
would_share _              = False

-- | True if the type is a non-empty composite (sum or product).
--
-- TODO later we should identify singleton sums and products with the thing
-- that they contain, and change this to pick out products and sums of size at
-- least 2.
is_compound :: Point.TypeRep ts -> Maybe (IsCompound ts)
is_compound (Point.Product_t (And _ _)) = Just IsNonEmptyProduct
is_compound (Point.Sum_t (And _ _))     = Just IsNonEmptySum
is_compound _                           = Nothing



-- | Run a CodeGen term and generate a translation unit.
--
-- It contains a function eval which evaluates the expression behind the
-- `Val s t` and returns it. That C value will be completely standalone: no
-- pointers in it. The translation unit includes everything that is needed in
-- order to compute that value, nothing more.
--
--
-- TODO currently it only works for points. Must change it significantly for
-- streams I think.
genTransUnit
  :: CodeGenOptions
  -> (forall s . CodeGen s (Stream s ('Stream.Prefix n x)))
  -> Either CodeGenError C.TransUnit
genTransUnit opts expr = fst $ evalCodeGen opts $ do
  stream <- expr
  -- The result of the eval function must not contain any pointers.
  -- We always take it to the not-shared variant. For types which do not
  -- actually have any sharing, this will be the same type TODO
  --
  -- Always make a binding, convert using the name, so that we don't
  -- duplicate work.
  {-
  (_ident, val') <- declare_initialized "return_value" val
  toNotShared val'
  -}

  cexpr <- streamExprNow (streamVal stream)
  let tinfo = streamCTypeInfo stream
  -- NB: this declaration and assignment is _not_ optional. If we didn't do
  -- it, then we could get incorrect results, because the expression would
  -- be evaluated _after_ all of the static streams are updated. If the
  -- expression uses one of those, then it could become incorrect.
  ident <- declare_initialized "return_value" cexpr tinfo
  let returnexpr = identIsCondExpr ident
  st <- codeGenGet
  let evalFun = mainFun st stream returnexpr
  pure $ codeGenTransUnit st evalFun

  where

  -- This function computes the expression. It assumes the value is not
  -- shared form i.e. it doesn't contain any pointers to non-static data.
  mainFun :: CodeGenState -> Stream s t -> C.CondExpr -> C.FunDef
  mainFun cgs' stream expr =
    let declnSpecs :: C.DeclnSpecs
        declnSpecs = C.DeclnSpecsType (streamTypeSpec stream) Nothing
        ptr = if streamPtr stream
              then Just (C.PtrBase Nothing)
              else Nothing
        -- It's ok to use the type's pointer information here. If it's really
        -- a non-shared type then it'll not be a pointer (unless it's an empty
        -- type then it's void* and that's fine too).
        declr :: C.Declr
        declr = C.Declr ptr $ C.DirectDeclrFun2
          (C.DirectDeclrIdent ident_eval)
          Nothing
        args :: Maybe C.DeclnList
        args = Nothing
        exprBlockItem :: C.BlockItem
        exprBlockItem = C.BlockItemStmt $ C.StmtJump $ C.JumpReturn $ Just $
          condExprIsExpr expr
        allBlockItems :: [C.BlockItem]
        allBlockItems = staticMemoryStreamBlockItems (cgsStaticStreams cgs') ++ cgsBlockItems cgs'
        compoundStmt :: C.CompoundStmt
        compoundStmt = C.Compound $ Just $ case blockItemList allBlockItems of
          Nothing  -> C.BlockItemBase exprBlockItem
          Just bil -> C.BlockItemCons bil exprBlockItem
    in  C.FunDef declnSpecs declr args compoundStmt

{-
-- | Given some value, make it OK for static use.
--
-- This assumes that the type for the val given is already declared as shared.
-- Will declare the not shared variant.
--
-- This is always a no-op for non-compound types.
--
-- If compound type sharing is not enabled, this does nothing, because pointers
-- never appear in compound types.
--
-- If compound type sharing _is_ enabled, then this will ensure that both the
-- shared and non-shared version of the compound types are declared, along with
-- the function which converts from shared to non-shared (basically does a bunch
-- of copying). It will then give a Val which calls that function on the given
-- Val.
toNotShared :: Val s ('ValPoint t) -> CodeGen s (Val s ('ValPoint t))
toNotShared = convertTreatment Shared NotShared

-- | Opposite of 'toNotShared'.
--
-- TODO define. It's actually the same as toNotShared, just with the treatments
-- reversed:
--
--   intro_product Shared (make_selectors NotShared fields)
--   elim_sum NotShared (make_cases Shared variants)
toShared :: Val s ('ValPoint t) -> CodeGen s (Val s ('ValPoint t))
toShared = convertTreatment NotShared Shared

-- TODO write this Monday
-- | Given a val in some treatment, convert it to the other treatment
-- Assumes the type for the value is already declared in the given treatment.
convertTreatment
  :: forall s t .
     CompoundTypeTreatment
  -> CompoundTypeTreatment
  -> Val s ('ValPoint t)
  -> CodeGen s (Val s ('ValPoint t))
convertTreatment Shared    Shared    val = pure val
convertTreatment NotShared NotShared val = pure val
convertTreatment ctt       ctt'      val = case valType val of

  ValPoint_t (Product_t All) -> pure val
  ValPoint_t (Sum_t All)     -> pure val

  ValPoint_t (trep@(Product_t fields@(And _ _))) -> do

    -- If we have
    --   TypeRep field
    --   Any (Selector f) fields field
    -- then we can make
    --   Field f field
    -- and therefore
    --   All (Field f) fields
    let
        -- Eliminates the product using the given selector and then converts
        -- its treatment, giving a field which can be used to re-introduce the
        -- whole product.
        roundtrip
          :: forall field fields .
             Point.TypeRep ('Product fields)
          -> PointTarget s ('Product fields)
          -> Point.TypeRep field
          -> Any (Selector (PointTarget s)) fields field
          -> Field (PointTarget s) field
        roundtrip trepP exprP _ any = Field trepF $ PointTarget $ do
          val' <- withCompoundTypeTreatment ctt' $ runPointTarget $
            eval_elim_product trepP any exprP
          convertTreatment ctt ctt' val'

        selectors = forAll (\_ -> Selector) fields

        -- Use all of the fields, taken from the original product and converted,
        -- to re-introduce the product under the new treatment.
        introductions = zipAll (roundtrip trep (PointTarget (pure val))) fields selectors
    
    withCompoundTypeTreatment ctt' $ runPointTarget $
      eval_intro_product trep introductions

  ValPoint_t (trep@(Sum_t variants@(And _ _))) -> do

    let roundtrip
          :: forall variant variants .
             Point.TypeRep ('Sum variants)
          -> Point.TypeRep variant
          -> Any (Selector (PointTarget s)) variants variant
          -> Case (PointTarget s) ('Sum variants) variant
        roundtrip trepS _ variant = Case trepV $ \it -> PointTarget $ do
          val <- runPointTarget it
          val' <- convertTreatment ctt ctt' val
          withCompoundTypeTreatment ctt' $ runPointTarget $
            eval_intro_sum trepS variant (PointTarget (pure val'))

        selectors = forAll (\_ -> Selector) variants

        -- For each variant, a case which gives the sum re-introduced in the
        -- new treatment.
        cases = zipAll (roundtrip trep) variants selectors

    -- Problem here is that we need the thing being eliminated to be
    -- treated like it's in the original treatment, but the thing being
    -- _constructed_ to be in the new treatment.
    --
    -- Here at the sum elimination, we want the treatment to cause the
    -- uninitialized variable to use the new treatment, but the scrutinee (since
    -- it already has been created) to use the original.
    --
    -- Perhaps what we need is to give the treatment along with the TypeRep
    -- here as parameters, both for the sum and the result (trep, trep).;
    withCompoundTypeTreatment ctt' $ runPointTarget $
      eval_elim_sum trep trep cases (PointTarget (pure val))

  _ -> pure val
-}
