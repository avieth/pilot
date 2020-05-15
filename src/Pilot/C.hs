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

import Control.Monad (unless, void)
import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity

import qualified Data.Kind as Haskell (Type)
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, symbolVal)
import Numeric.Natural (Natural)

import qualified Language.C99.AST as C
import Language.C99.Pretty (Pretty, pretty)
import Text.PrettyPrint (render)

import Pilot.EDSL.Point hiding (Either, Maybe)
import qualified Pilot.EDSL.Point as Point

import System.IO (writeFile)
import System.IO.Error (userError)
import Control.Exception (throwIO)

-- TODO NEXT STEPS
--
-- - Streams.
--   - "pure" streams (made from pointwise functions through the stream functor/
--     applicative/monad interfaces) compile to points.
--   - "memory" streams: generate a new name for the stream, and a static
--
--       struct <ty_name> {
--         <type> values[<size>];
--         <size_type> index;
--       };
--       struct <ty_name> <stream_name>;
--
--     where <size> is statically known (from the Nat type parameter), <type>
--     as well, and <size_type> is chosen so that it fits <size> and is
--     unsigned. A stream is represented by something which is a pointer to
--     this static struct. We can run the continuation with &<stream_name> to
--     come up with the expression which computes the next value in the stream,
--     and use that to implement an update function or macro
--
--       void <stream_name>_update(<type> value) {
--         <stream_name>.index += 1;
--         <stream_name>.index %= <size>;
--         <stream_name>.values[<stream_name>.index] = value;
--       }
--
--     Care must be taken to ensure that stack-allocated compound types are
--     taken by value, but static stream types (which can also be held in
--     streams) are taken by reference.
--
--     Then, at the end of the step function, for each stream we compute the
--     expression of the next element and then copy it in, in blocks
--
--       stream_1_val = <stream_1_expr>;
--       stream_2_val = <stream_2_expr>;
--       stream_1_update(stream_1_val);
--       stream_2_update(stream_2_val);
--
--     this way, if stream 1 uses stream 2 or vice versa, we still get the
--     expected result (no destructive updates mid-computation). All writes
--     happen at the end, after all reads.
--
--     TODO IMPORTANT since pure streams can have any type index, we'll need
--     to know from the Val type whether it's a pure stream or not, so that
--     we can correctly implement drop: if it's pure, then drop x = x.
--
--   - "impure" streams are simply extern declarations with a type annotation.
--     Actually, 2 types here: the extern type (any syntactically valid C), and
--     the EDSL type. The programmer must then say how to convert from the
--     extern to the intern. This will be done at the start of each step, to
--     copy the extern to a local static variable of the intern type.
--     This is of course C CodeGen-specific, unlike memory streams.
--
-- PROBLEM: how to represent streams of streams. Case study: a memory stream
-- which has streams as its elements. Some of these may be other memory streams,
-- some may be external streams, some may be pure streams. For pure streams,
-- we can just evaluate them and put in the value. For externals, we have to
-- just keep a pointer (is ok because they are extern). For memory streams,
-- pointer as well, to the struct holding index and array (is ok because these
-- are static). So conceptually it is
--
--   StreamRep t = Value t | Extern (Ptr t) | Memory (Ptr (MemoryStruct t))
--
--   union stream_variant_t {
--     t value;
--     // const restrict OK here since we copy all foreign things over at the
--     // start of each step. Even if we didn't do that, this would be read
--     // only anyway... although, no not really, since the harness program
--     // certainly will write to it.
--     t *const restrict foreign;
--     // Problem here is that each memory stream gets its own _type_. We have
--     // to use a function pointer instead.
--     // No sense in the struct then is there? Just create for each memory
--     // stream a function which gets its value, and a function which writes
--     // its value. 
--     // Ah but no, this can't work. Getting the _latest_ value may involve
--     // scope.
--     t (*memory)(void);
--   };
--
--   NB: a memory stream which has all of its memory dropped is the same as a
--   pure stream. For that we can just drop it in as we would for any other
--   pure stream. For memory streams which have not been dropped to 0 we should
--   take a pointer to an array index pair... so if we want this to wor
--
--   Oh but there is a much bigger problem here. Imagine we take a composition
--   over a memory stream and try to use that as an initial value?
--
--     stateful1 = ...
--     composite = (+) <$> stateful1 <*> pure 1
--     stateful2 = hold (VCons composite VNil) $ \_ -> pure 42
--
--   could it be just that the initial values must not use any bindings?
--   Yeah, we need that anyway. That means that they can be made into functions
--   and we can just store function pointers?
--
--   Yeah this is a problem, since streams are a lot like functions in that
--   they have a closure.
--   All of this would go away if we could eliminate streams of streams, i.e.
--   make Stream a special "add on" type.
--
--   Yeah, that was the original idea anyway. 
--
--
--
--
--
-- - C backend specific externs:
--   - values of any EDSL type
--   - Also, functions? Yeah, that's probably the way forward. This can express
--     effectful things like triggers, but also pure things like introducing a
--     mathematical function that you'd like to implement later, directly in C.
--   - NB: in the pointwise EDSL, these must be constants.
--   By using one of these, you constrain the f and val types on the expression.
--   So, the programmer expresses as much as possible without specifying f or
--   val, then when the backend is decided upon, these externs are dropped in.
--   It should be very nice.
--
-- - Use of NULL for void and unit.
--   Given that unit cannot be eliminated, and void cannot be introduced, we're
--   sure that the use of NULL in the generated code is safe (it will never be
--   dereferenced). However, wouldn't it be better if we didn't generate any
--   code at all for these cases? Should look into that.
--
-- - Aggressive simplification of products and sums? It may be worthwhile to
--   simplify all products and sums using the 1 and 0 identity laws. That's to
--   say, a product contains no 1s, and a sum contains no 0s.
--   It would give smaller (and probably faster) C.
--

-- | Useful for debugging.
prettyPrint :: Pretty a => a -> String
prettyPrint = render . pretty

-- |
-- = Type names and type declarations
--
-- Integral types are represented using standard C99 types such as uint8_t and
-- int64_t.
--
-- Compound types, in general, are represented using structs, unions, and enums
-- in the following way:
--
-- - An empty sum or empty product has type void * and their value
--   representation is NULL. Since the empty sum cannot be introduced, and
--   the empty product cannot be eliminated, this NULL will never actually be
--   used.
--
-- - A non-empty product is a struct with a field for each conjunct.
--
-- - A non-sum is a struct with fields tag and variant. The tag is an enum with
--   one constructor for each disjunct, and the variant is a union with one
--   constructor for each disjunct.
--
-- - If a sum or product contains another compound type, it appears directly,
--   not behind a pointer.
--
-- - Introducing a sum or product means initializing the entire compound
--   structure.
--
-- - Eliminating a product is a direct field access (.)
--
-- - Eliminating a sum is a switch/case construction, because each branch needs
--   its own scope. Each of the branches will assign once to an uninitialized
--   result variable. Each branch is given the corresponding union accessor
--   for the variant.
--
-- However, this representation is not chosen for every sum. We would like for
-- the sum 1 + 1 to be represented by a byte with 0 for one of the disjuncts and
-- 1 for the other. By choosing this representation we can use it as the boolean
-- type without any runtime cost.
--
-- More generally, for any sum of the form a_1 + ... + a_n, where each a_i is
-- either 1 or 0 (unit or void), this sum is represented by an enum with its
-- values specified increasing from 0 to n.
--
-- To introducing such a sum, just give the enum constructor. To eliminate, do
-- the usual switch/case construction but instead of giving the union variant
-- accessor, give the representation of 0 or 1 (i.e. NULL).
--
-- Moving forward, we may want to offer a potential optimization: compound
-- types could be shared by way of const restrict pointers within the evaluation
-- function block (i.e. whenever we know they do not need to hang around after
-- this function returns).


-- | Identifies sum types of the form a_1 + ... + a_n where each a_i is either
-- 1 or 0 (unit or void).
--
-- If the result is `Just 0`, then this is the empty sum (void) and we represent
-- it as (void *) NULL.
--
-- If the result is `Just n, n > 0` then this is a simple enum and we represent
-- it as a C `enum { tag_(n-1) = (n-1), ..., tag_0 = 0 }`.
--
-- Otherwise, we use the general sum representation as a struct with an enum tag
-- and a union variant.
sum_is_enum :: TypeRep ('Sum types) -> Maybe Natural
sum_is_enum (Sum_t All)          = Just 0
sum_is_enum (Sum_t (And ty tys)) = case ty of
  -- This is 1 (unit)
  Product_t All -> ((+) 1) <$> sum_is_enum (Sum_t tys)
  -- This is 0 (void)
  Sum_t All     -> ((+) 1) <$> sum_is_enum (Sum_t tys)
  _             -> Nothing

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

-- | The C type specifier, and whether it should be taken through a pointer.
data CTypeInfo = CTypeInfo
  { ctypeSpec :: !C.TypeSpec
  , ctypePtr  :: !(Maybe C.Ptr)
  }

-- | Get the C type information for a given TypeRep. This includes not only
-- the type specifier but also info about whether it should be taken as a
-- pointer, which is often an important thing to know... Weird that in,
-- "pointer" is not a type specifier, as we might expect from experience in
-- functional languages.
type_info :: TypeRep t -> CodeGen s CTypeInfo
type_info trep = do
  typeSpec <- type_spec trep
  pure $ CTypeInfo { ctypeSpec = typeSpec, ctypePtr = type_ptr trep }

-- | Use the type rep to fill in the specs and pointer properties of the
-- val record.
type_rep_val :: TypeRep ty -> C.CondExpr -> CodeGen s (Val s ty)
type_rep_val tr cexpr = do
  typeSpec <- type_spec tr
  pure $ Val
    { getVal = cexpr
    , valSpecs = typeSpec
    , valPtr = type_ptr tr
    }

-- | C pointer information for a given type. If its representation is to be
-- taken always behind a pointer, then this will be Just.
--
-- At the moment, only empty products and sums are represented using pointers
-- (they are void *).
type_ptr :: TypeRep ty -> Maybe C.Ptr
type_ptr (Sum_t All)     = Just $ C.PtrBase $ Just const_restrict
type_ptr (Product_t All) = Just $ C.PtrBase $ Just const_restrict
type_ptr _               = Nothing

const_restrict :: C.TypeQualList
const_restrict = C.TypeQualCons
  (C.TypeQualBase C.QConst)
  C.QRestrict

-- | The C type specifier. This doesn't include pointer information.
type_spec :: TypeRep ty -> CodeGen s C.TypeSpec

-- Integer types use the standard sized variants like uint8_t. These are
-- typedefs.
type_spec (Integer_t sr wr) =
  pure $ C.TTypedef $ C.TypedefName (integer_ident sr wr)

-- TODO develop support for rational numbers.
type_spec Rational_t = codeGenError $
  CodeGenInternalError "fractional numbers not supported at the moment"

type_spec p@(Product_t _) = product_type_spec p

type_spec s@(Sum_t _)     = sum_type_spec s

-- TODO
-- refactoring of the product_type_spec and sum_type_spec motifs. All we need to
-- do here is put the fields of the type rep into the map, along with the
-- identifier. We only generate the actual declarations at generation time; the
-- identifiers are all we need prior to that.


-- | Stateful CodeGen term to declare a product. If it has already been
-- declared (something with the same 'Haskell.TypeRep' was declared) then
-- nothing happens.
--
-- Otherwise, we generate a new identifier, and include its struct declaration
-- in the CodeGen declarations list.
product_type_spec :: TypeRep ('Product tys) -> CodeGen s C.TypeSpec
product_type_spec (Product_t All) = pure $ C.TVoid
product_type_spec trep@(Product_t fields@(And t ts)) = do
  st <- CodeGen $ Trans.lift get
  let someTypeRep :: SomeTypeRep
      someTypeRep = SomeTypeRep trep
  case Map.lookup someTypeRep (cgsProducts st) of
    -- TODO should store the TypeRep the map and do a sanity check that that
    -- it is equal to what we expect?
    Just pdeclr -> pure $ pdTypeSpec pdeclr
    Nothing -> do
      declnList <- field_declns "field_" 0 (NonEmptyFields fields)
      -- NB: map may have changed as a result of fields_declare, in case there
      -- are composite types in there which have not yet been seen.
      st <- CodeGen $ Trans.lift get

      -- Create the product's declaration.
      let !ident = assertValidIdentifier
            ("product_type_spec bad identifier for " ++ show someTypeRep)
            (stringIdentifier ("product_" ++ show (Map.size (cgsProducts st))))

      let typeSpecs = product_decln_type_spec ident declnList
          decln = C.Decln (C.DeclnSpecsType (ctDef typeSpecs) Nothing) Nothing

      let !pdeclr = ProductDeclr { pdTypeSpec = ctDec typeSpecs }
          !prodMap' = Map.insert someTypeRep pdeclr (cgsProducts st)
          !declns' = decln : cgsDeclns st
          !st' = st { cgsDeclns = declns', cgsProducts = prodMap' }
      CodeGen $ Trans.lift $ put st'
      pure $ ctDec typeSpecs

-- | The type spec for the definition of a product, given a name and its fields.
product_decln_type_spec :: C.Ident -> C.StructDeclnList -> CompTypeSpec
product_decln_type_spec ident declnList = CompTypeSpec
  { ctDef = definition
  , ctDec = declaration
  }
  where
  definition  = C.TStructOrUnion $ C.StructOrUnionDecln C.Struct (Just ident) declnList
  declaration = C.TStructOrUnion $ C.StructOrUnionForwDecln C.Struct ident

-- | Exactly like 'product_type_spec' but on a different part of the CodeGen
-- state.
sum_type_spec :: TypeRep ('Sum tys) -> CodeGen s C.TypeSpec
sum_type_spec (Sum_t All) = pure $ C.TVoid
sum_type_spec trep@(Sum_t variants@(And t ts)) = do
  st <- CodeGen $ Trans.lift get
  let someTypeRep :: SomeTypeRep
      someTypeRep = SomeTypeRep trep
  case Map.lookup someTypeRep (cgsSums st) of
    Just sdeclr -> pure $ sdTypeSpec sdeclr
    Nothing -> do
      declnList <- field_declns "variant_" 0 (NonEmptyFields variants)
      st <- CodeGen $ Trans.lift get

      let !ident = assertValidIdentifier
            ("sum_type_spec bad identifier for " ++ show someTypeRep)
            (stringIdentifier ("sum_" ++ show (Map.size (cgsSums st))))
          !tagIdent = assertValidIdentifier
            ("sum_type_spec bad enum identifier for " ++ show someTypeRep)
            (stringIdentifier ("sum_tag_" ++ show (Map.size (cgsSums st))))
          !variantIdent = assertValidIdentifier
            ("sum_type_spec bad union identifier for " ++ show someTypeRep)
            (stringIdentifier ("sum_variant_" ++ show (Map.size (cgsSums st))))

      let tagSpecs = sum_tag_decln_type_spec tagIdent (NonEmptyFields variants)
          variantSpecs = sum_variant_decln_type_spec variantIdent declnList
          typeSpecs = sum_decln_type_spec ident (ctDec tagSpecs) (ctDec variantSpecs) declnList
          tagDecln = C.Decln (C.DeclnSpecsType (ctDef tagSpecs) Nothing) Nothing
          variantDecln = C.Decln (C.DeclnSpecsType (ctDef variantSpecs) Nothing) Nothing
          decln = C.Decln (C.DeclnSpecsType (ctDef typeSpecs) Nothing) Nothing

      let !sdeclr = SumDeclr { sdTypeSpec = ctDec typeSpecs }
          !sumMap' = Map.insert someTypeRep sdeclr (cgsSums st)
          !declns' = decln : variantDecln : tagDecln : cgsDeclns st
          !st' = st { cgsDeclns = declns', cgsSums = sumMap' }
      CodeGen $ Trans.lift $ put st'
      pure $ ctDec typeSpecs

-- | For composite types (structs, unions, enums) we have their definitions
-- as well as their declarations.
data CompTypeSpec = CompTypeSpec
  { ctDef :: C.TypeSpec
  , ctDec :: C.TypeSpec
  }

-- | The type spec for the definition of a sum, given a name, and the type
-- specs for its tag and variant fields.
--
-- Also gives the forward declaration for reference in other types.
--
--   struct <ident> {
--     <tag_spec> tag;
--     <variant_spec> variant;
--   };
sum_decln_type_spec
  :: C.Ident
  -> C.TypeSpec -- ^ Type for the tag.
  -> C.TypeSpec -- ^ Type for the variant.
  -> C.StructDeclnList
  -> CompTypeSpec
sum_decln_type_spec ident tagSpec variantSpec decln = CompTypeSpec
  { ctDef = definition
  , ctDec = declaration
  }
  where
  definition = C.TStructOrUnion $ C.StructOrUnionDecln C.Struct (Just ident)
    (sum_struct_decln_list tagSpec variantSpec)
  declaration = C.TStructOrUnion $ C.StructOrUnionForwDecln C.Struct ident

-- | A struct is represented by
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
    (C.SpecQualQual C.QConst $ Just (C.SpecQualType tagSpec Nothing))
    (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_tag))))
  )
  (C.StructDecln
    (C.SpecQualQual C.QConst $ Just (C.SpecQualType variantSpec Nothing))
    (C.StructDeclrBase (C.StructDeclr (C.Declr Nothing (C.DirectDeclrIdent ident_variant))))
  )

-- | The type spec for the declaration of a tag for a sum. It's an enum with
-- one variant for each field.
sum_tag_decln_type_spec :: C.Ident -> NonEmptyFields -> CompTypeSpec
sum_tag_decln_type_spec ident neFields = CompTypeSpec
  { ctDef = definition
  , ctDec = declaration
  }
  where
  definition  = C.TEnum $ C.EnumSpec (Just ident) $ sum_enum_tag_declns 0 neFields
  declaration = C.TEnum $ C.EnumSpecForw ident

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
sum_variant_decln_type_spec :: C.Ident -> C.StructDeclnList -> CompTypeSpec
sum_variant_decln_type_spec ident declnList = CompTypeSpec
  { ctDef = definition
  , ctDec = declaration
  }
  where
  definition  = C.TStructOrUnion $ C.StructOrUnionDecln C.Union (Just ident) declnList
  declaration = C.TStructOrUnion $ C.StructOrUnionForwDecln C.Union ident

-- | The struct/union declaration list for product and sum types. For products,
-- this will give the struct fields; for sums, the union variants.
--
-- They will all be qualified with const.
--
-- This will put the fields in reverse order, since the C declaration list
-- type is defines like a snoc-list. Doesn't really matter though.
--
-- TODO consider factoring this: given NonEmptyFields, get CTypeInfo for each,
-- in the CodeGen monad, then another function which takes a NonEmpty CTypeInfo
-- and String and Natural and generates the StructDeclnList.
field_declns
  :: String  -- ^ Prefix for the fields/variants
  -> Natural -- ^ Initial disambiguator. Call this will 0.
  -> NonEmptyFields
  -> CodeGen s C.StructDeclnList

field_declns name n (NonEmptyFields (And t All)) = do
  info <- type_info t
  let !ident = assertValidIdentifier 
        ("field_declns bad identifier")
        (stringIdentifier (name ++ show n))
      -- We use the type spec, qualified by const: struct fields and union
      -- variants are set on initialization and are never changed.
      qualList :: C.SpecQualList
      qualList = C.SpecQualQual C.QConst $ Just $ C.SpecQualType (ctypeSpec info) $ Nothing
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr (ctypePtr info) $
        C.DirectDeclrIdent ident
  pure $ C.StructDeclnBase $ C.StructDecln qualList declrList

field_declns name n (NonEmptyFields (And t (And t' ts))) = do
  subList <- field_declns name (n+1) (NonEmptyFields (And t' ts))
  info <- type_info t
  let !ident = assertValidIdentifier
        ("field_declns bad identifier")
        (stringIdentifier (name ++ show n))
      qualList :: C.SpecQualList
      qualList = C.SpecQualQual C.QConst $ Just $ C.SpecQualType (ctypeSpec info) $ Nothing
      declrList :: C.StructDeclrList
      declrList = C.StructDeclrBase $ C.StructDeclr $ C.Declr (ctypePtr info) $
        C.DirectDeclrIdent ident
  pure $ C.StructDeclnCons subList $ C.StructDecln qualList declrList

-- |
-- = Evaluation of expressions

run_example
  :: Expr ExprF CodeGen Val s t
  -> (Prelude.Either CodeGenError (Val s t), CodeGenState)
run_example x = evalCodeGen (evalInMonad x eval_expr)

write_example :: String -> Expr ExprF CodeGen Val s t -> IO ()
write_example fp expr = codeGenToFile fp (evalInMonad expr eval_expr)

example_1 :: Expr ExprF f val s (Pair UInt8 Int8)
example_1 = pair uint8_t int8_t (uint8 42) (int8 (-42))

example_2 :: Expr ExprF f val s (Point.Either UInt8 Int8)
example_2 = right uint8_t int8_t (int8 (-42))

example_3 :: Expr ExprF f val s (Point.Maybe Int8)
example_3 = just int8_t (int8 (-42))

example_4 :: Expr ExprF f val s Int8
example_4 = elim_maybe int8_t int8_t example_3
  (\_ -> int8 (-1))
  (\t -> t)

example_4_1 :: Expr ExprF f val s Int8
example_4_1 = elim_either uint8_t int8_t int8_t example_2
  (\_ -> int8 (-1))
  (\_ -> int8 2)

example_5 :: Expr ExprF f val s UInt8
example_5 = Point.fst uint8_t int8_t example_1

example_6 :: Expr ExprF f val s UInt8
example_6 = add uint8_t (uint8 2) (uint8 2)

example_7 :: Expr ExprF f val s UInt8
example_7 = add uint8_t example_6 example_5

example_8 :: Expr ExprF f val s UInt8
example_8 = local (pair_t uint8_t int8_t) uint8_t example_1 $ \p -> do
  add uint8_t (Point.fst uint8_t int8_t p) example_6

example_9 :: Expr ExprF f val s UInt8
example_9 =
  let a = uint8 0
      b = uint8 1
      c = uint8 3
      d = add uint8_t a b
      e = add uint8_t d c
      f = shiftR uint8_t e a
  in  notB uint8_t f

example_10 :: Expr ExprF f val s UInt8
example_10 = local uint8_t uint8_t example_9 $ \a ->
  orB uint8_t a (uint8 42)

example_11 :: Expr ExprF f val s Point.Ordering
example_11 =
  local uint8_t ordering_t example_10 $ \s ->
    local uint8_t ordering_t example_6 $ \t ->
      cmp uint8_t s t

-- | Contains a nested product in a sum.
example_12 :: Expr ExprF f val s UInt8
example_12 =
  -- Bind the pair from example_1
  local (pair_t uint8_t int8_t) uint8_t example_1 $ \p ->
    -- Bind a maybe of this
    --local (maybe_t (typeOf p)) uint8_t (nothing (typeOf p)) $ \s ->
    local (maybe_t (typeOf p)) uint8_t (just (typeOf p) p) $ \s ->
      elim_maybe (typeOf p) uint8_t s
        (\_ -> uint8 1)
        (\x -> Point.fst uint8_t int8_t x)

-- | Generate a C value representation for an expression, assuming any/all of
-- its sub-expressions are already generated.
--
-- For many `ExprF`s, this will be a simple C expression. For some, C statements
-- and declarations are required (forming a compound statement). In all cases,
-- a C expression is ultimately given, but the state carried in the `CodeGen`
-- monad will contain the information necessary to construct the compound
-- statement which gives meaning to that expression.
--
-- A `Local` binding, for instance, needs a C declaration in the same scope.
-- The most complicated aspect is `ElimSum`, which must elaborate to an if/else
-- or switch construct, because the cases eliminators may reuqire scope of their
-- own (and so a conditional _expression_ cannot be used). Ultimately, the
-- `ElimSum` yields a C identifier which is updated at the end of every case
-- branch.
--
-- The `s` type parameter serves to represent the fact that the Val, which must
-- be a C expression, makes sense only in context.
eval_expr :: ExprF CodeGen Val s t -> CodeGen s (Val s t)
eval_expr (IntroInteger tr il)        = eval_intro_integer tr il
eval_expr (PrimOp primop)             = eval_primop primop
eval_expr (IntroProduct tr fields)    = eval_intro_product tr fields
eval_expr (IntroSum tr variant)       = eval_intro_sum tr variant
eval_expr (ElimProduct tr _rr sel it) = eval_elim_product tr sel it
eval_expr (ElimSum tr rr cases it)    = eval_elim_sum tr rr cases it
eval_expr (Local tt tr it k)          = eval_local tt tr it k

eval_expr' :: Expr ExprF CodeGen Val s x -> CodeGen s (Val s x)
eval_expr' expr = evalInMonad expr eval_expr

eval_primop :: PrimOpF CodeGen Val s t -> CodeGen s (Val s t)
eval_primop (Arithmetic arithop) = eval_arithop arithop
eval_primop (Bitwise bitop)      = eval_bitop bitop
eval_primop (Relative relop)     = eval_relop relop

eval_arithop :: ArithmeticOpF CodeGen Val s t -> CodeGen s (Val s t)
eval_arithop (AddInteger tr x y) = eval_add_integer tr x y
eval_arithop (SubInteger tr x y) = eval_sub_integer tr x y
eval_arithop (MulInteger tr x y) = eval_mul_integer tr x y
eval_arithop (DivInteger tr x y) = eval_div_integer tr x y
eval_arithop (ModInteger tr x y) = eval_mod_integer tr x y
eval_arithop (NegInteger tr x)   = eval_neg_integer tr x

eval_bitop :: BitwiseOpF CodeGen Val s t -> CodeGen s (Val s t)
eval_bitop (AndB tr x y)   = eval_and_bitwise tr x y
eval_bitop (OrB  tr x y)   = eval_or_bitwise  tr x y
eval_bitop (XOrB tr x y)   = eval_xor_bitwise tr x y
eval_bitop (NotB tr x)     = eval_not_bitwise tr x
eval_bitop (ShiftL tr x y) = eval_shiftl_bitwise tr x y
eval_bitop (ShiftR tr x y) = eval_shiftr_bitwise tr x y

eval_relop :: RelativeOpF CodeGen Val s t -> CodeGen s (Val s t)
eval_relop (Cmp tr x y) = eval_cmp tr x y

-- | Take a fresh name, bind the expression to it, and use the _name_ rather
-- than the expression to elaborate the code here in the meta-language.
--
-- NB: this has implications for the evaluation of sum type elimination. It
-- cannot be done by way of an expression, because each branch requires its own
-- scope, so we're forced to use if/else blocks or switch statements with block
-- scopes.
--
-- TODO an improvement for later: if the value being bound is just an identifier,
-- then we don't need a new binding. Can be done easily if we change the Val
-- representation to be a sum.
eval_local
  :: forall t r s .
     TypeRep t
  -> TypeRep r
  -> Expr ExprF CodeGen Val s t
  -> (Expr ExprF CodeGen Val s t -> Expr ExprF CodeGen Val s r)
  -> CodeGen s (Val s r)
eval_local _tt _tr x k = do
  val <- eval_expr' x
  (_ident, val') <- declare_initialized "local" val
  eval_expr' (k (value val'))

eval_intro_integer
  :: forall signedness width s .
     TypeRep ('Integer signedness width)
  -> IntegerLiteral signedness width
  -> CodeGen s (Val s ('Integer signedness width))

eval_intro_integer tr@(Integer_t Unsigned_t _width) il = type_rep_val tr expr
  where
  expr = constIsCondExpr $ C.ConstInt $ C.IntHex (hex_const (absolute_value il)) Nothing

eval_intro_integer tr@(Integer_t Signed_t _width) il = type_rep_val tr $
  if is_negative il
  then unaryExprIsCondExpr $ C.UnaryOp C.UOMin $ constIsCastExpr $ C.ConstInt $
        C.IntHex (hex_const (absolute_value il)) Nothing
  else constIsCondExpr $ C.ConstInt $ C.IntHex (hex_const (absolute_value il)) Nothing

is_negative :: IntegerLiteral 'Signed width -> Bool
is_negative (Int8 i8)   = i8 < 0
is_negative (Int16 i16) = i16 < 0
is_negative (Int32 i32) = i32 < 0
is_negative (Int64 i64) = i64 < 0

absolute_value :: IntegerLiteral signedness width -> Natural
absolute_value (UInt8 w8)   = fromIntegral w8
absolute_value (UInt16 w16) = fromIntegral w16
absolute_value (UInt32 w32) = fromIntegral w32
absolute_value (UInt64 w64) = fromIntegral w64
absolute_value (Int8 i8)    = fromIntegral (abs i8)
absolute_value (Int16 i16)  = fromIntegral (abs i16)
absolute_value (Int32 i32)  = fromIntegral (abs i32)
absolute_value (Int64 i64)  = fromIntegral (abs i64)

-- | The `signedness` and `width` meta-language types ensure that the two
-- integers are of the same type.
eval_add_integer
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_add_integer tr vx vy = do
  x <- eval_expr' vx
  y <- eval_expr' vy
  let expr = addExprIsCondExpr $ C.AddPlus
        (condExprIsAddExpr (getVal x))
        (condExprIsMultExpr (getVal y))
  type_rep_val tr expr

eval_sub_integer
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_sub_integer tr vx vy = do
  x <- eval_expr' vx
  y <- eval_expr' vy
  let expr = addExprIsCondExpr $ C.AddMin
        (condExprIsAddExpr (getVal x))
        (condExprIsMultExpr (getVal y))
  type_rep_val tr expr

eval_mul_integer
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_mul_integer tr vx vy = do
  x <- eval_expr' vx
  y <- eval_expr' vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultMult
        (condExprIsMultExpr (getVal x))
        (condExprIsCastExpr (getVal y))
  type_rep_val tr expr

eval_div_integer
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_div_integer tr vx vy = do
  x <- eval_expr' vx
  y <- eval_expr' vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultDiv
        (condExprIsMultExpr (getVal x))
        (condExprIsCastExpr (getVal y))
  type_rep_val tr expr

eval_mod_integer
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_mod_integer tr vx vy = do
  x <- eval_expr' vx
  y <- eval_expr' vy
  let expr = addExprIsCondExpr $ C.AddMult $ C.MultMod
        (condExprIsMultExpr (getVal x))
        (condExprIsCastExpr (getVal y))
  type_rep_val tr expr

eval_neg_integer
  :: TypeRep ('Integer 'Signed width)
  -> Expr ExprF CodeGen Val s ('Integer 'Signed width)
  -> CodeGen s (Val s ('Integer 'Signed width))
eval_neg_integer tr vx = do
  x <- eval_expr' vx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOMin $
        condExprIsCastExpr (getVal x)
  type_rep_val tr expr

eval_and_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_and_bitwise tr bx by = do
  x <- eval_expr' bx
  y <- eval_expr' by
  let expr = andExprIsCondExpr $ C.And
        (condExprIsAndExpr (getVal x))
        (condExprIsEqExpr  (getVal y))
  type_rep_val tr expr

eval_or_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_or_bitwise tr bx by = do
  x <- eval_expr' bx
  y <- eval_expr' by
  let expr = orExprIsCondExpr $ C.Or
        (condExprIsOrExpr  (getVal x))
        (condExprIsXOrExpr (getVal y))
  type_rep_val tr expr

eval_xor_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_xor_bitwise tr bx by = do
  x <- eval_expr' bx
  y <- eval_expr' by
  let expr = xorExprIsCondExpr $ C.XOr
        (condExprIsXOrExpr (getVal x))
        (condExprIsAndExpr (getVal y))
  type_rep_val tr expr

eval_not_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s ('Integer signedness width))
eval_not_bitwise tr bx = do
  x <- eval_expr' bx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOBNot
        (condExprIsCastExpr (getVal x))
  type_rep_val tr expr

eval_shiftl_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer 'Unsigned 'Eight)
  -> CodeGen s (Val s ('Integer signedness width))
eval_shiftl_bitwise tr bx by = do
  x <- eval_expr' bx
  y <- eval_expr' by
  let expr = shiftExprIsCondExpr $ C.ShiftLeft
        (condExprIsShiftExpr (getVal x))
        (condExprIsAddExpr   (getVal y))
  type_rep_val tr expr

eval_shiftr_bitwise
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer 'Unsigned 'Eight)
  -> CodeGen s (Val s ('Integer signedness width))
eval_shiftr_bitwise tr bx by = do
  x <- eval_expr' bx
  y <- eval_expr' by
  let expr = shiftExprIsCondExpr $ C.ShiftRight
        (condExprIsShiftExpr (getVal x))
        (condExprIsAddExpr   (getVal y))
  type_rep_val tr expr

-- | The comparison is expressed using 2 C ternary expressions.
-- Relies on the assumption of a total order (that if x is neither than than nor
-- greater than y then x is equal to y). Would not work for float/double, for
-- example.
eval_cmp
  :: TypeRep ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> Expr ExprF CodeGen Val s ('Integer signedness width)
  -> CodeGen s (Val s Point.Ordering)
eval_cmp _tr vx vy = do
  -- We elaborate all 3 cases here.
  -- The ternary operator which we generate ensures that only one of them is
  -- actually evaluated in the object-language
  lessThan    <- eval_expr' lt
  greaterThan <- eval_expr' gt
  equalTo     <- eval_expr' eq
  x <- eval_expr' vx
  y <- eval_expr' vy
  let isLt :: C.RelExpr
      isLt = C.RelLT (condExprIsRelExpr (getVal x)) (condExprIsShiftExpr (getVal y))
      isGt :: C.RelExpr
      isGt = C.RelGT (condExprIsRelExpr (getVal x)) (condExprIsShiftExpr (getVal y))
      expr = C.Cond (relExprIsLOrExpr isLt) (condExprIsExpr (getVal lessThan)) $
             C.Cond (relExprIsLOrExpr isGt) (condExprIsExpr (getVal greaterThan)) $
                                            (getVal equalTo)
  type_rep_val ordering_t expr

-- | Product intro: give all conjuncts and get the product. Since products are
-- structs, this corresponds to a struct initializer with a field for each
-- conjunct.
--
-- Special case for the empty product introduction, which is simply NULL.
-- TODO there is no way to eliminate an empty product, so we could probably
-- get away with simply erasing an intro of an empty product.
eval_intro_product
  :: TypeRep ('Product types)
  -> Fields CodeGen Val s types
  -> CodeGen s (Val s ('Product types))
eval_intro_product trep AllF = type_rep_val trep cNULL
eval_intro_product trep (AndF t ts) = do
  -- This will ensure the composite type is in the code gen state
  typeSpec <- product_type_spec trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
  initList <- product_field_inits 0 t ts
  let pexpr = C.PostfixInits typeName initList
  type_rep_val trep (postfixExprIsCondExpr pexpr)

-- | Product elimination: an indirect field accessor (->).
--
-- NB: this cannot be an empty product, the 'Selector' GADT does not allow it.
eval_elim_product
  :: TypeRep ('Product types)
  -> Selector CodeGen Val s types r
  -> Expr ExprF CodeGen Val s ('Product types)
  -> CodeGen s (Val s r)
eval_elim_product trep selector cgt = do
  typeSpec <- product_type_spec trep
  cgtVal <- eval_expr' cgt
  let pexpr = condExprIsPostfixExpr (getVal cgtVal)
  eval_elim_product_with_selector 0 pexpr selector

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
  -> Selector CodeGen Val s types r
  -> CodeGen s (Val s r)
eval_elim_product_with_selector n pexpr (OrC sel) =
  eval_elim_product_with_selector (n+1) pexpr sel
eval_elim_product_with_selector n pexpr (AnyC trep k) = do
  fieldIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_product_with_selector bad field " ++ show n)
    (pure (stringIdentifier ("field_" ++ show n)))
  let expr = postfixExprIsCondExpr $ C.PostfixDot pexpr fieldIdent
  val <- type_rep_val trep expr
  eval_expr' (k (value val))

-- |
--
-- Like for empty products, empty sums are also void* so that we can just use
-- NULL and not allocate anything.
--
eval_intro_sum
  :: TypeRep ('Sum types)
  -> Variant CodeGen Val s types
  -> CodeGen s (Val s ('Sum types))
-- The meta-language doesn't allow for empty sums to be introduced (void type
-- in the algebraic sense).
eval_intro_sum (Sum_t All) it = case it of
  {}
eval_intro_sum trep@(Sum_t (And _ _)) anyt = do
  typeSpec <- sum_type_spec trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
  initList <- sum_field_inits anyt
  let pexpr = C.PostfixInits typeName initList
  type_rep_val trep (postfixExprIsCondExpr pexpr)

product_field_inits
  :: Natural
  -> Expr ExprF CodeGen Val s t
  -> Fields CodeGen Val s ts
  -> CodeGen s C.InitList
product_field_inits n cgt AllF = do
  exprVal <- eval_expr' cgt
  designator <- simple_designator ("field_" ++ show n)
  pure $ C.InitBase (Just designator) (C.InitExpr (condExprIsAssignExpr (getVal exprVal)))
product_field_inits n cgt (AndF cgt' cgts) = do
  exprVal <- eval_expr' cgt
  designator <- simple_designator ("field_" ++ show n)
  subList <- product_field_inits (n+1) cgt' cgts
  pure $ C.InitCons subList (Just designator) (C.InitExpr (condExprIsAssignExpr (getVal exprVal)))

-- | The init list for a sum struct: its tag and its variant.
sum_field_inits :: Variant CodeGen Val s ts -> CodeGen s C.InitList
sum_field_inits anyt = do
  tagExpr <- condExprIsAssignExpr <$> sum_tag_expr 0 anyt
  variantInitList <- sum_variant_init_list 0 anyt
  pure $ C.InitCons
    (C.InitBase (Just (ident_designator ident_tag)) (C.InitExpr tagExpr))
    (Just (ident_designator ident_variant))
    -- Sad naming convention from the spec: it's not initializing an array, it's
    -- just an array of initializers. It's how we get to give an initializer
    -- without specifying the union type name.
    (C.InitArray variantInitList)

-- | The expression for a sum's tag: determined by the offset in the disjuncts
-- in the type signature, and the common "tag_" prefix.
sum_tag_expr :: Natural -> Variant f val s ts -> CodeGen s C.CondExpr
sum_tag_expr n (OrV there) = sum_tag_expr (n+1) there
sum_tag_expr n (AnyV _) = do
  ident <- maybeError
    (CodeGenInternalError $ "sum_tag_expr invalid tag field " ++ show n)
    (pure (stringIdentifier ("tag_" ++ show n)))
  pure $ primExprIsCondExpr $ C.PrimIdent ident

-- | The variant expression for a sum: it's a union literal, _without_ a
-- pointer (sums hold their tags and unions directly).
sum_variant_init_list
  :: Natural
  -> Variant CodeGen Val s ts
  -> CodeGen s C.InitList
sum_variant_init_list n (OrV there) = sum_variant_init_list (n+1) there
sum_variant_init_list n (AnyV cgt) = do
  exprVal <- eval_expr' cgt
  designator <- simple_designator ("variant_" ++ show n)
  let initExpr = C.InitExpr (condExprIsAssignExpr (getVal exprVal))
  pure $ C.InitBase (Just designator) initExpr

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
  :: TypeRep ('Sum types)
  -> TypeRep r
  -> Cases CodeGen Val s types r
  -> Expr ExprF CodeGen Val s ('Sum types)
  -> CodeGen s (Val s r)
eval_elim_sum trep rrep cases cgt = do
  typeSpec <- sum_type_spec trep
  cgtVal <- eval_expr' cgt
  -- Our two declarations: scrutinee and result.
  -- Declaring the scrutinee is important, so that we don't _ever_ have a case
  -- statement in which the scrutinee is repeatedly constructed at each case.
  (_scrutineeIdent, scrutineeVal) <- declare_initialized   "scrutinee" cgtVal
  (resultIdent, resultVal)        <- declare_uninitialized "result"    rrep
  -- We take two expressions in the object-language (forgetting their
  -- meta-language types): the sum's tag and its variant. These are taken by way
  -- of the indirect accessor. The union, however, will be accessed using the
  -- direct dot accessor, for the struct itself contains the union directly.
  let tagPostfixExpr :: C.PostfixExpr
      tagPostfixExpr = C.PostfixDot
        (condExprIsPostfixExpr (getVal scrutineeVal))
        ident_tag
      tagExpr :: C.Expr
      tagExpr = postfixExprIsExpr tagPostfixExpr
      variantExpr = C.PostfixDot
        (condExprIsPostfixExpr (getVal scrutineeVal))
        ident_variant
  -- If the sum is empty, the result is a switch statement with no cases behind
  -- it. That's a no-op. The result variable will remain undefined.
  -- Should be you can never introduce an empty sum, so this code should not
  -- be reachable.
  caseBlockItems :: [C.BlockItem] <- case trep of
    Sum_t All       -> pure []
    Sum_t (And _ _) -> NE.toList <$> eval_elim_sum_cases 0 rrep
      (postfixExprIsEqExpr tagPostfixExpr)
      variantExpr
      resultIdent
      cases
  let casesStmt :: C.Stmt
      casesStmt = C.StmtCompound $ C.Compound $ blockItemList caseBlockItems
      switchItem :: C.BlockItem
      switchItem = C.BlockItemStmt $ C.StmtSelect $ C.SelectSwitch tagExpr casesStmt
  addBlockItem switchItem
  pure resultVal

-- | Make a declaration assigning the given value to a new identifier.
-- The resulting Val is that identifier.
declare_initialized :: String -> Val s t -> CodeGen s (C.Ident, Val s t)
declare_initialized prefix val = do
  ident <- fresh_binder prefix
  -- Now we must make a block item which assigns the value `it` to the
  -- identifier `ident`.
  -- Every initialized binding is const.
  --
  --   const <typeSpec> <ident> = <rexpr>;
  --   |______________| |_____|   |_____|
  --      declnSpecs     decln     init
  --
  let declnSpecs :: C.DeclnSpecs
      declnSpecs = C.DeclnSpecsQual C.QConst $ Just $ C.DeclnSpecsType (valSpecs val) Nothing
      declr :: C.Declr
      declr = C.Declr (valPtr val) (C.DirectDeclrIdent ident)
      cexpr :: C.CondExpr
      cexpr = getVal val
      cinit :: C.Init
      cinit = C.InitExpr (condExprIsAssignExpr cexpr);
      initDeclr :: C.InitDeclr
      initDeclr = C.InitDeclrInitr declr cinit
      initDeclrList :: C.InitDeclrList
      initDeclrList = C.InitDeclrBase initDeclr
      blockItem :: C.BlockItem
      blockItem = C.BlockItemDecln $ C.Decln declnSpecs (Just initDeclrList)
  addBlockItem blockItem
  let val' = Val
        { getVal   = identIsCondExpr ident
        , valSpecs = valSpecs val
        , valPtr   = valPtr val
        }
  pure (ident, val')

-- | Make a declaration without initializing it.
-- If it's a pointer type we make sure it's not declared const.
-- See 'declare_initialized', which is defined similarly.
declare_uninitialized :: String -> TypeRep t -> CodeGen s (C.Ident, Val s t)
declare_uninitialized prefix trep = do
  ident <- fresh_binder prefix
  let ptr = type_ptr trep
  typeSpec <- type_spec trep
  let declnSpecs = C.DeclnSpecsType typeSpec Nothing
      declr :: C.Declr
      declr = C.Declr ptr (C.DirectDeclrIdent ident)
      initDeclr :: C.InitDeclr
      initDeclr = C.InitDeclr declr
      initDeclrList :: C.InitDeclrList
      initDeclrList = C.InitDeclrBase initDeclr
      blockItem :: C.BlockItem
      blockItem = C.BlockItemDecln $ C.Decln declnSpecs (Just initDeclrList)
  addBlockItem blockItem
  let val = Val
        { getVal   = identIsCondExpr ident
        , valSpecs = typeSpec
        , valPtr   = ptr
        }
  pure (ident, val)

-- | Makes the cases in a switch statement for a sum elimination.
eval_elim_sum_cases
  :: Natural
  -> TypeRep r
  -> C.EqExpr -- ^ The tag of the sum
  -> C.PostfixExpr -- ^ The variant of the sum
  -> C.Ident -- ^ Identifier of the place to assign the result.
  -> Cases CodeGen Val s (ty ': tys) r
  -> CodeGen s (NonEmpty C.BlockItem)
eval_elim_sum_cases n rrep tagExpr variantExpr resultIdent (AndC trep k cases) = do
  -- We need the identifiers for the enum tag, and the union variant, at this
  -- case.
  tagIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (pure (stringIdentifier ("tag_" ++ show n)))
  variantIdent <- maybeError
    (CodeGenInternalError $ "eval_elim_sum_with_cases bad identifier")
    (pure (stringIdentifier ("variant_" ++ show n)))
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
  let valueSelector :: C.PostfixExpr
      valueSelector = C.PostfixDot variantExpr variantIdent
  valInThisCase <- type_rep_val trep (postfixExprIsCondExpr valueSelector)
  (expr, blockItems) <- withNewScope $ eval_expr' (k (value valInThisCase))
  let -- Here we have the result assignment and the case break, the final two
      -- statements in the compound statement.
      resultAssignment :: C.BlockItem
      resultAssignment = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $
        C.ExprAssign $ C.Assign
          (identIsUnaryExpr resultIdent)
          C.AEq
          (condExprIsAssignExpr (getVal expr))
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
    AllC -> pure $ blockItem NE.:| []
    cases'@(AndC _ _ _) -> do
      items <- eval_elim_sum_cases (n+1) rrep tagExpr variantExpr resultIdent cases'
      pure $ NE.cons blockItem items

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

identIsRelExpr :: C.Ident -> C.RelExpr
identIsRelExpr = C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

identIsUnaryExpr :: C.Ident -> C.UnaryExpr
identIsUnaryExpr = C.UnaryPostfix . C.PostfixPrim . C.PrimIdent

identIsPostfixExpr :: C.Ident -> C.PostfixExpr
identIsPostfixExpr = condExprIsPostfixExpr . identIsCondExpr

postfixExprIsCondExpr :: C.PostfixExpr -> C.CondExpr
postfixExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary . C.UnaryPostfix

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

unaryExprIsCondExpr :: C.UnaryExpr -> C.CondExpr
unaryExprIsCondExpr = C.CondLOr . C.LOrAnd . C.LAndOr . C.OrXOr . C.XOrAnd .
  C.AndEq . C.EqRel . C.RelShift . C.ShiftAdd . C.AddMult . C.MultCast .
  C.CastUnary

ident_designator :: C.Ident -> C.Design
ident_designator = C.Design . C.DesigrBase . C.DesigrIdent

simple_designator :: String -> CodeGen s C.Design
simple_designator str = do
  ident <- maybeError
    (CodeGenInternalError $ "simple_designator bad identifier")
    (pure (stringIdentifier str))
  pure $ C.Design $ C.DesigrBase $ C.DesigrIdent ident

-- | All numbers are put out in hex. C decimals are just harder to work with,
-- since 0 is not a decimal number, but rather an octal one.
hex_const :: Natural -> C.HexConst
hex_const = hexConst . hexDigits

data CodeGenError where
  -- | Indicates a bug in this program.
  CodeGenInternalError :: String -> CodeGenError

deriving instance Show CodeGenError

-- | Scope information: one number for the "major" scope, indicating how many
-- nested scopes we have taken, and one "minor" indicating how many bindings
-- have been created in the major scope.
--
-- This is used to come up with C variable identifiers
--
--   uint8_t prefix_major_minor = 42;
--
data Scope = Scope
  { scopeMajor :: !Natural
  , scopeMinor :: !Natural
  }

scope_init :: Scope
scope_init = Scope { scopeMajor = 0, scopeMinor = 0 }

scope_new :: Scope -> Scope
scope_new s = s { scopeMajor = scopeMajor s + 1, scopeMinor = 0 }

scope_next :: Scope -> ((Natural, Natural), Scope)
scope_next s = ((scopeMajor s, scopeMinor s), s { scopeMinor = scopeMinor s + 1 })

fresh_binder :: String -> CodeGen s C.Ident
fresh_binder prefix = do
  st <- CodeGen $ Trans.lift get
  let scope NE.:| scopes = cgsScope st
      ((major, minor), scope') = scope_next scope
      st' = st { cgsScope = scope' NE.:| scopes }
      bindName = prefix ++ "_" ++ show major ++ "_" ++ show minor
  ident <- maybeError
    (CodeGenInternalError $ "fresh_binder invalid " ++ show bindName)
    (pure (stringIdentifier bindName))
  CodeGen $ Trans.lift $ put st'
  pure ident

-- | Code generation modifies a `CodeGenState` from an initial empty state.
--
-- This state is relative to some C expression which is being built-up (see
-- the `CodeGen` and `CodeGen` types). That expression may make reference to
-- C compound types (structs, unions, enums) and also to variable declarations.
-- In order to give those declarations meaning, it may be necessary to carry
-- out a compound statement _before_ this expression is evaluated. All of this
-- information is contained here in the code generation state.
--
data CodeGenState = CodeGenState
  { -- | C declarations in reverse order. This includes enum, union, and struct
    -- declarations induced by compound types encountered during code
    -- generation.
    cgsDeclns :: ![C.Decln]
    -- | C block items composing a compound statement which must be evaluated
    -- before the expression. It's in reverse order: head of list is the last
    -- to be evaluated.
    --
    -- In good faith this should be in a writer monad. CodeGen terms will never
    -- remove anything from this list.
  , cgsBlockItems :: ![C.BlockItem]
    -- | Scope information for making variable names.
  , cgsScope      :: !(NonEmpty Scope)
    -- | Product types encountered.
  , cgsProducts   :: !(Map TypeIdentifier ProductDeclr)
    -- | Sum types encountered.
  , cgsSums       :: !(Map TypeIdentifier SumDeclr)
  }

-- | The C translation unit for a CodeGenState. This is the type declarations,
--
-- Must give a function definition which serves as the "main" function for
-- this CodeGen. This ensures we always have at least one declaration and
-- therefore do indeed get a translation unit.
--
-- TODO extern declarations, followed by function definitions.
codeGenTransUnit :: CodeGenState -> C.FunDef -> C.TransUnit
codeGenTransUnit cgs mainFunDef = mkTransUnit (C.ExtFun mainFunDef NE.:| extDeclns)
  where

  mkTransUnit :: NonEmpty C.ExtDecln -> C.TransUnit
  mkTransUnit (t NE.:| [])      = C.TransUnitBase t
  mkTransUnit (t NE.:| (t':ts)) = C.TransUnitCons (mkTransUnit (t' NE.:| ts)) t

  extDeclns :: [C.ExtDecln]
  extDeclns = fmap C.ExtDecln (cgsDeclns cgs)

codeGenCompoundStmt :: CodeGenState -> C.CompoundStmt
codeGenCompoundStmt = C.Compound . blockItemList . cgsBlockItems

blockItemListNE :: NonEmpty C.BlockItem -> C.BlockItemList
blockItemListNE (item NE.:| [])              = C.BlockItemBase item
blockItemListNE (item NE.:| (item' : items)) = C.BlockItemCons
  (blockItemListNE (item' NE.:| items))
  item

blockItemList :: [C.BlockItem] -> Maybe C.BlockItemList
blockItemList []             = Nothing
blockItemList (item : items) = Just (blockItemListNE (item NE.:| items))

-- | The C declaration (not definition) of the type representing this product.
data ProductDeclr = ProductDeclr { pdTypeSpec :: !C.TypeSpec }

-- | The C declaration (not definition) of the type representing this sum.
data SumDeclr = SumDeclr { sdTypeSpec :: !C.TypeSpec }

data NonEmptyFields where
  NonEmptyFields :: All TypeRep (ty ': tys) -> NonEmptyFields

type TypeIdentifier = SomeTypeRep

-- | Represents an object-language value within a 'CodeGen' context (the `s`
-- type parameter, the ST/STRef trick).
--
-- TODO it may be useful to make this a sum
--
--     Name C.Ident
--   | Expression C.Expr
--   | Unreachable
--
-- this way we could easily "eta-reduce" when binding a name to another name,
-- and we'd also get some code reduction for impossible cases, i.e. elimination
-- of an empty sum.
--
data Val (s :: Haskell.Type) (t :: Type) = Val
  { getVal   :: !C.CondExpr
  -- TODO use CTypeInfo rather than these 2 fields.
  , valSpecs :: !C.TypeSpec
  , valPtr   :: !(Maybe C.Ptr)
  }

-- | A monad to ease the expression of code generation, which carries some
-- state and may exit early with error cases.
newtype CodeGen (s :: Haskell.Type) (t :: Haskell.Type) = CodeGen
  { runCodeGen :: ExceptT CodeGenError (StateT CodeGenState Identity) t }

deriving instance Functor (CodeGen s)
deriving instance Applicative (CodeGen s)
deriving instance Monad (CodeGen s)

-- | Run a CodeGen in a fresh scope, giving back all of the generated block
-- items. This allows you to create a new scope using a compound statement.
withNewScope :: CodeGen s t -> CodeGen s (t, [C.BlockItem])
withNewScope cg = CodeGen $ do
  st <- Trans.lift get
  let scopes = cgsScope st
      scope' = scope_new (NE.head scopes)
      blockItems = cgsBlockItems st
      blockItems' = []
      st' = st { cgsBlockItems = blockItems', cgsScope = NE.cons scope' scopes }
      Identity (outcome, st'') = runStateT (runExceptT (runCodeGen cg)) st'
      newBlockItems = cgsBlockItems st''
  Trans.lift $ put $ st'' { cgsBlockItems = blockItems, cgsScope = scopes }
  t <- except outcome
  pure (t, newBlockItems)

addBlockItem :: C.BlockItem -> CodeGen s ()
addBlockItem !bitem = CodeGen $ do
  st <- Trans.lift get
  let bitems = cgsBlockItems st
      !st' = st { cgsBlockItems = bitem : bitems }
  Trans.lift $ put st'

evalCodeGen :: CodeGen s t -> (Either CodeGenError t, CodeGenState)
evalCodeGen cgm = runIdentity (runStateT (runExceptT (runCodeGen cgm)) initialState)
  where
  initialState = CodeGenState
    { cgsDeclns     = []
    , cgsBlockItems = []
    , cgsScope      = scope_init NE.:| []
    , cgsProducts   = mempty
    , cgsSums       = mempty
    }

-- | Run a CodeGen term and generate a translation unit.
-- It contains a function eval which evaluates the expression behind the
-- `Val s t` and returns it. That C value will be completely standalone: no
-- pointers in it. The translation unit includes everything that is needed in
-- order to compute that value, nothing more.
codeGen :: CodeGen s (Val s t) -> Either CodeGenError C.TransUnit
codeGen cg = fmap mkTransUnit outcome
  where
  (outcome, cgs) = evalCodeGen cg
  mkTransUnit :: Val s t -> C.TransUnit
  mkTransUnit val = codeGenTransUnit cgs (mainFun val cgs) 
  -- This function computes the expression.
  -- TODO we'll want to factor this out and re-use it if we decide to allow
  -- for the expression of subroutines.
  mainFun :: Val s t -> CodeGenState -> C.FunDef
  mainFun val cgs' =
    let declnSpecs :: C.DeclnSpecs
        declnSpecs = C.DeclnSpecsType (valSpecs val) Nothing
        expr :: C.CondExpr
        expr = getVal val
        declr :: C.Declr
        declr = C.Declr Nothing $ C.DirectDeclrFun2
          (C.DirectDeclrIdent ident_eval)
          Nothing
        args :: Maybe C.DeclnList
        args = Nothing
        exprBlockItem :: C.BlockItem
        exprBlockItem = C.BlockItemStmt $ C.StmtJump $ C.JumpReturn $ Just $
          condExprIsExpr expr
        compoundStmt :: C.CompoundStmt
        compoundStmt = C.Compound $ Just $ case blockItemList (cgsBlockItems cgs') of
          Nothing  -> C.BlockItemBase exprBlockItem
          Just bil -> C.BlockItemCons bil exprBlockItem
    in  C.FunDef declnSpecs declr args compoundStmt

-- | Dereferences a CondExpr as many times as necessary according to the ptr
-- argument (assumes the CondExpr represents something of type with that many
-- pointers).
dereference :: Maybe C.Ptr -> C.CondExpr -> C.CondExpr
dereference Nothing cexpr = cexpr
dereference (Just (C.PtrBase _))     cexpr = unaryExprIsCondExpr $
  C.UnaryOp C.UODeref (condExprIsCastExpr cexpr)
dereference (Just (C.PtrCons _ ptr)) cexpr = unaryExprIsCondExpr $
  C.UnaryOp C.UODeref (condExprIsCastExpr (dereference (Just ptr) cexpr))

codeGenToFile :: String -> CodeGen s (Val s t) -> IO ()
codeGenToFile fp cg = case codeGen cg of
  Left  err       -> throwIO (userError (show err))
  Right transUnit -> writeFile fp $ includes ++ prettyPrint transUnit
  where
  includes = mconcat
    [ "#include <stdint.h>\n"
    , "#include <stdio.h>\n"
    ]

codeGenError :: CodeGenError -> CodeGen s x
codeGenError err = CodeGen (throwE err)

maybeError :: CodeGenError -> CodeGen s (Maybe x) -> CodeGen s x
maybeError err act = do
  x <- act
  maybe (codeGenError err) pure x

assertValidIdentifier :: String -> Maybe C.Ident -> C.Ident
assertValidIdentifier msg Nothing  = error msg
assertValidIdentifier _   (Just i) = i

-- | Make a C identifier from a string. Will fail if the string is malformed
-- w.r.t. valid C identifiers.
stringIdentifier :: forall s . String -> Maybe C.Ident
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

symbolIdentifier :: forall name s . KnownSymbol name => Proxy name -> Maybe C.Ident
symbolIdentifier p = stringIdentifier (symbolVal p)

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
append_ident left (C.IdentBase idnd) = C.IdentConsNonDigit left idnd
append_ident left (C.IdentConsNonDigit right idnd) = C.IdentConsNonDigit (append_ident left right) idnd
append_ident left (C.IdentCons right idd) = C.IdentCons (append_ident left right) idd

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

-- | "_static"
ident__static :: C.Ident
ident__static =
  C.IdentConsNonDigit
    (C.IdentConsNonDigit
      (C.IdentConsNonDigit
        (C.IdentConsNonDigit
          (C.IdentConsNonDigit
            (C.IdentConsNonDigit
              (C.IdentBase (C.IdentNonDigit C.NDUnderscore))
              (C.IdentNonDigit C.NDs)
            )
            (C.IdentNonDigit C.NDt)
          )
          (C.IdentNonDigit C.NDa)
        )
        (C.IdentNonDigit C.NDt)
      )
      (C.IdentNonDigit C.NDi)
    )
    (C.IdentNonDigit C.NDc)
