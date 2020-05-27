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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE EmptyCase #-}

module Pilot.C where

import Control.Monad (when)
import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Compose
import Data.Functor.Identity

import Data.Foldable (toList)
import qualified Data.Kind as Haskell (Type)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Proxy (Proxy (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import GHC.TypeLits (KnownSymbol, symbolVal)
import Numeric.Natural (Natural)

import qualified Language.C99.AST as C
import Language.C99.Pretty (Pretty, pretty)
import Text.PrettyPrint (render)

import Pilot.EDSL.Expr
-- TODO these should not be in the Point module.
import Pilot.EDSL.Point (All (..), Any (..), Selector (..), Case (..),
  anyOfAll, forAll, mapAll)
import Pilot.EDSL.Point (Signedness (..), Width (..), SignednessRep (..), WidthRep (..))
import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Fun
import Pilot.Types.Nat
import Pilot.Types.Represented

import qualified Pilot.Pure as Pure (Point (..), F, eval_point_)

import System.IO (writeFile)
import System.IO.Error (userError)
import Control.Exception (throwIO)

-- TODO NEXT STEPS
--
-- - C specific IO
--   - Input corresponds exactly to externs
--   - Output is set up by way of "triggers": multiple streams can be combined
--     into one trigger, along with a string identifier, resulting in an
--     extern function declaration.
--     Then multiple triggers may be combined monoidally.
--
--       nop :: Trigger
--       (<>) :: Trigger -> Trigger -> Trigger
--       trigger :: TriggerCInfo -> TriggerStreams -> CodeGen s Trigger
--
--     To get a full C program you would need something of type
--
--       ExprM <EDSL> (Stream s) (CodeGen s) (Trigger s)
--
--     which can use the "pure" EDSL but ultimately commits to the C backend
--     types.
--
-- - Simplify declare_product and declare_sum: just put the root name and the
--   usage into the map, and generate the declarations at the end like we did
--   before... ah yes but we still need the order... so track the order as
--   well and then insertion sort them by that.
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

-- | Useful for debugging: C AST types, including the translation unit, have
-- Pretty instances.
prettyPrint :: Pretty a => a -> String
prettyPrint = render . pretty

eval_point :: Expr Point.ExprF (Point s) (CodeGen s) t -> CodeGen s (Point s t)
eval_point = evalExprM eval_point_expr eval_point_bind . runExpr

eval_stream :: StreamExpr s t -> CodeGen s (Stream s t)
eval_stream = evalExprM eval_stream_expr eval_stream_bind . runExpr

-- | For naming/substitution in the CodeGenM monad: a C declaration is used.
eval_point_bind :: Point s t -> CodeGen s (Point s t)
eval_point_bind point = declare_initialized_point "point_binder" point

-- | Like 'eval_point_bind' but for streams: do the same thing, but behind the
-- offset function.
--
-- TODO ideally, if we make a binding to a memory stream, it doesn't create a
-- new binder, it just uses the name of the static thing.
-- Could do the same for C externs. 
eval_stream_bind :: Stream s t -> CodeGen s (Stream s t)
eval_stream_bind stream = declare_initialized_stream "stream_binder" stream

eval_point_expr
  :: Point.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) t
  -> CodeGen s (Point s t)
eval_point_expr (Point.IntroInteger tr il)        = eval_intro_integer tr il
eval_point_expr (Point.PrimOp primop)             = eval_primop primop
eval_point_expr (Point.IntroProduct tr fields)    = eval_intro_product tr fields
eval_point_expr (Point.ElimProduct tr tr' sel it) = eval_elim_product tr tr' sel it
eval_point_expr (Point.IntroSum tr tr' variant)   = eval_intro_sum tr tr' variant
eval_point_expr (Point.ElimSum tr rr it cases)    = eval_elim_sum tr rr it cases

-- We can only run stream expressions which unify with these types

type StreamExprF s = Stream.ExprF
  (Expr Point.ExprF (Point s) (CodeGen s))
  (Expr Point.ExprF Pure.Point Pure.F)
  (Expr (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Pure.F)) (Stream s) (CodeGen s))

type StreamExpr s = Expr
  (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Pure.F))
  (Stream s)
  (CodeGen s)

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

-- | The C type specifier, and whether it should be taken through a pointer.
data CTypeInfo = CTypeInfo
  { ctypeSpec :: !C.TypeSpec
  , ctypePtr  :: !Bool
  }

-- | Representation of a point (values in the pointwise EDSL).
data Point s (t :: Point.Type) = Point
  { pointExpr      :: !C.CondExpr
  , pointTypeRep   :: !(Point.TypeRep t)
  , pointCTypeInfo :: !CTypeInfo
  }

pointPtr :: Point s t -> Bool
pointPtr = ctypePtr . pointCTypeInfo

pointTypeSpec :: Point s t -> C.TypeSpec
pointTypeSpec = ctypeSpec . pointCTypeInfo

streamPtr :: Stream s t -> Bool
streamPtr = ctypePtr . streamCTypeInfo

streamTypeSpec :: Stream s t -> C.TypeSpec
streamTypeSpec = ctypeSpec . streamCTypeInfo

data StreamVal s (t :: Stream.Type Point.Type) where
  StreamValConstant :: !C.CondExpr -> StreamVal s ('Stream.Stream n t)
  StreamValStatic   :: !StaticStreamVal -> StreamVal s ('Stream.Stream n t)
  -- | The expression at this offset, and a way to get the expression at
  -- later offsets.
  StreamValFunction :: !(Offset n -> CodeGen s C.CondExpr)
                    -> StreamVal s ('Stream.Stream n t)

data ExternStream = ExternStream
  { esGlobal :: !C.Ident
  , esLocal  :: !C.Ident
  }

data StaticStreamVal = StaticStreamVal
  { ssvIndex  :: !C.Ident
  , ssvArray  :: !C.Ident
  , ssvSize   :: !Natural -- ^ Of the C array
  , ssvOffset :: !Natural -- ^ Used in computing stream drops
  }

-- | Takes the static stream's static array identifier and indexes it at the
-- appropriate offset (modulo its size)
staticStreamAtOffset :: Natural -> StaticStreamVal -> C.CondExpr
staticStreamAtOffset n ssv = postfixExprIsCondExpr $ C.PostfixIndex
  (identIsPostfixExpr (ssvArray ssv))
  indexExpr
  where
  indexExpr :: C.Expr
  indexExpr = multExprIsExpr $
    C.MultMod (addExprIsMultExpr index) (constIsCastExpr modulus)
  -- n gives the local offset, ssvOffset ssv accounts for any changes from
  -- a drop on this stream. Their sum gives the value to add to the current
  -- index. If it's 0, we skip this.
  index :: C.AddExpr
  index =
    if (n + ssvOffset ssv) == 0
    then identIsAddExpr (ssvIndex ssv)
    else C.AddPlus (identIsAddExpr (ssvIndex ssv)) (constIsMultExpr addIndex)
  addIndex :: C.Const
  addIndex = C.ConstInt $ C.IntHex (hex_const (n + ssvOffset ssv)) Nothing
  modulus :: C.Const
  modulus = C.ConstInt $ C.IntHex (hex_const (ssvSize ssv)) Nothing

-- | Representation of a stream of points (values in the streamwise EDSL over
-- the pointwise EDSL).
data Stream s (t :: Stream.Type Point.Type) = Stream
  { streamVal       :: !(StreamVal s t)
  , streamTypeRep   :: !(Stream.TypeRep t)
  , streamCTypeInfo :: !CTypeInfo
  }

-- How are streams represented? It depends upon how they are composed...
--
-- - Point streams (Stream.point, type 'Constant t) take the same representation
--   of an EDSL Point: the type Point t.
-- - Constant streams also: Point t. These are identical to pointwise
--   expressions, and could even be factored out and precomputed.
-- - External streams: a C identifier of the copy of the extern.
-- - Memory streams: a C identifier of the array, C identifier of the current
--   index, and size to use as modulus when doing stream drop
-- - Composite streams... The generated code depends upon the offset being
--   taken, so Offset n -> CondExpr seems like the obvious choice.
--
-- It would be good to have the function as a derived thing

streamExprAtOffset :: Offset n -> StreamVal s ('Stream.Stream n t) -> CodeGen s C.CondExpr
streamExprAtOffset _   (StreamValConstant c) = pure c
streamExprAtOffset off (StreamValStatic ssv) = pure $ staticStreamAtOffset (offsetToNatural off) ssv
streamExprAtOffset off (StreamValFunction k) = k off

streamExprNow :: StreamVal s ('Stream.Stream n t) -> CodeGen s C.CondExpr
streamExprNow = streamExprAtOffset Current

streamArgToPointArg
  :: Offset n
  -> NatRep n
  -> Stream s ('Stream.Stream n t)
  -> Expr Point.ExprF (Point s) (CodeGen s) t
streamArgToPointArg offset nrep stream = Pilot.EDSL.Expr.special $ do
  expr <- streamExprAtOffset offset (streamVal stream)
  pure $ Point
    { pointExpr      = expr
    , pointTypeRep   = case streamTypeRep stream of
        Stream.Stream_t _ trep -> trep
    , pointCTypeInfo = streamCTypeInfo stream
    }

streamArgsToPointArgs
  :: Offset n
  -> NatRep n
  -> Args Point.TypeRep args
  -> Args (Stream s) (MapArgs ('Stream.Stream n) args)
  -> Args (Expr Point.ExprF (Point s) (CodeGen s)) args
streamArgsToPointArgs offset nrep Args              Args           = Args
streamArgsToPointArgs offset nrep (Arg rep argsrep) (Arg arg args) = Arg
  (streamArgToPointArg   offset nrep arg)
  (streamArgsToPointArgs offset nrep argsrep args)

stream_drop
  :: forall s n t .
     Stream s ('Stream.Stream ('S n) t)
  -> Stream s ('Stream.Stream     n  t)
stream_drop stream = Stream
  { streamVal       = val
  , streamTypeRep   = typeRep
  , streamCTypeInfo = streamCTypeInfo stream
  }
  where
  typeRep :: Stream.TypeRep ('Stream.Stream n t)
  typeRep = case streamTypeRep stream of
    Stream.Stream_t (S_t nrep) trep -> Stream.Stream_t nrep trep

  val :: StreamVal s ('Stream.Stream n t)
  val = case streamVal stream of
    -- Dropping from a constant? Same thing.
    StreamValConstant c -> StreamValConstant c
    -- Dropping from a static memory stream: bump the index.
    StreamValStatic   s -> StreamValStatic $ s { ssvOffset = 1 + ssvOffset s }
    StreamValFunction k -> StreamValFunction (withNextOffset k)

stream_shift
  :: forall s n t .
     Stream s ('Stream.Stream ('S n) t)
  -> Stream s ('Stream.Stream     n  t)
stream_shift stream = Stream
  { streamVal       = val
  , streamTypeRep   = typeRep
  , streamCTypeInfo = streamCTypeInfo stream
  }
  where
  typeRep :: Stream.TypeRep ('Stream.Stream n t)
  typeRep = case streamTypeRep stream of
    Stream.Stream_t (S_t nrep) trep -> Stream.Stream_t nrep trep

  val :: StreamVal s ('Stream.Stream n t)
  val = case streamVal stream of
    StreamValConstant c -> StreamValConstant c
    StreamValStatic   s -> StreamValStatic s
    StreamValFunction k -> StreamValFunction (withSameOffset k)

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


{-
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
-}

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
  st <- CodeGen $ Trans.lift get
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

        CodeGen $ Trans.lift $ modify' $ \st -> 
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

        CodeGen $ Trans.lift $ modify' $ \st -> 
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

      CodeGen $ Trans.lift $ modify' $ \st ->
        st { cgsProducts = Map.insert someTypeRep declr (cgsProducts st) }

      declnList <- field_declns ctt product_field_name 0 (NonEmptyFields fields)

      let !productIdent = case ctt of
            NotShared -> identNotShared
            Shared    -> identShared

          productSpec = product_decln_type_spec productIdent
          productDef = product_defn_type_spec productIdent declnList

          productDecln = C.Decln (C.DeclnSpecsType productDef Nothing) Nothing

          cdeclns = [productDecln]

      CodeGen $ Trans.lift $ modify' $ \st ->
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
  st <- CodeGen $ Trans.lift get
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

        CodeGen $ Trans.lift $ modify' $ \st -> 
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

        CodeGen $ Trans.lift $ modify' $ \st -> 
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

      CodeGen $ Trans.lift $ modify' $ \st ->
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

      CodeGen $ Trans.lift $ modify' $ \st ->
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
  :: Point.PrimOpF (Expr Point.ExprF (Point s) (CodeGen s)) t
  -> CodeGen s (Point s t)
eval_primop (Point.Arithmetic arithop) = eval_arithop arithop
eval_primop (Point.Bitwise bitop)      = eval_bitop bitop
eval_primop (Point.Relative relop)     = eval_relop relop

eval_arithop
  :: Point.ArithmeticOpF (Expr Point.ExprF (Point s) (CodeGen s)) t
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_neg_integer tr vx  = do
  x <- eval_point vx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOMin $
        condExprIsCastExpr (pointExpr x)
  type_rep_val tr expr

eval_bitop
  :: Point.BitwiseOpF (Expr Point.ExprF (Point s) (CodeGen s)) t
  -> CodeGen s (Point s t)
eval_bitop (Point.AndB tr x y)   = eval_and_bitwise tr x y
eval_bitop (Point.OrB  tr x y)   = eval_or_bitwise  tr x y
eval_bitop (Point.XOrB tr x y)   = eval_xor_bitwise tr x y
eval_bitop (Point.NotB tr x)     = eval_not_bitwise tr x
eval_bitop (Point.ShiftL tr x y) = eval_shiftl_bitwise tr x y
eval_bitop (Point.ShiftR tr x y) = eval_shiftr_bitwise tr x y

eval_and_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_not_bitwise tr bx = do
  x <- eval_point bx
  let expr = unaryExprIsCondExpr $ C.UnaryOp C.UOBNot
        (condExprIsCastExpr (pointExpr x))
  type_rep_val tr expr

eval_shiftl_bitwise
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer 'Unsigned 'Eight)
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
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer 'Unsigned 'Eight)
  -> CodeGen s (Point s ('Point.Integer signedness width))
eval_shiftr_bitwise tr bx by = do
  x <- eval_point bx
  y <- eval_point by
  let expr = shiftExprIsCondExpr $ C.ShiftRight
        (condExprIsShiftExpr (pointExpr x))
        (condExprIsAddExpr   (pointExpr y))
  type_rep_val tr expr

eval_relop
  :: Point.RelativeOpF (Expr Point.ExprF (Point s) (CodeGen s)) t
  -> CodeGen s (Point s t)
eval_relop (Point.Cmp trep trepr x y lt eq gt) = eval_cmp trep trepr x y lt eq gt

eval_cmp
  :: Point.TypeRep ('Point.Integer signedness width)
  -> Point.TypeRep r
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Integer signedness width)
  -> Expr Point.ExprF (Point s) (CodeGen s) r
  -> Expr Point.ExprF (Point s) (CodeGen s) r
  -> Expr Point.ExprF (Point s) (CodeGen s) r
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
  -> Expr Point.ExprF (Point s) (CodeGen s) t
  -> CodeGen s (Stream s ('Stream.Stream n t))
eval_constant_stream trep nrep pexpr = do
  point <- eval_point pexpr
  pure $ Stream
    { streamVal       = StreamValConstant (pointExpr point)
    , streamTypeRep   = Stream.Stream_t nrep (pointTypeRep point)
    , streamCTypeInfo = pointCTypeInfo point
    }

eval_drop_stream
  :: Point.TypeRep t
  -> NatRep ('S n)
  -> Expr
       (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Identity))
       (Stream s)
       (CodeGen s)
       ('Stream.Stream ('S n) t)
  -> CodeGen s (Stream s ('Stream.Stream n t))
eval_drop_stream trep nrep expr = do
  stream <- eval_stream expr
  pure $ stream_drop stream

eval_shift_stream
  :: Point.TypeRep t
  -> NatRep ('S n)
  -> Expr
       (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Pure.F))
       (Stream s)
       (CodeGen s)
       ('Stream.Stream ('S n) t)
  -> CodeGen s (Stream s ('Stream.Stream n t))
eval_shift_stream trep nrep expr = do
  stream <- eval_stream expr
  pure $ stream_shift stream

eval_lift_stream
  :: forall args s n r .
     Args Point.TypeRep args
  -> Point.TypeRep r
  -> NatRep n
  -> (Args (Expr Point.ExprF (Point s) (CodeGen s)) args -> Expr Point.ExprF (Point s) (CodeGen s) r)
  -> Args (StreamExpr s) (MapArgs ('Stream.Stream n) args)
  -> CodeGen s (Stream s ('Stream.Stream n r))
eval_lift_stream argsrep trep nrep k args = do

  ctt <- compoundTypeTreatment
  tinfo <- type_info ctt trep

  -- Evaluate all of the stream arguments.
  streamArgs :: Args (Stream s) (MapArgs ('Stream.Stream n) args)
    <- traverseArgs eval_stream args

  -- If this stream has a nonzero prefix, we do not elaborate the code at
  -- all offsets. Instead we use a function
  --   Offset n -> CodeGen s C.CondExpr
  --
  let f :: Offset n -> CodeGen s C.CondExpr
      f = \offset -> do
        let args  = streamArgsToPointArgs offset nrep argsrep streamArgs
            pexpr = k args
        point <- eval_point pexpr
        return $ pointExpr point

      streamVal :: StreamVal s ('Stream.Stream n t)
      streamVal = StreamValFunction f

  pure $ Stream
    { streamVal       = streamVal
    , streamTypeRep   = Stream.Stream_t nrep trep
    , streamCTypeInfo = tinfo
    }

eval_memory_stream
  :: forall s n t .
     Point.TypeRep t
  -> NatRep ('S n)
  -> Vec ('S n) (Expr Point.ExprF Pure.Point Pure.F t)
  -> (   Expr (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Pure.F)) (Stream s) (CodeGen s) ('Stream.Stream n t)
      -> Expr (Stream.ExprF (Expr Point.ExprF (Point s) (CodeGen s)) (Expr Point.ExprF Pure.Point Pure.F)) (Stream s) (CodeGen s) ('Stream.Stream 'Z t)
     )
  -> CodeGen s (Stream s ('Stream.Stream ('S n) t))
eval_memory_stream trep nrep initExprs k = do
  -- Storing in stream: always not shared, since we must copy the entire data
  -- structure to the static area.
  tinfo <- type_info NotShared trep
  -- Using the code gen state we can come up with fresh names for the static
  -- data: array, index, and copy
  n :: Natural <- CodeGen $ Trans.lift $ gets $ fromIntegral . Seq.length . cgsStaticStreams

  let !arrayIdentifier = assertValidStringIdentifier ("memory_array_" ++ show n)
      !indexIdentifier = assertValidStringIdentifier ("memory_index_" ++ show n)
      !copyIdentifier  = assertValidStringIdentifier ("memory_copy_"  ++ show n)

  -- Since we require that the "static" parts of the expression unify with
  -- the pure interpreter types, we can actually precompute them using that
  -- interpreter. This means that these expressions will certainly be suitable
  -- for C static array initializers (no function calls, no variable bindings).
  let initPoints :: Vec ('S n) (Pure.Point t)
      !initPoints = vecMap Pure.eval_point_ initExprs

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

  -- NB: if the result is a sum or product, it will have been declared
  -- here in this do block (type_info)
  let arrayInits :: NonEmpty C.CondExpr
      !arrayInits = fmap pureExpr (vecToNonEmpty initPoints)

  -- TODO must create a stream value to run the continuation with, using the
  -- identifiers
  let sval :: StaticStreamVal
      sval = StaticStreamVal
        { ssvIndex  = indexIdentifier
        , ssvArray  = arrayIdentifier
        , ssvSize   = 1 + arrayLength
        , ssvOffset = 0
        }

      stream :: Stream s ('Stream.Stream ('S n) t)
      stream = Stream
        { streamVal       = StreamValStatic sval
        , streamTypeRep   = Stream.Stream_t nrep trep
        , streamCTypeInfo = tinfo
        }

      nrep' :: NatRep n
      nrep' = case nrep of
        S_t n -> n

      -- NB: it's `n`, not `'S n`.
      streamRec :: Stream s ('Stream.Stream n t)
      streamRec = Stream
        { streamVal       = StreamValStatic sval
        , streamTypeRep   = Stream.Stream_t nrep' trep
        , streamCTypeInfo = tinfo
        }

  -- NB: this recursive call may declare more memory streams, updating the
  -- cgsStaticStreams list, but that's OK, it just means the suffix on the
  -- names will not necessarily be consistent with the order in the list.
  sval' <- eval_stream (k (value streamRec))
  nextValueExpr <- streamExprNow (streamVal sval')

  let !sms = StaticMemoryStream
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

      -- This block item updates the stream at the "write index"
      bi = staticMemoryStreamUpdateArrayBlockItem sms (condExprIsAssignExpr nextValueExpr)

  CodeGen $ Trans.lift $ modify' $ \cgs -> cgs
    { cgsStaticStreams = cgsStaticStreams cgs Seq.|> sms
    , cgsBlockItems    = bi : cgsBlockItems cgs
    }

  pure stream


-- | Make a C expression from a pure evaluation of a point (Pilot.Pure).
pureExpr :: Pure.Point t -> C.CondExpr

pureExpr (Pure.UInt8  w8)  = integer_literal auto (Point.UInt8  w8)
pureExpr (Pure.UInt16 w16) = integer_literal auto (Point.UInt16 w16)
pureExpr (Pure.UInt32 w32) = integer_literal auto (Point.UInt32 w32)
pureExpr (Pure.UInt64 w64) = integer_literal auto (Point.UInt64 w64)
pureExpr (Pure.Int8   i8)  = integer_literal auto (Point.Int8   i8)
pureExpr (Pure.Int16  i16) = integer_literal auto (Point.Int16   i16)
pureExpr (Pure.Int32  i32) = integer_literal auto (Point.Int32   i32)
pureExpr (Pure.Int64  i64) = integer_literal auto (Point.Int64   i64)

pureExpr (Pure.Product points) = error "pureExpr TODO"
pureExpr (Pure.Sum points)     = error "pureExpr TODO"

-- | Product intro: give all conjuncts and get the product. Since products are
-- structs, this corresponds to a struct initializer with a field for each
-- conjunct.
--
-- Special case for the empty product introduction, which is simply NULL.
-- TODO there is no way to eliminate an empty product, so we could probably
-- get away with simply erasing an intro of an empty product.
--
eval_intro_product
  :: Point.TypeRep ('Point.Product types)
  -> All (Expr Point.ExprF (Point s) (CodeGen s)) types
  -> CodeGen s (Point s ('Point.Product types))

eval_intro_product trep All        = type_rep_val trep cNULL

eval_intro_product trep@(Point.Product_t (And _tr _trs)) (And t ts) = do
  ctt <- compoundTypeTreatment
  -- This will ensure the composite type is in the code gen state
  typeSpec <- declare_product ctt trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
  initList <- product_field_inits ctt 0 t ts
  let pexpr = C.PostfixInits typeName initList
      expr = case ctt of
        Shared    -> reference (postfixExprIsCondExpr pexpr)
        NotShared -> postfixExprIsCondExpr pexpr
  type_rep_val trep expr

product_field_inits
  :: CompoundTypeTreatment
  -> Natural
  -> Expr Point.ExprF (Point s) (CodeGen s) t
  -> All (Expr Point.ExprF (Point s) (CodeGen s)) ts
  -> CodeGen s C.InitList

product_field_inits ctt n t All = do
  exprVal <- eval_point t
  -- With shared compound type treatment, all compound types which appear in
  -- other compound types are by reference.
  -- TODO think of a way to organize this to be less ad-hoc.
  let expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep exprVal))
          then reference (pointExpr exprVal)
          else pointExpr exprVal
        NotShared -> pointExpr exprVal
      !designator = assertValidDesignator "product_field" (product_field_name n)
  pure $ C.InitBase (Just designator) (C.InitExpr (condExprIsAssignExpr expr))

product_field_inits ctt n t (And t' ts) = do
  exprVal <- eval_point t
  let expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep exprVal))
          then reference (pointExpr exprVal)
          else pointExpr exprVal
        NotShared -> pointExpr exprVal
      !designator = assertValidDesignator "product_field" (product_field_name n)
  subList <- product_field_inits ctt (n+1) t' ts
  pure $ C.InitCons subList (Just designator) (C.InitExpr (condExprIsAssignExpr expr))

-- | Product elimination is just a field accessor.
eval_elim_product
  :: Point.TypeRep ('Point.Product fields)
  -> Point.TypeRep field
  -> Any Point.Selector fields field
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Product fields)
  -> CodeGen s (Point s field)
eval_elim_product trep trepF selector t = do
  ctt <- compoundTypeTreatment
  -- We don't need the type spec itself, but we do need to ensure that it is
  -- declared.
  _typeSpec <- declare_product ctt trep
  point <- eval_point t
  let pexpr = condExprIsPostfixExpr $ dereferenceIf (pointPtr point) (pointExpr point)
  eval_elim_product_with_selector ctt trepF 0 pexpr selector

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
  -> Point.TypeRep variant
  -> Any (Expr Point.ExprF (Point s) (CodeGen s)) variants variant
  -> CodeGen s (Point s ('Point.Sum variants))
-- The meta-language doesn't allow for empty sums to be introduced (void type
-- in the algebraic sense).
eval_intro_sum (Point.Sum_t All) _ it = case it of
  {}

eval_intro_sum trep@(Point.Sum_t (And _ _)) trepV anyt = do
  ctt <- compoundTypeTreatment
  typeSpec <- declare_sum ctt trep
  let typeName = C.TypeName (C.SpecQualType typeSpec Nothing) Nothing
  initList <- sum_field_inits ctt trepV anyt
  let pexpr = C.PostfixInits typeName initList
      expr = case ctt of
        Shared    -> reference (postfixExprIsCondExpr pexpr)
        NotShared -> postfixExprIsCondExpr pexpr
  type_rep_val trep expr

-- | The init list for a sum struct: its tag and its variant.
sum_field_inits
  :: CompoundTypeTreatment
  -> Point.TypeRep variant
  -> Any (Expr Point.ExprF (Point s) (CodeGen s)) variants variant
  -> CodeGen s C.InitList
sum_field_inits ctt trep anyt = do
  let !tagExpr = condExprIsAssignExpr (sum_tag_expr 0 anyt)
  variantInitList <- sum_variant_init_list ctt trep 0 anyt
  pure $ C.InitCons
    (C.InitBase (Just (ident_designator ident_tag)) (C.InitExpr tagExpr))
    (Just (ident_designator ident_variant))
    -- Sad naming convention from the spec: it's not initializing an array, it's
    -- just an array of initializers. It's how we get to give an initializer
    -- without specifying the union type name.
    (C.InitArray variantInitList)

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
  -> Point.TypeRep variant
  -> Natural
  -> Any (Expr Point.ExprF (Point s) (CodeGen s)) variants variant
  -> CodeGen s C.InitList

sum_variant_init_list ctt trep n (Or there) =
  sum_variant_init_list ctt trep (n+1) there

sum_variant_init_list ctt trep n (Any t) = do
  exprVal <- eval_point t 
  -- TODO factor out this little pattern here, it's used also in product
  -- introduction.
  let expr = case ctt of
        Shared    ->
          if isJust (is_compound (pointTypeRep exprVal))
          then reference (pointExpr exprVal)
          else pointExpr exprVal
        NotShared -> pointExpr exprVal
      !designator = assertValidDesignator "sum_variant_init_list" (sum_variant_name n)
      initExpr = C.InitExpr (condExprIsAssignExpr expr)
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
  :: Point.TypeRep ('Point.Sum types)
  -> Point.TypeRep r
  -> Expr Point.ExprF (Point s) (CodeGen s) ('Point.Sum types)
  -> All (Case (Expr Point.ExprF (Point s) (CodeGen s)) r) types
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
  -> All (Case (Expr Point.ExprF (Point s) (CodeGen s)) r) (ty ': tys)
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
-- For composite streams with nonzero prefix, what happens when you drop the
-- bound thing? Do you get a new binder?
declare_initialized_stream :: String -> Stream s t -> CodeGen s (Stream s t)
declare_initialized_stream _ _ = error "declare_initialized_stream not defined"
{-
declare_initialized_stream prefix stream = do
  expr <- streamExprNow (streamVal stream)
  ident <- declare_initialized prefix expr (streamCTypeInfo stream)
  pure $ 
-}

-- | Make a declaration assigning the given value to a new identifier.
-- The declaration appears in the CodeGen state, and the resulting C identifier
-- may be used to refer to it.
declare_initialized
  :: String
  -> C.CondExpr
  -> CTypeInfo
  -> CodeGen s C.Ident
declare_initialized prefix cexpr tinfo = do
  ident <- fresh_binder prefix
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
  ident <- fresh_binder prefix
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

-- | How should compound types be represented: with sharing or without sharing.
--
-- With sharing, compound types are always taken by pointer. This can mean less
-- copying and less stack use, but cannot be used outside of the scope in which
-- they are created, so are not always appropriate.
--
-- Any compound type's representation is either _wholly_ in the not-shared form
-- or the shared form: the not-shared form cannot contain, anywhere within it,
-- a shared form of another compound type, and vice-versa.
data CompoundTypeTreatment where
  -- | A composite type should be duplicated fully if it appears in another
  -- composite type.
  NotShared :: CompoundTypeTreatment
  -- | A composite type should appear as a (const restrict) pointer in another
  -- composite type.
  Shared    :: CompoundTypeTreatment

deriving instance Eq CompoundTypeTreatment
deriving instance Ord CompoundTypeTreatment

oppositeTreatment :: CompoundTypeTreatment -> CompoundTypeTreatment
oppositeTreatment NotShared = Shared
oppositeTreatment Shared    = NotShared

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

data CodeGenOptions = CodeGenOptions
  { -- | Set to True to do the "composite-reference" optimization. This means
    -- that whenever possible, composite types (sums and products) will be
    -- referenced by const restrict pointer, to allow for sharing.
    cgoCompoundTypeTreatment :: !CompoundTypeTreatment
  }

compoundTypeTreatment :: CodeGen s CompoundTypeTreatment
compoundTypeTreatment = CodeGen $ Trans.lift $ gets
  (cgoCompoundTypeTreatment . cgsOptions)

-- | Run a code gen with a given compound type treatment.
--
-- Must use with care to ensure that a compound type in shared form never
-- appears inside another compound type in not-shared form, or vice-versa.
withCompoundTypeTreatment :: CompoundTypeTreatment -> CodeGen s t -> CodeGen s t
withCompoundTypeTreatment ctt cg = do
  origCtt <- compoundTypeTreatment
  CodeGen $ Trans.lift $ modify $ \st ->
    st { cgsOptions = (cgsOptions st) { cgoCompoundTypeTreatment = ctt } }
  t <- cg
  CodeGen $ Trans.lift $ modify $ \st ->
    st { cgsOptions = (cgsOptions st) { cgoCompoundTypeTreatment = origCtt } }
  pure t

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
  { cgsOptions :: !CodeGenOptions
  , -- | Type declarations in reverse order. This comprises enum, union, and
    -- struct declarations induced by compound types encountered during code
    -- generation.
    cgsTypeDeclns :: ![C.Decln]
    -- | Extern object and function declarations, keyed on the string which
    -- determines their C identifiers, so that the generated C will not have
    -- duplicate names.
  , cgsExterns    :: !(Map ExternIdentifier ExternDeclr)
    -- | Information determining declarations and statements which implement
    -- static streams with memory.
  , cgsStaticStreams :: !(Seq StaticMemoryStream)
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
  , cgsProducts   :: !(Map CompoundTypeIdentifier CompoundTypeDeclr)
    -- | Sum types encountered.
  , cgsSums       :: !(Map CompoundTypeIdentifier CompoundTypeDeclr)
  }

--
-- TODO what we need is
-- - Top-level declaration of static arrays and their indices.
-- - Statements which do the update:
--   - For all memory streams, write the update to its "copy" location
--   - For all memory streams, write the "copy" location to its static
--     array at the current index
-- The two phase update with copy thing ensures we don't have to worry
-- about ordering of updates.
--
-- Also for externs, may be good practice to copy them all over at the
-- start of eval, to be _really_ sure they will be consistent, in case we
-- somehow were running on an SMP system.
-- No, no sense worrying about it. There's always going to be ways to do it
-- wrong (passing pointers, for instance). Let's just say the programmer must
-- ensure that these externs are only updated in strong ordering w.r.t. to the
-- eval function.
--
-- But there's still the matter of conversion (also relevant to output) to/from
-- whatever types the C shell uses.
--
-- Form of the main function:
--
--   1. Put in the block items which compute the triggers
--   2. For each memory stream, compute its next value and assign it to its
--      copy location.
--   3. For each memory stream, bump its index modulo its size and copy its
--      copy location to this index.

-- | This contains all of the information needed in order to generate
-- - Static declarations of the stream
-- - The statements to update the stream (i.e. mutate those static declarations)
data StaticMemoryStream = StaticMemoryStream
  { -- | Identifier of the static array
    smsArrayIdent :: !C.Ident
    -- | Identifier of the static current index into the array
  , smsIndexIdent :: !C.Ident
    -- | Integer constant giving the size of the array (shall be at least 2).
  , smsCSize      :: !C.IntConst
    -- | Integer constant giving one less than smsCSize. Add this to the
    -- current offset, modulo smsCSize, gives the "write" cell.
  , smsWriteOffset :: !C.IntConst
    -- | How many bits do we need for the index?
    -- In practice it's unlikely there would ever be a memory stream of size
    -- greater than even 255 but still it's good to know this.
  , smsSizeWidth  :: !Point.SomeWidthRep
    -- | The initial values for the array. Must be exactly as many as the size.
    -- This is in reverse order: earlier entries will go later in the array.
  , smsArrayInits :: !(NonEmpty C.CondExpr)
    -- | The C type information for the _points_ in this stream.
  , smsCTypeInfo  :: !CTypeInfo
  }

-- | Make an array initializer with these values, in reverse order.
staticMemoryArrayInits :: NonEmpty C.CondExpr -> C.InitList
staticMemoryArrayInits (cexpr NE.:| []) = C.InitBase
  Nothing
  (C.InitExpr (C.AssignCond cexpr))
staticMemoryArrayInits (cexpr NE.:| (cexpr' : cexprs)) = C.InitCons
  (staticMemoryArrayInits (cexpr NE.:| cexprs))
  Nothing
  (C.InitExpr (C.AssignCond cexpr))

staticMemoryStreamDeclns :: StaticMemoryStream -> [C.Decln]
staticMemoryStreamDeclns sms =
  [ staticMemoryStreamIndexDecln sms
  , staticMemoryStreamArrayDecln sms
  ]

-- | Block items to update the current indices of all static memory streams.
-- This must be done at the end of every evaluation frame.
staticMemoryStreamBlockItems :: Seq StaticMemoryStream -> [C.BlockItem]
staticMemoryStreamBlockItems smss =
  fmap staticMemoryStreamUpdateIndexBlockItem lst
  where
  lst = toList smss

-- | Increments the stream's index, modulo the size of the C array.
staticMemoryStreamUpdateIndexBlockItem :: StaticMemoryStream -> C.BlockItem
staticMemoryStreamUpdateIndexBlockItem sms = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $
  C.ExprAssign $ C.Assign
    (identIsUnaryExpr (smsIndexIdent sms))
    C.AEq
    (multExprIsAssignExpr (C.MultMod incrementedIndex modulus))
  where
  incrementedIndex :: C.MultExpr
  incrementedIndex = addExprIsMultExpr $ C.AddPlus
    (identIsAddExpr (smsIndexIdent sms))
    (constIsMultExpr (C.ConstInt (C.IntHex (hex_const 1) Nothing)))
  modulus :: C.CastExpr
  modulus = constIsCastExpr (C.ConstInt (smsCSize sms))

-- | The "write" portion of a memory stream. The "write index" is the current
-- index plus the size of the prefix (i.e. 1 less than the size of the C
-- array) modulo the size of the C array. Could also think of it as the cell
-- "behind" the current index in the sense of a circular array.
staticMemoryStreamUpdateArrayBlockItem
  :: StaticMemoryStream
  -> C.AssignExpr
  -> C.BlockItem
staticMemoryStreamUpdateArrayBlockItem sms expr = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $
  C.ExprAssign $ C.Assign
    (postfixExprIsUnaryExpr arrayAtIndex)
    C.AEq
    expr
  where
  arrayAtIndex :: C.PostfixExpr
  arrayAtIndex = C.PostfixIndex
    (identIsPostfixExpr (smsArrayIdent sms))
    (multExprIsExpr moduloExpr)
  moduloExpr :: C.MultExpr
  moduloExpr = C.MultMod (addExprIsMultExpr sumExpr) modulusExpr
  sumExpr :: C.AddExpr
  sumExpr = C.AddPlus
    (identIsAddExpr (smsIndexIdent sms))
    (constIsMultExpr (C.ConstInt (smsWriteOffset sms)))
  modulusExpr :: C.CastExpr
  modulusExpr = constIsCastExpr (C.ConstInt (smsCSize sms))


-- | Declaration of the static memory area for the array of values for this
-- memory stream.
staticMemoryStreamArrayDecln :: StaticMemoryStream -> C.Decln
staticMemoryStreamArrayDecln sms = C.Decln specs (Just initDeclrList)
  where
  specs = C.DeclnSpecsStorage C.SStatic $ Just $ C.DeclnSpecsType typeSpec Nothing
  typeSpec = ctypeSpec (smsCTypeInfo sms)
  initDeclrList :: C.InitDeclrList
  initDeclrList = C.InitDeclrBase $ C.InitDeclrInitr
    (C.Declr mPtr $ C.DirectDeclrArray1 identDeclr Nothing (Just sizeExpr))
    (C.InitArray (staticMemoryArrayInits (smsArrayInits sms)))
  identDeclr :: C.DirectDeclr
  identDeclr = C.DirectDeclrIdent (smsArrayIdent sms)
  sizeExpr :: C.AssignExpr
  sizeExpr = constIsAssignExpr (C.ConstInt (smsCSize sms))
  mPtr :: Maybe C.Ptr
  mPtr = if ctypePtr (smsCTypeInfo sms)
         then Just (C.PtrBase Nothing)
         else Nothing

-- | Declaration of the "current index" memory location for this stream.
staticMemoryStreamIndexDecln :: StaticMemoryStream -> C.Decln
staticMemoryStreamIndexDecln sms = C.Decln specs (Just initDeclrList)
  where
  -- The spec of the index is always
  --   static uint<N>_t <name> = 0x00
  -- where N depends upon how big the array is.
  specs = C.DeclnSpecsStorage C.SStatic $ Just $ C.DeclnSpecsType typeSpec Nothing
  typeSpec = C.TTypedef $ C.TypedefName $ case smsSizeWidth sms of
    Point.SomeWidthRep Point.Eight_t     -> ident_uint8_t
    Point.SomeWidthRep Point.Sixteen_t   -> ident_uint16_t
    Point.SomeWidthRep Point.ThirtyTwo_t -> ident_uint32_t
    Point.SomeWidthRep Point.SixtyFour_t -> ident_uint64_t
  initDeclrList :: C.InitDeclrList
  initDeclrList = C.InitDeclrBase $ C.InitDeclrInitr
    (C.Declr Nothing (C.DirectDeclrIdent (smsIndexIdent sms)))
    (C.InitExpr (constIsAssignExpr (C.ConstInt (C.IntHex (hex_const 0) Nothing))))


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
  extDeclns = externs ++ staticMemDeclns ++ extTypeDeclns

  staticMemDeclns :: [C.ExtDecln]
  staticMemDeclns = fmap C.ExtDecln $
    concatMap staticMemoryStreamDeclns (toList (cgsStaticStreams cgs))

  externs :: [C.ExtDecln]
  externs = fmap (C.ExtDecln . externDecln) (Map.elems (cgsExterns cgs))

  extTypeDeclns :: [C.ExtDecln]
  extTypeDeclns = fmap C.ExtDecln (cgsTypeDeclns cgs)

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

-- | The Haskell TypeRep of a composite type's fields determines its C
-- representation(s).
type CompoundTypeIdentifier = Point.SomeTypeRep

-- | How is a compound type used in the program? Determines which type
-- declarations we need.
data CompoundTypeUsage where
  UsedShared    :: CompoundTypeUsage
  UsedNotShared :: CompoundTypeUsage
  UsedBoth      :: CompoundTypeUsage

-- | Information about the C types representing a compound type.
data CompoundTypeDeclr where
  -- | Shared and not-shared types are the same.
  SimpleCompoundType
    :: !C.TypeSpec
    -> CompoundTypeDeclr
  -- | Shared and not-shared types are different.
  ComplexCompoundType
    :: !String     -- ^ Root name for types representing this thing.
    -> !C.TypeSpec -- ^ Of the non-shared representation
    -> !C.TypeSpec -- ^ Of the shared representation
    -> !CompoundTypeUsage
    -> CompoundTypeDeclr

data NonEmptyFields where
  NonEmptyFields :: All Point.TypeRep (ty ': tys) -> NonEmptyFields

type ExternIdentifier = String

extern :: String -> Point.TypeRep t -> CodeGen s (Stream s ('Stream.Stream 'Z t))
extern name trep = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExterns
  when exists $ codeGenError $ CodeGenInternalError ("extern name already exists " ++ name)
  tinfo <- type_info NotShared trep
  let typeSpec = ctypeSpec tinfo
      mPtr = if ctypePtr tinfo then Just (C.PtrBase Nothing) else Nothing
      -- Prefix with "extern_" so that it's impossible to clash with names
      -- that we choose internally for other things.
      ident = assertValidStringIdentifier ("extern_" ++ name)
      !externDeclr = ExternObjectDeclr
        Nothing
        typeSpec
        mPtr
        ident
      !cexpr = identIsCondExpr ident
      stream = Stream
        { streamVal       = StreamValConstant cexpr
        , streamTypeRep   = Stream.Stream_t Z_t trep
        , streamCTypeInfo = tinfo
        }
  CodeGen $ Trans.lift $ modify' $ \cgs ->
    cgs { cgsExterns = Map.insert name externDeclr (cgsExterns cgs) }
  pure stream

data ExternDeclr where
  ExternObjectDeclr
    :: !(Maybe C.TypeQualList)
    -> !C.TypeSpec
    -> !(Maybe C.Ptr)
    -> !C.Ident
    -> ExternDeclr
  ExternFunctionDeclr
    :: !(Maybe C.TypeQualList)
    -> !C.TypeSpec
    -> !(Maybe C.Ptr)
    -> !C.Ident
    -> ![FunctionParam]
    -> ExternDeclr

data FunctionParam = FunctionParam
  { fpTypeQual :: !(Maybe C.TypeQualList)
  , fpTypeSpec :: !C.TypeSpec
  , fpPtr      :: !(Maybe C.Ptr)
  , fpIdent    :: !C.Ident
  }

-- | The top-level declaration for an external thing.
externDecln :: ExternDeclr -> C.Decln

externDecln (ExternObjectDeclr mtq ts mPtr ident) = C.Decln
  (externDeclnSpecs mtq ts)
  (Just $ C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr $ C.DirectDeclrIdent ident)

externDecln (ExternFunctionDeclr mtq ts mPtr ident fparams) = C.Decln
  (externDeclnSpecs mtq ts)
  (Just $ C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr $ C.DirectDeclrFun1 dident ptl)
  where
  dident :: C.DirectDeclr
  dident = C.DirectDeclrIdent ident
  ptl :: C.ParamTypeList
  ptl = C.ParamTypeList pl
  pl :: C.ParamList
  pl = case fparams of
    []       -> C.ParamBase $ C.ParamDeclnAbstract (C.DeclnSpecsType C.TVoid Nothing) Nothing
    (fp:fps) -> functionParams (NE.reverse (fp NE.:| fps))

functionParams :: NonEmpty FunctionParam -> C.ParamList
functionParams (fp NE.:| []) = C.ParamBase $ C.ParamDecln
  (functionParamDeclnSpecs fp)
  (C.Declr (fpPtr fp) (C.DirectDeclrIdent (fpIdent fp)))
functionParams (fp NE.:| (fp' : fps)) = C.ParamCons
  (functionParams (fp' NE.:| fps))
  (C.ParamDecln (functionParamDeclnSpecs fp) (C.Declr (fpPtr fp) (C.DirectDeclrIdent (fpIdent fp))))

functionParamDeclnSpecs :: FunctionParam -> C.DeclnSpecs
functionParamDeclnSpecs fp = declnSpecsQualListMaybe (fpTypeQual fp)
  (C.DeclnSpecsType (fpTypeSpec fp) Nothing)

externDeclnSpecs :: Maybe C.TypeQualList -> C.TypeSpec -> C.DeclnSpecs
externDeclnSpecs mtq ts = C.DeclnSpecsStorage C.SExtern $ Just $
  declnSpecsQualListMaybe mtq (C.DeclnSpecsType ts Nothing)

declnSpecsQualListMaybe :: Maybe C.TypeQualList -> C.DeclnSpecs -> C.DeclnSpecs
declnSpecsQualListMaybe Nothing   ds = ds
declnSpecsQualListMaybe (Just qs) ds = declnSpecsQualList qs ds

-- | Prepend the type qualifier list to a decln specs.
declnSpecsQualList :: C.TypeQualList -> C.DeclnSpecs -> C.DeclnSpecs
declnSpecsQualList (C.TypeQualBase tq)     specs = C.DeclnSpecsQual tq (Just specs)
declnSpecsQualList (C.TypeQualCons tqs tq) specs = declnSpecsQualList tqs (C.DeclnSpecsQual tq (Just specs))

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

evalCodeGen
  :: CodeGenOptions
  -> CodeGen s t
  -> (Either CodeGenError t, CodeGenState)
evalCodeGen opts cgm = runIdentity (runStateT (runExceptT (runCodeGen cgm)) initialState)
  where
  initialState = CodeGenState
    { cgsOptions       = opts
    , cgsTypeDeclns    = []
    , cgsExterns       = mempty
    , cgsStaticStreams = mempty
    , cgsBlockItems    = []
    , cgsScope         = scope_init NE.:| []
    , cgsProducts      = mempty
    , cgsSums          = mempty
    }

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
  -> CodeGen s (Stream s ('Stream.Stream n x))
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
  st <- CodeGen $ Trans.lift $ get
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
        roundtrip trepP exprP trepF any = Field trepF $ PointTarget $ do
          val' <- withCompoundTypeTreatment ctt' $ runPointTarget $
            eval_elim_product trepP trepF any exprP
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
        roundtrip trepS trepV variant = Case trepV $ \it -> PointTarget $ do
          val <- runPointTarget it
          val' <- convertTreatment ctt ctt' val
          withCompoundTypeTreatment ctt' $ runPointTarget $
            eval_intro_sum trepS trepV variant (PointTarget (pure val'))

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

codeGenToFile
  :: String
  -> CodeGenOptions
  -> CodeGen s (Stream s ('Stream.Stream n x))
  -> IO ()
codeGenToFile fp opts cg = case genTransUnit opts cg of
  Left  err       -> throwIO (userError (show err))
  Right transUnit -> writeFile fp $ includes ++ prettyPrint transUnit
  where
  includes = mconcat
    [ "#include <stdint.h>\n"
    , "#include <stdio.h>\n"
    , "\n"
    ]

write_point_expr
  :: (Point.KnownType t)
  => String
  -> Bool
  -> Expr Point.ExprF (Point s) (CodeGen s) t -> IO ()
write_point_expr fp b expr = write_stream_expr fp b (Stream.constant auto Z_t expr)

write_stream_expr
  :: String
  -> Bool
  -> StreamExpr s ('Stream.Stream n x)
  -> IO ()
write_stream_expr fp b expr = codeGenToFile fp opts (eval_stream expr)
  where
  opts = CodeGenOptions { cgoCompoundTypeTreatment = if b then Shared else NotShared }

codeGenError :: CodeGenError -> CodeGen s x
codeGenError err = CodeGen (throwE err)

maybeError :: CodeGenError -> CodeGen s (Maybe x) -> CodeGen s x
maybeError err act = do
  x <- act
  maybe (codeGenError err) pure x

-- |
-- = Utilities for C99 AST manipulation

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

symbolIdentifier :: forall name . KnownSymbol name => Proxy name -> Maybe C.Ident
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
