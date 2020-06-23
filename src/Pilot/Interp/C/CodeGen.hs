{-|
Module      : Pilot.Interp.C.CodeGen
Description : Definition of the CodeGen type and relevant others.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Pilot.Interp.C.CodeGen
  ( StreamExpr
  , StreamExprF

  , Point (..)
  , pointPtr
  , pointTypeSpec
  , Stream (..)
  , streamPtr
  , streamTypeSpec
  , StreamVal (..)
  , StaticStreamVal (..)
  , staticStreamAtOffset
  , streamExprAtOffset
  , streamExprNow
  , streamArgsToPointArgs

  , CodeGen (..)
  , evalCodeGen
  , codeGenTransUnit

  , CodeGenState (..)

  , CodeGenError (..)
  , codeGenError
  , maybeError

  , CodeGenOptions (..)

  , ExternDeclr (..)
  , FunctionParam (..)

  , StaticMemoryStream (..)

  , CompoundTypeTreatment (..)
  , oppositeTreatment
  , compoundTypeTreatment
  , withCompoundTypeTreatment

  , CompoundTypeUsage (..)
  , CompoundTypeDeclr (..)
  , NonEmptyFields (..)

  , Scope (..)
  , scopeInit
  , scopeNew
  , scopeNext
  , freshBinder

  , withNewScope
  , addBlockItem
  , blockItemList
  , blockItemListNE
  , staticMemoryStreamBlockItems
  , staticMemoryStreamUpdateArrayBlockItem

  , prettyPrint

  , CTypeInfo (..)
  ) where

import qualified Data.Kind as Haskell (Type)

import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity (Identity (..))

import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)

import qualified Language.C99.AST as C
import Language.C99.Pretty (Pretty, pretty)
import Text.PrettyPrint (render)

import Numeric.Natural (Natural)

import Pilot.EDSL.Expr
import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Fun
import Pilot.Types.Logic
import Pilot.Types.Nat

import qualified Pilot.Interp.Pure as Pure (Point)
import Pilot.Interp.C.AST

-- | We can only run stream expressions which unify with this.
-- NB: the "static" part must unify with the "pure" interpreter types. These
-- points can be and are precomputed at code generation time.
type StreamExpr s = Expr
  (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point))
  (Stream s)

type StreamExprF s = Stream.ExprF
  (Expr Point.ExprF (Point s))
  (Expr Point.ExprF Pure.Point)
  (StreamExpr s)

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

-- | Representation of a stream of points (values in the streamwise EDSL over
-- the pointwise EDSL).
data Stream s (t :: Stream.Type Point.Type) = Stream
  { streamVal       :: !(StreamVal s t)
  , streamTypeRep   :: !(Stream.TypeRep Point.TypeRep t)
  , streamCTypeInfo :: !CTypeInfo
  }

streamPtr :: Stream s t -> Bool
streamPtr = ctypePtr . streamCTypeInfo

streamTypeSpec :: Stream s t -> C.TypeSpec
streamTypeSpec = ctypeSpec . streamCTypeInfo

data StreamVal s (t :: Stream.Type Point.Type) where

  -- | A static stream (used to implement memory streams). It's a C static
  -- array with a static current index value.
  StreamValStatic :: !StaticStreamVal -> StreamVal s ('Stream.Stream n t)

  -- | Each of the n prefix values in the stream.
  -- The vector is length at least one because even streams with no prefix have
  -- their current value.
  StreamValNonStatic
    :: !(Vec ('S n) (CodeGen s C.CondExpr))
    -> StreamVal s ('Stream.Stream n t)

nonStaticStreamAtOffset
  :: Offset n
  -> Vec ('S n) (CodeGen s C.CondExpr)
  -> CodeGen s C.CondExpr
nonStaticStreamAtOffset Current       (VCons c _)              = c
nonStaticStreamAtOffset (Next offset) (VCons _ vs@(VCons _ _)) =
  nonStaticStreamAtOffset offset vs

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

streamExprAtOffset
  :: Offset n
  -> StreamVal s ('Stream.Stream n t)
  -> CodeGen s C.CondExpr
streamExprAtOffset off (StreamValStatic ssv)   = pure $ staticStreamAtOffset (offsetToNatural off) ssv
streamExprAtOffset off (StreamValNonStatic cs) = nonStaticStreamAtOffset off cs

streamExprNow :: StreamVal s ('Stream.Stream n t) -> CodeGen s C.CondExpr
streamExprNow = streamExprAtOffset Current

streamArgToPointArg
  :: Offset n
  -> NatRep n
  -> Stream s ('Stream.Stream n t)
  -> CodeGen s (Expr Point.ExprF (Point s) t)
streamArgToPointArg offset nrep stream = do
  expr <- streamExprAtOffset offset (streamVal stream)
  pure $ Pilot.EDSL.Expr.value $ Point
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
  -> CodeGen s (Args (Expr Point.ExprF (Point s)) args)
streamArgsToPointArgs offset nrep Args              Args           = pure Args
streamArgsToPointArgs offset nrep (Arg rep argsrep) (Arg arg args) = do
  a  <- streamArgToPointArg   offset nrep arg
  as <- streamArgsToPointArgs offset nrep argsrep args
  pure $ Arg a as

-- | A monad to ease the expression of code generation, which carries some
-- state and may exit early with error cases.
--
-- The `s` parameter is the `ST` trick: 'Point' and 'Stream' also have it, so
-- it would be possible to prevent these from escaping.
newtype CodeGen (s :: Haskell.Type) (t :: Haskell.Type) = CodeGen
  { runCodeGen :: ExceptT CodeGenError (StateT CodeGenState Identity) t }

deriving instance Functor (CodeGen s)
deriving instance Applicative (CodeGen s)
deriving instance Monad (CodeGen s)

evalCodeGen
  :: CodeGenOptions
  -> CodeGen s t
  -> (Either CodeGenError t, CodeGenState)
evalCodeGen opts cgm = runIdentity (runStateT (runExceptT (runCodeGen cgm)) initialState)
  where
  initialState = CodeGenState
    { cgsOptions       = opts
    , cgsTypeDeclns    = []
    , cgsExternInputs  = mempty
    , cgsExternOutputs = mempty
    , cgsStaticStreams = mempty
    , cgsBlockItems    = []
    , cgsScope         = scopeInit NE.:| []
    , cgsProducts      = mempty
    , cgsSums          = mempty
    }

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
    -- | Extern input declarations, keyed on the string which determines their
    -- C identifiers.
  , cgsExternInputs :: !(Map ExternIdentifier ExternDeclr)
    -- | Extern output declarations, keyed on the string which determines their
    -- C identifiers.
  , cgsExternOutputs :: !(Map ExternIdentifier ExternDeclr)
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

data CodeGenError where
  -- | Indicates a bug in this program.
  CodeGenInternalError :: String -> CodeGenError
  CodeGenDuplicateExternName :: String -> CodeGenError
  CodeGenInvalidExternName   :: String -> CodeGenError

deriving instance Show CodeGenError

codeGenError :: CodeGenError -> CodeGen s x
codeGenError err = CodeGen (throwE err)

maybeError :: CodeGenError -> CodeGen s (Maybe x) -> CodeGen s x
maybeError err act = do
  x <- act
  maybe (codeGenError err) pure x

type ExternIdentifier = String

-- | TODO FIXME this is actually a misnomer. These do not always define C
-- externs. They correspond to top-level declarations which may either be
-- extern (an input which the C shell would define and set) or static (an
-- output which the C shell would declare as extern and read).
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
externDecln :: IOClass -> ExternDeclr -> C.Decln

externDecln ioClass (ExternObjectDeclr mtq ts mPtr ident) = C.Decln
  (externDeclnSpecs ioClass mtq ts)
  (Just $ C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr $ C.DirectDeclrIdent ident)

externDecln ioClass (ExternFunctionDeclr mtq ts mPtr ident fparams) = C.Decln
  (externDeclnSpecs ioClass mtq ts)
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

data IOClass where
  IOInputExtern  :: IOClass
  IOOutputStatic :: IOClass

externDeclnSpecs
  :: IOClass
  -> Maybe C.TypeQualList
  -> C.TypeSpec
  -> C.DeclnSpecs
externDeclnSpecs ioClass mtq ts = C.DeclnSpecsStorage storageClass $ Just $
  declnSpecsQualListMaybe mtq (C.DeclnSpecsType ts Nothing)
  where
  storageClass = case ioClass of
    IOInputExtern  -> C.SExtern
    IOOutputStatic -> C.SStatic

declnSpecsQualListMaybe :: Maybe C.TypeQualList -> C.DeclnSpecs -> C.DeclnSpecs
declnSpecsQualListMaybe Nothing   ds = ds
declnSpecsQualListMaybe (Just qs) ds = declnSpecsQualList qs ds

-- | Prepend the type qualifier list to a decln specs.
declnSpecsQualList :: C.TypeQualList -> C.DeclnSpecs -> C.DeclnSpecs
declnSpecsQualList (C.TypeQualBase tq)     specs = C.DeclnSpecsQual tq (Just specs)
declnSpecsQualList (C.TypeQualCons tqs tq) specs = declnSpecsQualList tqs (C.DeclnSpecsQual tq (Just specs))

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
  (staticMemoryArrayInits (cexpr' NE.:| cexprs))
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

data CodeGenOptions = CodeGenOptions
  { -- | Set to True to do the "composite-reference" optimization. This means
    -- that whenever possible, composite types (sums and products) will be
    -- referenced by const restrict pointer, to allow for sharing.
    cgoCompoundTypeTreatment :: !CompoundTypeTreatment
  }

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

scopeInit :: Scope
scopeInit = Scope { scopeMajor = 0, scopeMinor = 0 }

scopeNew :: Scope -> Scope
scopeNew s = s { scopeMajor = scopeMajor s + 1, scopeMinor = 0 }

scopeNext :: Scope -> ((Natural, Natural), Scope)
scopeNext s = ((scopeMajor s, scopeMinor s), s { scopeMinor = scopeMinor s + 1 })

freshBinder :: String -> CodeGen s C.Ident
freshBinder prefix = do
  st <- CodeGen $ Trans.lift get
  let scope NE.:| scopes = cgsScope st
      ((major, minor), scope') = scopeNext scope
      st' = st { cgsScope = scope' NE.:| scopes }
      bindName = prefix ++ "_" ++ show major ++ "_" ++ show minor
  ident <- maybeError
    (CodeGenInternalError $ "fresh_binder invalid " ++ show bindName)
    (pure (stringIdentifier bindName))
  CodeGen $ Trans.lift $ put st'
  pure ident

-- | Run a CodeGen in a fresh scope, giving back all of the generated block
-- items. This allows you to create a new scope using a compound statement.
withNewScope :: CodeGen s t -> CodeGen s (t, [C.BlockItem])
withNewScope cg = CodeGen $ do
  st <- Trans.lift get
  let scopes = cgsScope st
      scope' = scopeNew (NE.head scopes)
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

-- | The C translation unit for a CodeGenState. This is the type declarations,
--
-- Must give a function definition which serves as the "main" function for
-- this CodeGen. This ensures we always have at least one declaration and
-- therefore do indeed get a translation unit.
--
-- TODO make a header, too.
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
  externs =
       fmap (C.ExtDecln . externDecln IOOutputStatic) (Map.elems (cgsExternOutputs cgs))
    ++ fmap (C.ExtDecln . externDecln IOInputExtern)  (Map.elems (cgsExternInputs cgs))

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

-- | Useful for debugging: C AST types, including the translation unit, have
-- Pretty instances.
prettyPrint :: Pretty a => a -> String
prettyPrint = render . pretty
