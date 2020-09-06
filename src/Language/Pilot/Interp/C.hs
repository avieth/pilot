{-|
Module      : Language.Pilot.Interp.C
Description : 
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Pilot.Interp.C where

import Control.Monad (forM_)
import qualified Control.Monad as Monad (join)
import Control.Monad.Trans.State.Strict (StateT (..))
import qualified Control.Monad.Trans.State.Strict as State
import Control.Monad.Trans.Except (ExceptT, runExceptT)
import qualified Control.Monad.Trans.Except as Except
import qualified Control.Monad.Trans.Class as Trans (lift)
import qualified Data.Foldable as Foldable (toList)
import Data.Functor.Compose
import Data.Functor.Identity
import qualified Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import qualified Data.Ord (Down (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Numeric.Natural (Natural)

import Language.Pilot.Meta (Obj, type (:->), type (:*), pattern Obj, pattern (:->), pattern (:*))
import qualified Language.Pilot.Meta as Meta
import Language.Pilot.Object (Constant, Varying, Program, pattern Constant, pattern Varying, pattern Program)
import qualified Language.Pilot.Object as Object
import qualified Language.Pilot.Object.Point as Object.Point
import qualified Language.Pilot.Repr as Repr
import Language.Pilot.Types

import Language.Pilot.Interp.C.Util as C
import qualified Language.C99 as C

import Language.C99.Pretty (Pretty, pretty)
import Text.PrettyPrint (render)

import qualified System.IO as IO

instance Repr.Interprets Object.Form ValueM Value where
  interp = interpC

-- Useful for debugging/playing around, but will also be used for codegen,
-- though it's less than ideal....
prettyPrintC :: Pretty a => a -> String
prettyPrintC = render . pretty

-- | Make the translation unit and write it to a file.
--
-- FIXME TODO this also throws down some includes, but that's just because I
-- haven't gotten around to doing this in a better way.
elaborateProgramAndWrite
  :: forall n t .
     String -- ^ Program name
  -> IO.FilePath
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Varying n t))))
  -> IO (Either ProgramError ())
elaborateProgramAndWrite progName fileName repr = case elaborateProgram progName repr of
  Left err -> pure (Left err)
  Right tu -> IO.writeFile fileName (includes ++ prettyPrintC tu) >> pure (Right ())
  where
  includes = mconcat
    [ "#include <stddef.h>\n"
    , "#include <stdint.h>\n"
    , "\n"
    ]

-- | Elaborate a program to a C translation unit. This is:
--
-- - [\] Type declarations for every compound type needed
-- - [x] Extern I/O declarations
-- - [ ] Marshalling functions for the user-facing types for I/O
-- - [x] An "init" function to initialize all static streams (for knots)
-- - [x] A "step" function which updates all static streams and does extern I/O
--
-- TODO every unmarked box above. Make a header translation unit as well.
--
-- NB: the first (earliest) element of the varying is returned.
elaborateProgram
  :: forall n t .
     String -- ^ Name of the program; used to prefix some C names.
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Varying n t))))
  -> Either ProgramError C.TransUnit
elaborateProgram name repr = case result of
  Left  err -> Left err
  Right val -> case mkTransUnit name pstate val of
    Left err' -> Left err'
    Right it  -> Right it

  where

  -- Bindings made in the ValueM outside the ProgramM must be passed along
  -- through to the ProgramM.
  -- Maybe there's a better way to express this.
  (v, pureState) = runValueM (Repr.getRepr repr)

  -- TODO it may be better to change the representation of the Program value
  -- to have
  --
  --   ProgramM (Repr.Val VlaueM Value t)
  --
  -- so that we wouldn't have to do valueMInProgramM here, which seems weird.
  progM :: ProgramM (Value (Varying n t))
  progM = do
    repr <- valueProgramRepr (Repr.fromObject v)
    valueMInProgramM (Repr.fromObject <$> Repr.getRepr repr)

  (result, pstate) = runProgramM progM pureState

-- |
--
-- TODO should give a header and a main. Header should only include explicitly
-- declared user-facing types (from externInput and externOutput). The main
-- function will use generated marshalling functions from/to these.
-- The header should also have all of these externs.
--
mkTransUnit
  :: forall n t .
     String -- ^ Program name. Will prefix certain names.
  -> ProgramState
  -> Value (Varying n t)
  -> Either ProgramError C.TransUnit
mkTransUnit progName pstate v = case mProgNameIdent of
  Nothing -> Left $ InvalidProgramName progName
  Just _  -> Right $
    declns
    `appendTransUnitL`
    (appendTransUnit initFun stepFun)

  where

  mProgNameIdent = stringIdentifier progName

  (identStep, identInit) = let Just progNameIdent = mProgNameIdent in
    ( C.append_ident progNameIdent (assertValidStringIdentifier "_step")
    , C.append_ident progNameIdent (assertValidStringIdentifier "_init")
    )

  Varying nrep trep = valueType v

  varyingExpr :: LocalM C.Expr
  VCons varyingExpr _ = valueVaryingExprs v

  inhabited = varyingValueIsInhabited v
  tyName = valueVaryingTypeName v

  declns :: Maybe C.TransUnit
  declns =
    transUnitFromDeclns typeDeclns
    `C.appendTransUnitLR`
    transUnitFromDeclns externDeclns
    `C.appendTransUnitLR`
    transUnitFromDeclns knotDeclns

  -- Type declarations

  pureState :: PureState
  pureState = program_state_pure_state pstate

  typeDeclns :: [C.Decln]
  typeDeclns = concatMap (NE.toList . ctrep_declns) sortedCompositeTypeReps

  -- Here we sort the composite type declarations by serial number _descending_
  -- because transUnitFromDeclns reverses the order, so that they will appear
  -- ultimately in ascending order.
  sortedCompositeTypeReps :: [CompositeTypeRep]
  sortedCompositeTypeReps = Data.List.sortOn
    (Data.Ord.Down . ctrep_serial_number)
    (Map.elems (pure_state_composite_types pureState))

  -- Extern IO declarations

  externIOs :: [ExternIO]
  externIOs = Map.elems (impure_state_extern_io (program_state_impure_state pstate))

  externDeclns :: [C.Decln]
  externDeclns = concatMap externIOStaticDeclns externIOs

  copyExternInputs, copyExternOutputs :: [LocalM ()]
  copyExternInputs = mapMaybe externIOCopyInput externIOs
  copyExternOutputs = mapMaybe externIOCopyOutput externIOs

  -- Static array (for knots) declarations

  deferredKnots :: [DeferredKnot]
  deferredKnots = Foldable.toList (impure_state_knots (program_state_impure_state pstate))

  knotDeclns :: [C.Decln]
  knotDeclns = concatMap deferredKnotStaticDeclarations deferredKnots

  initFun :: C.TransUnit
  initFun = C.TransUnitBase $ C.ExtFun $ initFunDef

  stepFun :: C.TransUnit
  stepFun = C.TransUnitBase $ C.ExtFun $ stepFunDef

  -- TODO this comes from the deferred knots in the program state.
  initFunDef :: C.FunDef
  initFunDef = elaborateToFunction identInit void initLocal

  void :: C.TypeName
  void = C.TypeName (C.SpecQualType C.TVoid Nothing) Nothing

  initLocal :: LocalM (Maybe C.Expr)
  initLocal = do
    forM_ deferredKnots deferredKnotInits
    pure Nothing

  -- The step function returns the computed Varying value, but it also does
  -- all of the other stuff required for I/O and memory streams. See
  -- `varyingExprWithUpdates`
  stepFunDef :: C.FunDef
  stepFunDef = elaborateToFunction identStep tyName (Just <$> varyingExprWithUpdates)

  -- We can use the LocalM monad to include the I/O and memory stream stuff.
  --
  -- The do notation should make things fairly clear. Inline comments hopefully
  -- give some explanation as to why it's done this way.
  varyingExprWithUpdates :: LocalM C.Expr
  varyingExprWithUpdates = do
    -- To make the step function re-entrant, we want to copy all extern inputs
    -- to local (non extern) locations.
    sequence copyExternInputs
    -- The static arrays used to implement knots are updated as soon as
    -- possible. Why? Because this way, _every_ location in the array is valid
    -- when the rest of the program runs. That's to say, if you give a
    -- single-element initializer to this stream, then there are always 2
    -- values available: the current frame, and the previous frame.
    --
    -- TODO it's possible there's some problem with this that I don't see.
    updateStaticArrays
    -- Now the program can be elaborated to get the return value, but we
    -- must assign it, because it may use values that are about to be updated.
    cexpr <- varyingExpr
    retIdent <- makeBinding trep inhabited tyName cexpr
    -- Copy outputs to their extern locations.
    sequence copyExternOutputs
    -- The static array indices must advance now, so that on the next frame
    -- the streams will have appeared to have moved forward.
    updateStaticArrayIndices
    pure $ C.identIsExpr retIdent

  -- | Updates the arrays as well as their indices.
  updateStaticArrays :: LocalM ()
  updateStaticArrays = forM_ deferredKnots deferredKnotArrayUpdates

  updateStaticArrayIndices :: LocalM ()
  updateStaticArrayIndices = forM_ deferredKnots deferredKnotIndexUpdates


newtype Gen = Gen { unGen :: Integer }

genInteger :: Gen -> (Integer, Gen)
genInteger gen =
  let i  = unGen gen
      !j = i + 1
  in  (i, Gen j)

-- | Use a Gen within some state transition function.
genValue
  :: (s -> Gen) -> (Gen -> s -> s)
  -> (Integer -> r)
  -> s
  -> (r, s)
genValue get set k s =
  let (i, gen') = genInteger (get s)
      r = k i
      s' = set gen' s
  in  (r, s')

type NameGen = Gen

genFreshName :: LocalM C.Ident
genFreshName = LocalM $ do
  st <- State.get
  let (name, !st') = genValue local_state_name_gen (\x s -> s { local_state_name_gen = x }) mkBinderName st
      !ident = assertValidStringIdentifier name
  State.put st'
  pure ident

mkBinderName :: Integer -> String
mkBinderName = (++) "local_" . show

type CompositeTypeIdGen = Gen

-- | For naming of composite types, and for sorting their declarations to
-- give an acceptable order for a C compiler.
newtype CompositeTypeId = CompositeTypeId { getCompositeTypeId :: Integer }

deriving instance Eq CompositeTypeId
deriving instance Ord CompositeTypeId

genCompositeTypeId :: ValueM CompositeTypeId
genCompositeTypeId = ValueM $ do
  st <- State.get
  let (typeId, !st') = genValue pure_state_type_id_gen (\x s -> s { pure_state_type_id_gen = x }) mkCompositeTypeId st
  State.put st'
  pure typeId

mkCompositeTypeId :: Integer -> CompositeTypeId
mkCompositeTypeId = CompositeTypeId


-- | Information about composite types to be held in the ValueM state monad's
-- PureState. It will be keyed in a map on SomeTypeRep. Ensures that proper
-- products and sums, which are represented using C compound datatypes (structs,
-- enums, unions) can get unique names, and that their declarations can be
-- put into the translation unit when the entire ValueM is run.
data CompositeTypeRep = CompositeTypeRep
  { ctrep_declns        :: !(NonEmpty C.Decln)
    -- | Useful to have when writing out the C declarations, because if they
    -- are put out in the order of this serial number ascending, then the C
    -- compiler will accept them.
  , ctrep_serial_number :: !CompositeTypeId
  }


-- | The callback is run when the type rep is not already known.
-- Only call this with the type rep of a _normalized_ type.
--
-- TODO could make that more clear by taking a NormalizedType parameter?
withCompositeTypeId
  :: Object.Point.SomeTypeRep
  -> (CompositeTypeId -> ValueM (NonEmpty C.Decln))
  -> ValueM CompositeTypeId
withCompositeTypeId strep k = do
  mIt <- ValueM $ State.gets (Map.lookup strep . pure_state_composite_types)
  case mIt of
    Just it -> pure $ ctrep_serial_number it
    Nothing -> do
      serialNumber <- genCompositeTypeId
      declns <- k serialNumber
      let !ctrep = CompositeTypeRep
            { ctrep_declns        = declns
            , ctrep_serial_number = serialNumber
            }
      ValueM $ State.modify' $ \st -> st
        { pure_state_composite_types = Map.insert strep ctrep (pure_state_composite_types st) }
      pure serialNumber


type BinderIdGen = Gen

-- | Identifies a let-binding "globally" in an EDSL expression, i.e. "over"
-- multiple 'LocalM' values. It's valid within the context of a 'ValueM', and
-- is used to make the 'LocalM' used in a let-binding idempotent.
newtype BinderId = BinderId { getBinderId :: Integer }

deriving instance Eq BinderId
deriving instance Ord BinderId

genBinderId :: ValueM BinderId
genBinderId = ValueM $ do
  st <- State.get
  let (binderId, !st') = genValue pure_state_binder_id_gen (\x s -> s { pure_state_binder_id_gen = x }) mkBinderId st
  State.put st'
  pure binderId

mkBinderId :: Integer -> BinderId
mkBinderId = BinderId

-- | Represents a let-binding: this identifier is bound to this expression.
-- Used in 'LocalState', in conjunction with the 'BinderId', which are delivered
-- by 'ValueM'/'PureState'.
data Binding where
  Binding :: !C.Ident -> !C.Expr -> Binding

-- | This is a part of the interpretation of a let binding.
--
-- The 'ValueM' contexts provides a new unique binding identifier. It gives a
-- 'LocalM' which checks its 'local_state_binders' for that 'BinderId'. If it's
-- there, then nothing else happens: the constant value cached there is
-- returned. But if it's not there, then it's at this point where the parameter
-- 'LocalM' is run, elaborating all of the C block items it needs, and then
-- the result is cached in the 'local_state_binders'.
makeIdempotent
  :: Object.Point.TypeRep t
  -> Inhabited t
  -> LocalM C.Expr
  -> ValueM (Value (Constant t))
makeIdempotent trep inhabited lm = do
  binderId <- genBinderId
  tyName <- typeName inhabited (Constant trep)
  pure $ constantValue (Obj (Constant trep)) inhabited tyName $ LocalM $ do
    lst <- State.get
    case Map.lookup binderId (local_state_binders lst) of
      Just (Binding ident expr) -> pure (C.identIsExpr ident)
      Nothing -> do
        -- Here, the parameter's bindings are all elaborated.
        cexpr <- unLocalM lm
        -- It's important to get the state again.
        lst <- State.get
        let binders = local_state_binders lst
        case Map.lookup binderId binders of
          Just _  -> error "bug: binder id taken"
          Nothing -> do
            ident <- unLocalM $ makeBinding trep inhabited tyName cexpr
            -- Even though makeBinding has added the block item, we must also
            -- update the BinderId map.
            unLocalM $ addBinding binderId ident cexpr
            pure $ C.identIsExpr ident

-- | Makes an identifier for the binding and adds the block item to do the
-- assignment. The binding is const.
makeBinding :: Object.Point.TypeRep t -> Inhabited t -> C.TypeName -> C.Expr -> LocalM C.Ident
makeBinding trep inhabited tyName cexpr = do
  ident <- genFreshName
  let !bm = C.blockItemInitialize tyName ident cexpr
  addBlockItem bm
  pure ident

data LocalState = LocalState
  {
    local_state_binders      :: !(Map BinderId Binding)
    -- The C BlockItemList type is used since it's already a tail-append list
    -- structure anyway.
  , local_state_block_items  :: !(Maybe C.BlockItemList)
  , local_state_name_gen     :: !NameGen
  }

initialLocalState :: LocalState
initialLocalState = LocalState
  { local_state_binders     = Map.empty
  , local_state_block_items = Nothing
  , local_state_name_gen    = Gen 0
  }

-- | `LocalM C.Expr` is the representation of constants. A vector of these is
-- the representation of varyings.
newtype LocalM t = LocalM
  { unLocalM :: StateT LocalState Identity t }

deriving instance Functor LocalM
deriving instance Applicative LocalM
deriving instance Monad LocalM

addBinding :: BinderId -> C.Ident -> C.Expr -> LocalM ()
addBinding bid ident expr = LocalM $ State.modify $ \ls ->
  let !binding = Binding ident expr
      binders = local_state_binders ls
      binders' = case Map.lookup bid binders of
        Just _  -> error "bug: duplicate binder id"
        Nothing -> Map.insert bid binding binders
      !ls' = ls { local_state_binders = binders' }
  in  ls'

addBlockItem :: C.BlockItem -> LocalM ()
addBlockItem bm = LocalM $ State.modify $ \ls ->
  let !bms = case local_state_block_items ls of
        Nothing  -> Just (C.BlockItemBase bm)
        Just bms -> Just (C.BlockItemCons bms bm)
      !ls' = ls { local_state_block_items = bms }
  in  ls'

-- | Runs the LocalM with an empty binding context, creating a C function
-- definition which takes no arguments and returns the given value's C
-- representation.
elaborateConstantToFunction :: C.TypeName -> C.Ident -> Value (Constant t) -> C.FunDef
elaborateConstantToFunction tyName funName v = elaborateToFunction funName tyName (Just <$> lm)
  where
  lm = valueConstantExpr v

elaborateVaryingToFunction :: C.TypeName -> C.Ident -> Value (Varying Z t) -> C.FunDef
elaborateVaryingToFunction tyName funName v = elaborateToFunction funName tyName (Just <$> lm)
  where
  VCons lm VNil = valueVaryingExprs v

-- | Make a function with a given C.Ident, returning a given C.TypeName.
-- If the LocalM gives Nothing, then there is no return statement, so your
-- TypeName should be void.
elaborateToFunction :: C.Ident -> C.TypeName -> LocalM (Maybe C.Expr) -> C.FunDef
elaborateToFunction funName tyName lm = C.FunDef declnSpecs declr args cstmt

  where

  cstmt :: C.CompoundStmt
  cstmt = C.Compound $ C.appendBlockItemListLR bms retVal

  (mCexpr, bms) = elaborateLocalM lm

  retVal :: Maybe C.BlockItemList
  retVal = flip fmap mCexpr $ \cexpr -> C.BlockItemBase $
    C.BlockItemStmt $ C.StmtJump $ C.JumpReturn (Just cexpr)

  declnSpecs :: C.DeclnSpecs
  declnSpecs = specQualListToDeclnSpecs specQualList

  declr :: C.Declr
  declr = C.Declr (mAbstractDeclrToPtr mAbsDeclr) $ C.DirectDeclrFun2
    (C.DirectDeclrIdent funName)
    Nothing

  args :: Maybe C.DeclnList
  args = Nothing

  C.TypeName specQualList mAbsDeclr = tyName

-- | Runs the LocalM with an empty context, producing a C expression and all
-- of the block items required in order to give it meaning.
elaborateLocalM :: LocalM t -> (t, Maybe C.BlockItemList)
elaborateLocalM lm = (t, bms)
  where
  (t, st) = runIdentity (runStateT (unLocalM lm) initialLocalState)
  bms = local_state_block_items st


data Of :: (k -> k -> Hask) -> k -> Hask where
  Of :: f k x -> Of f k


-- | Opposite of 'normalizedTypeRep'.
typeRepFromNormalized
  :: NormalizedType a b
  -> Object.Point.TypeRep b
  -> Object.Point.TypeRep a

typeRepFromNormalized IntegerIsNormal trep = trep
typeRepFromNormalized BytesIsNormal   trep = trep

typeRepFromNormalized (NormalizedProduct nonUnits normP) trep =
  typeRepFromNormalizedProduct nonUnits normP trep

typeRepFromNormalized (NormalizedSum nonVoids normS) trep =
  typeRepFromNormalizedSum nonVoids normS trep


typeRepFromNormalizedProduct
  :: NonUnitFields fields nonUnits
  -> NormalizedProduct nonUnits norm
  -> Object.Point.TypeRep norm
  -> Object.Point.TypeRep ('Object.Point.Product_t fields)

typeRepFromNormalizedProduct nonUnits UnitIsNormal _ =
  Object.Point.Product_r (typeRepFromNormalizedProductUnit nonUnits)

typeRepFromNormalizedProduct nonUnits NormalizedProductSingleton trep =
  Object.Point.Product_r (typeRepFromNormalizedProductSingleton nonUnits trep)

typeRepFromNormalizedProduct nonUnits NormalizedProductProper (Object.Point.Product_r treps) =
  Object.Point.Product_r (typeRepFromNormalizedProductProper nonUnits treps)


typeRepFromNormalizedProductUnit
  :: NonUnitFields fields '[]
  -> All Object.Point.TypeRep fields
typeRepFromNormalizedProductUnit NonUnitNil = All
typeRepFromNormalizedProductUnit (NonUnitAbsorb nty isUnit rec) = case isUnit of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.unit_t)
    (typeRepFromNormalizedProductUnit rec)


typeRepFromNormalizedProductSingleton
  :: NonUnitFields fields '[nonUnit]
  -> Object.Point.TypeRep nonUnit
  -> All Object.Point.TypeRep fields
typeRepFromNormalizedProductSingleton (NonUnitAbsorb nty isUnit rec) trep = case isUnit of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.unit_t)
    (typeRepFromNormalizedProductSingleton rec trep)
typeRepFromNormalizedProductSingleton (NonUnitCons nty _ rec) trep =
  And (typeRepFromNormalized nty trep)
      (typeRepFromNormalizedProductUnit rec)


typeRepFromNormalizedProductProper
  :: NonUnitFields fields tys
  -> All Object.Point.TypeRep tys
  -> All Object.Point.TypeRep fields
typeRepFromNormalizedProductProper NonUnitNil All = All
typeRepFromNormalizedProductProper (NonUnitAbsorb nty isUnit rec) treps = case isUnit of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.unit_t)
    (typeRepFromNormalizedProductProper rec treps)
typeRepFromNormalizedProductProper (NonUnitCons nty _ rec) (And trep treps) =
  And (typeRepFromNormalized nty trep)
      (typeRepFromNormalizedProductProper rec treps)


typeRepFromNormalizedSum
  :: NonVoidVariants variants nonVoids
  -> NormalizedSum nonVoids norm
  -> Object.Point.TypeRep norm
  -> Object.Point.TypeRep ('Object.Point.Sum_t variants)

typeRepFromNormalizedSum nonVoids VoidIsNormal _ =
  Object.Point.Sum_r (typeRepFromNormalizedSumVoid nonVoids)

typeRepFromNormalizedSum nonVoids NormalizedSumSingleton trep =
  Object.Point.Sum_r (typeRepFromNormalizedSumSingleton nonVoids trep)

typeRepFromNormalizedSum nonVoids NormalizedSumProper (Object.Point.Sum_r treps) =
  Object.Point.Sum_r (typeRepFromNormalizedSumProper nonVoids treps)


typeRepFromNormalizedSumVoid
  :: NonVoidVariants variants '[]
  -> All Object.Point.TypeRep variants
typeRepFromNormalizedSumVoid NonVoidNil = All
typeRepFromNormalizedSumVoid (NonVoidAbsorb nty isVoid rec) = case isVoid of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.void_t)
    (typeRepFromNormalizedSumVoid rec)


typeRepFromNormalizedSumSingleton
  :: NonVoidVariants variants '[nonVoid]
  -> Object.Point.TypeRep nonVoid
  -> All Object.Point.TypeRep variants
typeRepFromNormalizedSumSingleton (NonVoidAbsorb nty isVoid rec) trep = case isVoid of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.void_t)
    (typeRepFromNormalizedSumSingleton rec trep)
typeRepFromNormalizedSumSingleton (NonVoidCons nty _ rec) trep =
  And (typeRepFromNormalized nty trep)
      (typeRepFromNormalizedSumVoid rec)


typeRepFromNormalizedSumProper
  :: NonVoidVariants variants tys
  -> All Object.Point.TypeRep tys
  -> All Object.Point.TypeRep variants
typeRepFromNormalizedSumProper NonVoidNil All = All
typeRepFromNormalizedSumProper (NonVoidAbsorb nty isVoid rec) treps = case isVoid of
  Refl -> And
    (typeRepFromNormalized nty Object.Point.void_t)
    (typeRepFromNormalizedSumProper rec treps)
typeRepFromNormalizedSumProper (NonVoidCons nty _ rec) (And trep treps) =
  And (typeRepFromNormalized nty trep)
      (typeRepFromNormalizedSumProper rec treps)


normalizedTypeRep
  :: NormalizedType t n
  -> Object.Point.TypeRep t
  -> Object.Point.TypeRep n

normalizedTypeRep IntegerIsNormal (Object.Point.Integer_r s w) = Object.Point.Integer_r s w

normalizedTypeRep BytesIsNormal (Object.Point.Bytes_r w) = Object.Point.Bytes_r w

normalizedTypeRep (NormalizedProduct nonUnits norm) (Object.Point.Product_r fields) =
  normalizedProductTypeRep fields nonUnits norm

normalizedTypeRep (NormalizedSum nonVoids norm) (Object.Point.Sum_r variants) =
  normalizedSumTypeRep variants nonVoids norm


-- TODO rewrite in the style of normalizedSumTypeRep, which matches primarily
-- on the NormalizedSum value, and seems to be better organized.
normalizedProductTypeRep
  :: All Object.Point.TypeRep fields
  -> NonUnitFields fields nonUnits
  -> NormalizedProduct nonUnits norm
  -> Object.Point.TypeRep norm

normalizedProductTypeRep All NonUnitNil UnitIsNormal = Object.Point.unit_t

normalizedProductTypeRep (And _ _) _ UnitIsNormal = Object.Point.unit_t

normalizedProductTypeRep (And ty _) (NonUnitCons nty _ _) NormalizedProductSingleton =
  normalizedTypeRep nty ty

normalizedProductTypeRep (And _ tys) (NonUnitAbsorb _ _ rec) NormalizedProductSingleton =
  normalizedProductTypeRep tys rec NormalizedProductSingleton

normalizedProductTypeRep (And _ tys) (NonUnitAbsorb _ _ rec) NormalizedProductProper =
  normalizedProductTypeRep tys rec NormalizedProductProper

normalizedProductTypeRep
    (And ty (And _ tys))
    (NonUnitCons nty notUnit (NonUnitAbsorb _ _ rec))
    NormalizedProductProper =
  normalizedProductTypeRep (And ty tys) (NonUnitCons nty notUnit rec) NormalizedProductProper

normalizedProductTypeRep (And _ All) (NonUnitCons _ _ rec) NormalizedProductProper =
  case rec of {}

normalizedProductTypeRep
    (And ty (And ty' (And _ ands)))
    (NonUnitCons nty notUnit (NonUnitCons nty' notUnit' (NonUnitAbsorb _ _ rec)))
    NormalizedProductProper =
  normalizedProductTypeRep
    (And ty (And ty' ands))
    (NonUnitCons nty notUnit (NonUnitCons nty' notUnit' rec))
    NormalizedProductProper

normalizedProductTypeRep
    (And ty (And ty' All))
    (NonUnitCons nty _ (NonUnitCons nty' _ NonUnitNil))
    NormalizedProductProper =
  Object.Point.Product_r
    (And (normalizedTypeRep nty  ty)
    (And (normalizedTypeRep nty' ty')
    All))

normalizedProductTypeRep
    (And ty and@(And _ (And _ _)))
    (NonUnitCons nty _ rec@(NonUnitCons _ _ (NonUnitCons _ _ _)))
    NormalizedProductProper =
  case normalizedProductTypeRep and rec NormalizedProductProper of
    Object.Point.Product_r ands -> Object.Point.Product_r $
      And (normalizedTypeRep nty ty) ands


normalizedSumTypeRep
  :: All Object.Point.TypeRep variants
  -> NonVoidVariants variants nonVoids
  -> NormalizedSum nonVoids norm
  -> Object.Point.TypeRep norm

normalizedSumTypeRep _ _ VoidIsNormal = Object.Point.void_t

normalizedSumTypeRep all nonVoids NormalizedSumSingleton = case all of
  All -> case nonVoids of {}
  And ty all' -> case nonVoids of
    NonVoidAbsorb _ _ rec -> normalizedSumTypeRep all' rec NormalizedSumSingleton
    NonVoidCons nty _ _ -> normalizedTypeRep nty ty

normalizedSumTypeRep all nonVoids NormalizedSumProper = case all of
  All -> case nonVoids of {}
  And ty all' -> case nonVoids of

    NonVoidAbsorb _ _ rec -> normalizedSumTypeRep all' rec NormalizedSumProper

    NonVoidCons nty _ (NonVoidCons nty' _ NonVoidNil) -> case all' of
      And ty' All -> Object.Point.Sum_r
        (And (normalizedTypeRep nty ty)
        (And (normalizedTypeRep nty' ty')
        All))

    NonVoidCons nty _ rec@(NonVoidCons _ _ (NonVoidCons _ _ _)) ->
      case normalizedSumTypeRep all' rec NormalizedSumProper of
        Object.Point.Sum_r ands -> Object.Point.Sum_r $
          And (normalizedTypeRep nty ty) ands

    NonVoidCons nty notVoid (NonVoidCons nty' notVoid' (NonVoidAbsorb _ _ rec)) ->
      case all' of
        And ty' (And _ all'') -> normalizedSumTypeRep
          (And ty (And ty' all''))
          (NonVoidCons nty notVoid (NonVoidCons nty' notVoid' rec))
          NormalizedSumProper

    NonVoidCons nty notVoid (NonVoidAbsorb _ _ rec) -> case all' of
      And _ all'' -> normalizedSumTypeRep
        (And ty all'')
        (NonVoidCons nty notVoid rec)
        NormalizedSumProper


-- | Every point type can be normalized. This will be useful for defining sum
-- and product intro and elim interpretations, such that their C representations
-- are sparse.
--
-- NB: there is a normalized type even for uninhabited types. A product
-- containing a void, for example, will normalize to a product which still
-- contains that void.
normalizedType :: Object.Point.TypeRep t -> NormalizedType `Of` t

normalizedType (Object.Point.Integer_r _ _) = Of IntegerIsNormal
normalizedType (Object.Point.Bytes_r     _) = Of BytesIsNormal

normalizedType (Object.Point.Product_r fields) = normalizedProduct normFields
  where
  normFields = forAll normalizedType fields

normalizedType (Object.Point.Sum_r variants) = normalizedSum normVariants
  where
  normVariants = forAll normalizedType variants


-- | Given normalized types of the fields, construct the normalized type of
-- the product of those fields.
normalizedProduct
  :: All (Of NormalizedType) fields
  -> NormalizedType `Of` ('Object.Point.Product_t fields)

normalizedProduct All = Of $ NormalizedProduct NonUnitNil UnitIsNormal

normalizedProduct (And (Of nty) ntys) = case (isUnit, rest) of

  -- Rest of it reduce to unit, next type is not unit, so it's a singleton.
  (No isNotUnit, Of (NormalizedProduct nonUnits UnitIsNormal)) -> Of $ NormalizedProduct
    (NonUnitCons nty isNotUnit nonUnits)
    NormalizedProductSingleton

  -- Rest of it reduces to a singleton, next type is not unit, so it's a proper
  -- product.
  (No isNotUnit, Of (NormalizedProduct nonUnits NormalizedProductSingleton)) -> Of $ NormalizedProduct
    (NonUnitCons nty isNotUnit nonUnits)
    NormalizedProductProper

  -- Rest of it reduces to a proper product, next type is not unit, so it
  -- remains a proper product, but longer.
  (No isNotUnit, Of (NormalizedProduct nonUnits NormalizedProductProper)) -> Of $ NormalizedProduct
    (NonUnitCons nty isNotUnit nonUnits)
    NormalizedProductProper

  -- Rest of it is unit, next type is unit, so it remains unit overall.
  (Yes isIndeedUnit, Of (NormalizedProduct nonUnits UnitIsNormal)) -> Of $ NormalizedProduct
    (NonUnitAbsorb nty isIndeedUnit nonUnits)
    UnitIsNormal

  -- Rest of it is a singleton, next type is unit, so it remains a singleton.
  (Yes isIndeedUnit, Of (NormalizedProduct nonUnits NormalizedProductSingleton)) -> Of $ NormalizedProduct
    (NonUnitAbsorb nty isIndeedUnit nonUnits)
    NormalizedProductSingleton

  -- Rest of it is a proper product, next type is unit, so it remains a
  -- proper product.
  (Yes isIndeedUnit, Of (NormalizedProduct nonUnits NormalizedProductProper)) -> Of $ NormalizedProduct
    (NonUnitAbsorb nty isIndeedUnit nonUnits)
    NormalizedProductProper

  where

  rest = normalizedProduct ntys
  isUnit = decideNormalizedTypeIsUnit nty


-- | Given normalized types of the variants, construct the normalized type of
-- the sum of those variants.
normalizedSum
  :: All (Of NormalizedType) variants
  -> NormalizedType `Of` (Object.Point.Sum_t variants)

normalizedSum All = Of $ NormalizedSum NonVoidNil VoidIsNormal

normalizedSum (And (Of nty) ntys) = case (isVoid, rest) of

  -- See normalizedProduct for comments that may or may not be helpful.
  -- This is exactly the same idea: whether the next type is void or not
  -- determines what the normalized sum becomes.

  (No isNotVoid, Of (NormalizedSum nonVoids VoidIsNormal)) -> Of $ NormalizedSum
    (NonVoidCons nty isNotVoid nonVoids)
    NormalizedSumSingleton

  (No isNotVoid, Of (NormalizedSum nonVoids NormalizedSumSingleton)) -> Of $ NormalizedSum
    (NonVoidCons nty isNotVoid nonVoids)
    NormalizedSumProper

  (No isNotVoid, Of (NormalizedSum nonVoids NormalizedSumProper)) -> Of $ NormalizedSum
    (NonVoidCons nty isNotVoid nonVoids)
    NormalizedSumProper

  (Yes isIndeedVoid, Of (NormalizedSum nonVoids VoidIsNormal)) -> Of $ NormalizedSum
    (NonVoidAbsorb nty isIndeedVoid nonVoids)
    VoidIsNormal

  (Yes isIndeedVoid, Of (NormalizedSum nonVoids NormalizedSumSingleton)) -> Of $ NormalizedSum
    (NonVoidAbsorb nty isIndeedVoid nonVoids)
    NormalizedSumSingleton

  (Yes isIndeedVoid, Of (NormalizedSum nonVoids NormalizedSumProper)) -> Of $ NormalizedSum
    (NonVoidAbsorb nty isIndeedVoid nonVoids)
    NormalizedSumProper

  where

  rest = normalizedSum ntys
  isVoid = decideNormalizedTypeIsVoid nty


decideNormalizedTypeIsUnit
  :: NormalizedType ty n
  -> Decision (n :~: 'Object.Point.Product_t '[])

decideNormalizedTypeIsUnit IntegerIsNormal = No (\it -> case it of {})
decideNormalizedTypeIsUnit BytesIsNormal   = No (\it -> case it of {})

decideNormalizedTypeIsUnit (NormalizedProduct _ UnitIsNormal) = Yes Refl
decideNormalizedTypeIsUnit (NormalizedProduct (NonUnitCons _ it _) NormalizedProductSingleton) =
  No it
decideNormalizedTypeIsUnit (NormalizedProduct _ NormalizedProductProper) =
  No (\it -> case it of {})
decideNormalizedTypeIsUnit (NormalizedProduct (NonUnitAbsorb _ _ rec) NormalizedProductSingleton) =
  decideNormalizedTypeIsUnit (NormalizedProduct rec NormalizedProductSingleton)

decideNormalizedTypeIsUnit (NormalizedSum _ VoidIsNormal) = No (\it -> case it of {})
decideNormalizedTypeIsUnit (NormalizedSum (NonVoidCons nty _ _) NormalizedSumSingleton) =
  decideNormalizedTypeIsUnit nty
decideNormalizedTypeIsUnit (NormalizedSum (NonVoidCons _ _ _) NormalizedSumProper) =
  No (\it -> case it of {})
decideNormalizedTypeIsUnit (NormalizedSum (NonVoidAbsorb _ _ rec) it) =
  decideNormalizedTypeIsUnit (NormalizedSum rec it)


decideNormalizedTypeIsVoid
  :: NormalizedType ty n
  -> Decision (n :~: 'Object.Point.Sum_t '[])

decideNormalizedTypeIsVoid IntegerIsNormal = No (\it -> case it of {})
decideNormalizedTypeIsVoid BytesIsNormal   = No (\it -> case it of {})

decideNormalizedTypeIsVoid (NormalizedSum _ VoidIsNormal) = Yes Refl
decideNormalizedTypeIsVoid (NormalizedSum (NonVoidCons _ it _) NormalizedSumSingleton) = No it
decideNormalizedTypeIsVoid (NormalizedSum _ NormalizedSumProper) = No (\it -> case it of {})
decideNormalizedTypeIsVoid (NormalizedSum (NonVoidAbsorb _ _ rec) it) =
  decideNormalizedTypeIsVoid (NormalizedSum rec it)

decideNormalizedTypeIsVoid (NormalizedProduct _ UnitIsNormal) = No (\it -> case it of {})
decideNormalizedTypeIsVoid (NormalizedProduct (NonUnitCons nty _ _) NormalizedProductSingleton) =
  decideNormalizedTypeIsVoid nty
decideNormalizedTypeIsVoid (NormalizedProduct (NonUnitCons _ _ _) NormalizedProductProper) =
  No (\it -> case it of {})
decideNormalizedTypeIsVoid (NormalizedProduct (NonUnitAbsorb _ _ rec) it) =
  decideNormalizedTypeIsVoid (NormalizedProduct rec it)


-- | Opposite of 'normalizationPreservesInhabitedness'
inhabitedFromNormalized
  :: NormalizedType a b
  -> Inhabited b
  -> Inhabited a

inhabitedFromNormalized IntegerIsNormal inh = inh
inhabitedFromNormalized BytesIsNormal   inh = inh

inhabitedFromNormalized (NormalizedProduct nonUnits normP) inh =
  inhabitedFromNormalizedProduct nonUnits normP inh

inhabitedFromNormalized (NormalizedSum nonVoids normS) inh =
  inhabitedFromNormalizedSum nonVoids normS inh


inhabitedFromNormalizedProduct
  :: NonUnitFields fields nonUnits
  -> NormalizedProduct nonUnits norm
  -> Inhabited norm
  -> Inhabited ('Object.Point.Product_t fields)

-- If it normalizes to unit, then we know all of its fields normalize to
-- unit, so they're all inhabited (since unit is inhabited).
inhabitedFromNormalizedProduct nonUnitFields UnitIsNormal _ =
  inhabitedFromNormalizedProductUnit nonUnitFields

inhabitedFromNormalizedProduct nonUnitFields NormalizedProductSingleton inhabited =
  inhabitedFromNormalizedProductSingleton nonUnitFields inhabited

inhabitedFromNormalizedProduct nonUnitFields NormalizedProductProper inhabited =
  inhabitedFromNormalizedProductProper nonUnitFields (allInhabitedFields inhabited Refl)


inhabitedFromNormalizedProductUnit
  :: NonUnitFields fields '[]
  -> Inhabited ('Object.Point.Product_t fields)
inhabitedFromNormalizedProductUnit (NonUnitAbsorb nty isUnit rec) = case isUnit of
  -- The product normalizes to unit, so we know therefore that it's inhabited,
  -- because unit is inhabited.
  -- Along with recursion onto the rest of the product (which also normalizes
  -- to unit), that's enough to conclude that the whole product must be
  -- inhabited.
  Refl -> productStillInhabited
    (inhabitedFromNormalized nty unitIsInhabited)
    (inhabitedFromNormalizedProductUnit rec)
inhabitedFromNormalizedProductUnit NonUnitNil = unitIsInhabited


inhabitedFromNormalizedProductSingleton
  :: NonUnitFields fields '[nonUnit]
  -> Inhabited nonUnit
  -> Inhabited ('Object.Point.Product_t fields)
inhabitedFromNormalizedProductSingleton (NonUnitAbsorb nty isUnit rec) inh = case isUnit of
  Refl -> productStillInhabited
    (inhabitedFromNormalized nty unitIsInhabited)
    (inhabitedFromNormalizedProductSingleton rec inh)
inhabitedFromNormalizedProductSingleton (NonUnitCons nty isNotUnit rec) inh =
  productStillInhabited
    (inhabitedFromNormalized nty inh)
    (inhabitedFromNormalizedProductUnit rec)


inhabitedFromNormalizedProductProper
  :: NonUnitFields fields (nonUnit1 ': nonUnit2 ': nonUnits)
  -> All Inhabited (nonUnit1 ': nonUnit2 ': nonUnits)
  -> Inhabited ('Object.Point.Product_t fields)
inhabitedFromNormalizedProductProper (NonUnitAbsorb nty isUnit rec) inhs = case isUnit of
  Refl -> productStillInhabited
    (inhabitedFromNormalized nty unitIsInhabited)
    (inhabitedFromNormalizedProductProper rec inhs)

inhabitedFromNormalizedProductProper (NonUnitCons nty _ rec) inhs = case inhs of

  And inh inhs@(And inh' All) ->
    productStillInhabited
      (inhabitedFromNormalized nty inh)
      (inhabitedFromNormalizedProductSingleton rec inh')

  And inh inhs@(And _ (And _ _)) ->
    productStillInhabited
      (inhabitedFromNormalized nty inh)
      (inhabitedFromNormalizedProductProper rec inhs)


inhabitedFromNormalizedSum
  :: NonVoidVariants variants nonVoids
  -> NormalizedSum nonVoids norm
  -> Inhabited norm
  -> Inhabited ('Object.Point.Sum_t variants)

-- The sum normalized to void, but you have proof that the normalized type
-- is inhabited? Inconceivable!
inhabitedFromNormalizedSum nonVoids VoidIsNormal inhabited =
  notEmptySum inhabited Refl

inhabitedFromNormalizedSum nonVoids NormalizedSumSingleton inhabited =
  inhabitedFromNormalizedSumSingleton nonVoids inhabited

inhabitedFromNormalizedSum nonVoids NormalizedSumProper inhabited =
  inhabitedFromNormalizedSumProper nonVoids (someInhabitedVariant inhabited Refl)


inhabitedFromNormalizedSumSingleton
  :: NonVoidVariants variants '[nonVoid]
  -> Inhabited nonVoid
  -> Inhabited ('Object.Point.Sum_t variants)

inhabitedFromNormalizedSumSingleton (NonVoidAbsorb _ _ rec) inhabited =
  sumStillInhabited (inhabitedFromNormalizedSumSingleton rec inhabited)

inhabitedFromNormalizedSumSingleton (NonVoidCons nty _ _) inhabited =
  sumIsInhabited (Some (inhabitedFromNormalized nty inhabited))


-- | Notice the unexpected type: it's surprisingly easy to prove this one,
-- and the more general type actually makes it easier.
inhabitedFromNormalizedSumProper
  :: NonVoidVariants variants nonVoids
  -> Some Inhabited nonVoids
  -> Inhabited ('Object.Point.Sum_t variants)

inhabitedFromNormalizedSumProper NonVoidNil some = case some of {}

inhabitedFromNormalizedSumProper (NonVoidAbsorb _ _ rec) some =
  sumStillInhabited (inhabitedFromNormalizedSumProper rec some)

inhabitedFromNormalizedSumProper (NonVoidCons nty _ _) (Some inhabited) =
  sumIsInhabited (Some (inhabitedFromNormalized nty inhabited))

inhabitedFromNormalizedSumProper (NonVoidCons _ _ rec) (Or someMore) =
  sumStillInhabited (inhabitedFromNormalizedSumProper rec someMore)




normalizationPreservesInhabitedness
  :: NormalizedType t n
  -> Inhabited t
  -> Inhabited n

normalizationPreservesInhabitedness IntegerIsNormal inh = inh
normalizationPreservesInhabitedness BytesIsNormal   inh = inh

normalizationPreservesInhabitedness (NormalizedProduct a b) inh =
  normalizationPreservesInhabitednessProduct a b (allInhabitedFields inh Refl)

normalizationPreservesInhabitedness (NormalizedSum a b) inh =
  normalizationPreservesInhabitednessSum a b (someInhabitedVariant inh Refl)


normalizationPreservesInhabitednessProduct
  :: NonUnitFields fields nonUnits
  -> NormalizedProduct nonUnits norm
  -> All Inhabited fields
  -> Inhabited norm

normalizationPreservesInhabitednessProduct
    NonUnitNil
    UnitIsNormal
    All =
  unitIsInhabited

normalizationPreservesInhabitednessProduct
    (NonUnitAbsorb nty isIndeedUnit rec)
    nh
    (And _ inh) =
  normalizationPreservesInhabitednessProduct rec nh inh

-- For the remaining cases we have to pattern match twice deep on the
-- NonUnitFields, so that we are able to choose a NormalizedProduct value for
-- recursion.

normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit NonUnitNil)
    NormalizedProductSingleton
    (And inh _) =
  normalizationPreservesInhabitedness nty inh

normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit (NonUnitAbsorb nty' isIndeedUnit rec))
    np
    (And inh (And _ inhs)) =
  normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit rec)
    np
    (And inh inhs)

normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit (NonUnitCons nty' isNotUnit' NonUnitNil))
    NormalizedProductProper
    (And inh (And inh' All)) =
  productIsInhabited
    (And (normalizationPreservesInhabitedness nty inh)
    (And (normalizationPreservesInhabitedness nty' inh')
     All))

normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit (NonUnitCons nty' isNotUnit' (NonUnitAbsorb _ _ rec)))
    NormalizedProductProper
    (And inh (And inh' (And _ inhs))) =
  normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit (NonUnitCons nty' isNotUnit' rec))
    NormalizedProductProper
    (And inh (And inh' inhs))

normalizationPreservesInhabitednessProduct
    (NonUnitCons nty isNotUnit rec@(NonUnitCons nty' isNotUnit' (NonUnitCons _ _ _)))
    NormalizedProductProper
    (And inh inhs@(And _ _)) =
  productStillInhabited
    (normalizationPreservesInhabitedness nty inh)
    (normalizationPreservesInhabitednessProduct rec NormalizedProductProper inhs)


-- | Proves that if at least one of the variants of the non-normalized sum is
-- inhabited, then the normalized sum is inhabited.
normalizationPreservesInhabitednessSum
  :: NonVoidVariants variants nonVoids
  -> NormalizedSum nonVoids norm
  -> Some Inhabited variants
  -> Inhabited norm

-- TODO FIXME there must be a better/shorter way to write this

normalizationPreservesInhabitednessSum
  NonVoidNil
  VoidIsNormal
  it = case it of {}

normalizationPreservesInhabitednessSum
    (NonVoidCons _ _ NonVoidNil)
    NormalizedSumSingleton
    (Or inhs) = case inhs of {}

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid NonVoidNil)
    NormalizedSumSingleton
    (Some inh) =
  normalizationPreservesInhabitedness nty inh

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' _))
    NormalizedSumProper
    (Some inh) =
  sumIsInhabited (Some (normalizationPreservesInhabitedness nty inh))

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' _))
    NormalizedSumProper
    (Or (Some inh)) =
  sumStillInhabited (sumIsInhabited (Some (normalizationPreservesInhabitedness nty' inh)))

normalizationPreservesInhabitednessSum
    (NonVoidCons _ _ (NonVoidCons _ _ NonVoidNil))
    NormalizedSumProper
    (Or (Or it)) = case it of {}

normalizationPreservesInhabitednessSum
    (NonVoidCons _ _ rec@(NonVoidCons _ _ (NonVoidCons _ _ _)))
    NormalizedSumProper
    (Or inhs) =
  sumStillInhabited (normalizationPreservesInhabitednessSum
    rec
    NormalizedSumProper
    inhs)

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' (NonVoidAbsorb _ _ rec)))
    NormalizedSumProper
    (Or (Or (Or (Or inhs)))) =
  normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' rec))
    NormalizedSumProper
    (Or (Or (Or inhs)))

normalizationPreservesInhabitednessSum
    (NonVoidCons _ _ (NonVoidCons _ _ (NonVoidAbsorb nty isIndeedVoid rec)))
    NormalizedSumProper
    (Or (Or (Some inh))) =
  notEmptySum (normalizationPreservesInhabitedness nty inh) isIndeedVoid

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' (NonVoidAbsorb _ _ rec)))
    NormalizedSumProper
    (Or (Or (Or (Some inh)))) =
  normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidCons nty' isNotVoid' rec))
    NormalizedSumProper
    (Or (Or (Some inh)))

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidAbsorb _ _ rec))
    ns
    (Or (Or inhs)) =
  normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid rec)
    ns
    (Or inhs)

normalizationPreservesInhabitednessSum
    (NonVoidCons _ _ (NonVoidAbsorb nty isIndeedVoid _))
    _
    (Or (Some inh)) =
  notEmptySum (normalizationPreservesInhabitedness nty inh) isIndeedVoid

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidAbsorb _ _ _))
    NormalizedSumSingleton
    (Some inh) =
  normalizationPreservesInhabitedness nty inh

normalizationPreservesInhabitednessSum
    (NonVoidCons nty isNotVoid (NonVoidAbsorb _ _ rec))
    NormalizedSumProper
    (Some inh) =
  sumIsInhabited (Some (normalizationPreservesInhabitedness nty inh))

normalizationPreservesInhabitednessSum
    (NonVoidAbsorb nty isIndeedVoid rec)
    ns
    (Some inh) =
  notEmptySum (normalizationPreservesInhabitedness nty inh) isIndeedVoid

normalizationPreservesInhabitednessSum
    (NonVoidAbsorb nty isIndeedVoid rec)
    ns
    (Or inhs) =
  normalizationPreservesInhabitednessSum
    rec
    ns
    inhs


-- | A key proper of type normalization: if we normalize twice, we get the same
-- form.
normalizationIsIdempotent :: NormalizedType a b -> NormalizedType b c -> b :~: c

normalizationIsIdempotent IntegerIsNormal IntegerIsNormal = Refl

normalizationIsIdempotent BytesIsNormal BytesIsNormal = Refl

normalizationIsIdempotent (NormalizedProduct nonUnits normP) norm =
  normalizationIsIdempotentForProduct nonUnits normP norm

normalizationIsIdempotent (NormalizedSum nonVoids normS) norm =
  normalizationIsIdempotentForSum nonVoids normS norm


normalizationIsIdempotentForProduct
  :: NonUnitFields fields nonUnits
  -> NormalizedProduct nonUnits norm
  -> NormalizedType norm norm'
  -> norm :~: norm'

-- When the normalized product is unit, the proof is easy.

normalizationIsIdempotentForProduct
    NonUnitNil
    UnitIsNormal
    (NormalizedProduct NonUnitNil UnitIsNormal) =
  Refl

normalizationIsIdempotentForProduct
    (NonUnitAbsorb _ _ rec)
    UnitIsNormal
    norm' =
  normalizationIsIdempotentForProduct rec UnitIsNormal norm'

-- When the normalized product is a singleton it's also straightforward: find
-- out what the type is and defer to normalizationIsIdempotent on that one.

normalizationIsIdempotentForProduct
    (NonUnitCons nty _ _)
    NormalizedProductSingleton
    norm' =
  normalizationIsIdempotent nty norm'

normalizationIsIdempotentForProduct
    (NonUnitAbsorb _ _ rec)
    NormalizedProductSingleton
    norm' =
  normalizationIsIdempotentForProduct rec NormalizedProductSingleton norm'

-- Now the cases for proper products. Here we know that
--
--   nonUnits ~ (nonUnit1 ': nonUnit2 ': nonUnits)
--   norm ~ Product (nonUnit1 ': nonUnit2 ': nonUnits)
--
-- but that list is in the NonUnitFields relation, and we know that this is
-- idempotent (nonUnitFieldsIsIdempotent) so we can therefore infer that the
-- NormalizedProduct is also NormalizedProductProper and that's it that's all.

normalizationIsIdempotentForProduct
    nonUnits
    NormalizedProductProper
    norm' =
  case norm' of
    NormalizedProduct nonUnits' normP -> case nonUnitFieldsIsIdempotent nonUnits nonUnits' of
      Refl -> case normP of
        NormalizedProductProper -> Refl


-- | If `b` is `a` without the non unit parts, then taking the non unit parts
-- of `b` doesn't change `b`. Seems reasonable.
nonUnitFieldsIsIdempotent
  :: NonUnitFields a b
  -> NonUnitFields b c
  -> b :~: c

nonUnitFieldsIsIdempotent NonUnitNil NonUnitNil = Refl

nonUnitFieldsIsIdempotent (NonUnitAbsorb _ _ rec) x =
  case nonUnitFieldsIsIdempotent rec x of
    Refl -> Refl

nonUnitFieldsIsIdempotent (NonUnitCons nty _ rec) (NonUnitCons nty' _ rec') =
  case normalizationIsIdempotent nty nty' of
    Refl -> case nonUnitFieldsIsIdempotent rec rec' of
      Refl -> Refl

nonUnitFieldsIsIdempotent (NonUnitCons nty isNotUnit _) (NonUnitAbsorb nty' isUnit _) =
  case normalizationIsIdempotent nty nty' of
    Refl -> isNotUnit isUnit


normalizationIsIdempotentForSum
  :: NonVoidVariants variants nonVoids
  -> NormalizedSum nonVoids norm
  -> NormalizedType norm norm'
  -> norm :~: norm'

normalizationIsIdempotentForSum
    NonVoidNil
    VoidIsNormal
    (NormalizedSum NonVoidNil VoidIsNormal) =
  Refl

normalizationIsIdempotentForSum
    (NonVoidAbsorb _ _ rec)
    VoidIsNormal
    norm' =
  normalizationIsIdempotentForSum rec VoidIsNormal norm'

normalizationIsIdempotentForSum
    (NonVoidCons nty _ _)
    NormalizedSumSingleton
    norm' =
  normalizationIsIdempotent nty norm'

normalizationIsIdempotentForSum
    (NonVoidAbsorb _ _ rec)
    NormalizedSumSingleton
    norm' =
  normalizationIsIdempotentForSum rec NormalizedSumSingleton norm'

-- Just as the product case uses NonUnitFields, idempotency for sums is proved
-- by way of idempotency of the NonVoidVariants.

normalizationIsIdempotentForSum
    nonVoids
    NormalizedSumProper
    norm' =
  case norm' of
    NormalizedSum nonVoids' normS -> case nonVoidVariantsIsIdempotent nonVoids nonVoids' of
      Refl -> case normS of
        NormalizedSumProper -> Refl


-- | Same idea as 'nonUnitFieldsIsIdempotent'
nonVoidVariantsIsIdempotent
  :: NonVoidVariants a b
  -> NonVoidVariants b c
  -> b :~: c

nonVoidVariantsIsIdempotent NonVoidNil NonVoidNil = Refl

nonVoidVariantsIsIdempotent (NonVoidAbsorb _ _ rec) x =
  case nonVoidVariantsIsIdempotent rec x of
    Refl -> Refl

nonVoidVariantsIsIdempotent (NonVoidCons nty _ rec) (NonVoidCons nty' _ rec') =
  case normalizationIsIdempotent nty nty' of
    Refl -> case nonVoidVariantsIsIdempotent rec rec' of
      Refl -> Refl

nonVoidVariantsIsIdempotent (NonVoidCons nty isNotVoid _) (NonVoidAbsorb nty' isVoid _) =
  case normalizationIsIdempotent nty nty' of
    Refl -> isNotVoid isVoid


-- | This proves that the NormalizedType relation is a function.
--
uniqueNormalizedType
  :: NormalizedType ty n1
  -> NormalizedType ty n2
  -> n1 :~: n2

uniqueNormalizedType IntegerIsNormal IntegerIsNormal = Refl
uniqueNormalizedType BytesIsNormal   BytesIsNormal   = Refl

uniqueNormalizedType
    (NormalizedProduct nonUnitFields  normProduct)
    (NormalizedProduct nonUnitFields' normProduct') =
  case uniqueNonUnitFields nonUnitFields nonUnitFields' of
    Refl -> uniqueNormalizedProduct normProduct normProduct'

uniqueNormalizedType
    (NormalizedSum nonVoidVariants  normSum)
    (NormalizedSum nonVoidVariants' normSum') =
  case uniqueNonVoidVariants nonVoidVariants nonVoidVariants' of
    Refl -> uniqueNormalizedSum normSum normSum'


uniqueNonUnitFields
  :: NonUnitFields fields nonUnits
  -> NonUnitFields fields nonUnits'
  -> (nonUnits :~: nonUnits')

uniqueNonUnitFields NonUnitNil NonUnitNil = Refl

uniqueNonUnitFields (NonUnitAbsorb _ _ nuFields) (NonUnitAbsorb _ _ nuFields') =
  case uniqueNonUnitFields nuFields nuFields' of Refl -> Refl

uniqueNonUnitFields (NonUnitCons nty _ nuFields) (NonUnitCons nty' _ nuFields') =
  case uniqueNormalizedType nty nty' of
    Refl -> case uniqueNonUnitFields nuFields nuFields' of
      Refl -> Refl

uniqueNonUnitFields (NonUnitCons nty isNotUnit _) (NonUnitAbsorb nty' isUnit _) =
  case uniqueNormalizedType nty nty' of
    Refl -> isNotUnit isUnit

uniqueNonUnitFields (NonUnitAbsorb nty isUnit _) (NonUnitCons nty' isNotUnit _) =
  case uniqueNormalizedType nty nty' of
    Refl -> isNotUnit isUnit


uniqueNonVoidVariants
  :: NonVoidVariants variants nonVoids
  -> NonVoidVariants variants nonVoids'
  -> (nonVoids :~: nonVoids')

uniqueNonVoidVariants NonVoidNil NonVoidNil = Refl

uniqueNonVoidVariants (NonVoidAbsorb _ _ nvVariants) (NonVoidAbsorb _ _ nvVariants') =
  case uniqueNonVoidVariants nvVariants nvVariants' of Refl -> Refl

uniqueNonVoidVariants (NonVoidCons nty _ nvVariants) (NonVoidCons nty' _ nvVariants') =
  case uniqueNormalizedType nty nty' of
    Refl -> case uniqueNonVoidVariants nvVariants nvVariants' of
      Refl -> Refl

uniqueNonVoidVariants (NonVoidCons nty isNotVoid _) (NonVoidAbsorb nty' isVoid _) =
  case uniqueNormalizedType nty nty' of
    Refl -> isNotVoid isVoid

uniqueNonVoidVariants (NonVoidAbsorb nty isVoid _) (NonVoidCons nty' isNotVoid _) =
  case uniqueNormalizedType nty nty' of
    Refl -> isNotVoid isVoid

uniqueNormalizedProduct
  :: NormalizedProduct nonUnits norm
  -> NormalizedProduct nonUnits norm'
  -> norm :~: norm'
uniqueNormalizedProduct UnitIsNormal               UnitIsNormal               = Refl
uniqueNormalizedProduct NormalizedProductSingleton NormalizedProductSingleton = Refl
uniqueNormalizedProduct NormalizedProductProper    NormalizedProductProper    = Refl

uniqueNormalizedSum
  :: NormalizedSum nonVoids norm
  -> NormalizedSum nonVoids norm'
  -> norm :~: norm'
uniqueNormalizedSum VoidIsNormal           VoidIsNormal           = Refl
uniqueNormalizedSum NormalizedSumSingleton NormalizedSumSingleton = Refl
uniqueNormalizedSum NormalizedSumProper    NormalizedSumProper    = Refl

-- | Relates two types, indicating that the second one is the normalization of
-- the first one. It's in fact a function (see 'uniqueNormalizedType'). It's
-- notable that type normalization is defined without using any type families.
data NormalizedType (ty :: Object.Point.Type) (norm :: Object.Point.Type) where

  IntegerIsNormal :: NormalizedType ('Object.Point.Integer_t s w) ('Object.Point.Integer_t s w)
  BytesIsNormal   :: NormalizedType ('Object.Point.Bytes_t     w) ('Object.Point.Bytes_t     w)

  NormalizedProduct
    :: NonUnitFields fields nonUnits
    -> NormalizedProduct nonUnits norm
    -> NormalizedType ('Object.Point.Product_t fields) norm

  NormalizedSum
    :: NonVoidVariants variants nonVoids
    -> NormalizedSum nonVoids norm
    -> NormalizedType ('Object.Point.Sum_t variants) norm

-- | `NonUnitFields fields nonUnits` means that `nonUnits` is the sub-list of
-- `fields` (order-preserved) consisting of all of the `fields` which are not
-- empty products after normalization.
data NonUnitFields (fields :: [Object.Point.Type]) (nonUnits :: [Object.Point.Type]) where
  NonUnitNil :: NonUnitFields '[] '[]
  NonUnitCons
    :: NormalizedType field norm
    -> Not (norm :~: 'Object.Point.Product_t '[])
    -> NonUnitFields           fields            nonUnits
    -> NonUnitFields (field ': fields) (norm ': nonUnits)
  NonUnitAbsorb
    :: NormalizedType field norm
    -> (norm :~: 'Object.Point.Product_t '[])
    -> NonUnitFields           fields  nonUnits
    -> NonUnitFields (field ': fields) nonUnits

-- | Like 'NonUnitFields' but for sums and voids.
data NonVoidVariants (variants :: [Object.Point.Type]) (nonVoids :: [Object.Point.Type]) where
  NonVoidNil :: NonVoidVariants '[] '[]
  NonVoidCons
    :: NormalizedType variant norm
    -> Not (norm :~: 'Object.Point.Sum_t '[])
    -> NonVoidVariants             variants           nonVoids
    -> NonVoidVariants (variant ': variants) (norm ': nonVoids)
  NonVoidAbsorb
    :: NormalizedType variant norm
    -> (norm :~: 'Object.Point.Sum_t '[])
    -> NonVoidVariants             variants  nonVoids
    -> NonVoidVariants (variant ': variants) nonVoids


data NormalizedProduct (nonUnits :: [Object.Point.Type]) (norm :: Object.Point.Type) where

  UnitIsNormal :: NormalizedProduct '[] ('Object.Point.Product_t '[])

  -- | A singleton product is represented by its component type.
  NormalizedProductSingleton :: NormalizedProduct '[nonUnitField] nonUnitField

  -- | 2 or more types which normalize to non-units form a "proper" product.
  NormalizedProductProper :: NormalizedProduct
    (nonUnitField1 ': nonUnitField2 ': nonUnitFields)
    (Object.Point.Product_t (nonUnitField1 ': nonUnitField2 ': nonUnitFields))


data NormalizedSum (variants :: [Object.Point.Type]) (norm :: Object.Point.Type) where

  VoidIsNormal :: NormalizedSum '[] ('Object.Point.Sum_t '[])

  NormalizedSumSingleton :: NormalizedSum '[nonVoidField] nonVoidField

  NormalizedSumProper :: NormalizedSum
    (nonVoidVariant1 ': nonVoidVariant2 ': nonVoidVariants)
    (Object.Point.Sum_t (nonVoidVariant1 ': nonVoidVariant2 ': nonVoidVariants))


-- | This is the state that must accompany a C Expr in order to give it meaning.
-- The expression may make reference to names assumed to be bound in the local
-- scope, and to names assumed to be declared by C type declarations.
-- Values which include sum elimination require switch statements; these are
-- tracked here, as a list of C BlockItems.
data PureState = PureState
  { -- | For non-empty sum and product types, we need enum, union, and struct
    -- declarations, and we need to know the names of these things and of
    -- their constructors.
    --
    -- The C.Ident is needed in order to construct values of these compound
    -- types. The list of C.Declns are those declarations required in the C
    -- sources (enums, structs, unions).
    --
    -- When writing out the declarations, they must be ordered appropriately, so
    -- that the C compiler always has every referenced struct or enum in scope.
    -- Ordering them by the CompositeTypeId ascending will achieve this, for
    -- all types used by one composite type are added to this map before the
    -- composite.
    pure_state_composite_types :: !(Map Object.Point.SomeTypeRep CompositeTypeRep)
  , pure_state_type_id_gen     :: !CompositeTypeIdGen
    -- | A "global" counter to identify let bindings.
    -- It is used to generate `LetBindId`, which are used as keys in the
    -- `LocalM` state.
  , pure_state_binder_id_gen :: !BinderIdGen
  }

initialPureState :: PureState
initialPureState = PureState
  { pure_state_composite_types = Map.empty
  , pure_state_type_id_gen     = Gen 0
  , pure_state_binder_id_gen   = Gen 0
  }

newtype ValueM t = ValueM
  { unValueM :: StateT PureState Identity t }

deriving instance Functor ValueM
deriving instance Applicative ValueM
deriving instance Monad ValueM

runValueM :: ValueM t -> (t, PureState)
runValueM v = runIdentity (runStateT (unValueM v) initialPureState)

runValueM_ :: ValueM t -> t
runValueM_ = fst . runValueM

data ProgramState = ProgramState
  { program_state_pure_state   :: !PureState
  , program_state_impure_state :: !ImpureState
  }

initialProgramState :: PureState -> ProgramState
initialProgramState ps = ProgramState
  { program_state_pure_state = ps
  , program_state_impure_state = initialImpureState
  }

data ProgramError where

  DuplicateExternName :: !String -> ProgramError
  InvalidExternName   :: !String -> ProgramError

  InvalidProgramName :: !String -> ProgramError

deriving instance Show ProgramError

newtype ProgramM t = ProgramM
  { unProgramM :: ExceptT ProgramError (StateT ProgramState Identity) t }

deriving instance Functor ProgramM
deriving instance Applicative ProgramM
deriving instance Monad ProgramM

runProgramM :: ProgramM t -> PureState -> (Either ProgramError t, ProgramState)
runProgramM p ps = runIdentity (runStateT (runExceptT (unProgramM p)) (initialProgramState ps))


newtype ExternId = ExternId { getExternId :: String }

deriving instance Eq ExternId
deriving instance Ord ExternId

data ExternInputData where
  -- | Identifier of the copy of the input (not extern storage).
  ExternInputData :: !C.Ident -> ExternInputData

data ExternOutputData where
  ExternOutputData :: !(LocalM C.Expr) -> ExternOutputData

data ExternIODefn where
  -- | Inputs will be copied to a local name at the start of each step, to
  -- make the function re-rentrant.
  ExternInput  :: !ExternInputData -> ExternIODefn
  -- | Outputs have a LocalM C.Expr that is used to write to the output at
  -- each step.
  ExternOutput :: !ExternOutputData -> ExternIODefn

data ExternIO = forall t . ExternIO
  { extern_io_type  :: !(Object.Point.TypeRep t)
  , extern_io_inhabited :: !(Inhabited t)
  , extern_io_type_name :: !C.TypeName
    -- | Identifier of the extern storage class name.
  , extern_io_ident :: !C.Ident
  , extern_io_defn  :: !ExternIODefn
    -- TODO says what the user-facing type is and how to marshall it to/from
    -- the internal type.
  --, extern_io_meta :: !()
  }

-- | Static declarations required for an `ExternIO`.
externIOStaticDeclns :: ExternIO -> [C.Decln]
externIOStaticDeclns (ExternIO trep inhabited tyName ident defn) = case defn of
  ExternOutput _ -> [externOutputStaticDecln trep inhabited tyName ident]
  ExternInput (ExternInputData i) ->
    let (a, b) = externInputStaticDeclns trep inhabited tyName ident i in [a, b]

-- | For extern outputs, there is just one declaration: an extern of the
-- appropriate type.
externOutputStaticDecln
  :: Object.Point.TypeRep t
  -> Inhabited t
  -> C.TypeName
  -> C.Ident
  -> C.Decln
externOutputStaticDecln trep inhabited tyName ident = C.Decln specs (Just initList)
  where
  specs = C.DeclnSpecsStorage C.SExtern (Just (C.specQualListToDeclnSpecs tySpecs))
  initList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent ident)
  mPtr = C.mAbstractDeclrToPtr mAbsDeclr
  C.TypeName tySpecs mAbsDeclr = tyName

externInputStaticDeclns
  :: Object.Point.TypeRep t
  -> Inhabited t
  -> C.TypeName
  -> C.Ident
  -> C.Ident
  -> (C.Decln, C.Decln)
externInputStaticDeclns trep inhabited tyName ident identCopy = (externDecln, copyDecln)
  where
  externDecln = C.Decln (C.DeclnSpecsStorage C.SExtern (Just specs)) (Just externInitList)
  copyDecln   = C.Decln                                      specs   (Just copyInitList)

  externInitList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent ident)
  copyInitList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent identCopy)

  specs = C.specQualListToDeclnSpecs tySpecs
  mPtr = C.mAbstractDeclrToPtr mAbsDeclr
  C.TypeName tySpecs mAbsDeclr = tyName

-- | Elaborates to the LocalM which copies the extern input to its copy
-- location. Gives Nothing if the ExternIO is an output.
externIOCopyInput :: ExternIO -> Maybe (LocalM ())
externIOCopyInput (ExternIO trep inhabited tyName ident defn) = case defn of
  ExternOutput _ -> Nothing
  ExternInput (ExternInputData identCopy) -> Just $
    let !identExpr = C.identIsExpr ident
        !identCopyExpr = C.identIsExpr identCopy
        !assignExpr = C.ExprAssign $ C.Assign
          (C.exprIsUnaryExpr identCopyExpr)
          C.AEq
          (C.exprIsAssignExpr identExpr)
        !bm = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $ assignExpr
    in  addBlockItem bm

-- | Elaborates to the LocalM which computes and copies the output's value to
-- its extern location. Gives Nothing if it's an input.
externIOCopyOutput :: ExternIO -> Maybe (LocalM ())
externIOCopyOutput (ExternIO trep inhabited tyName ident defn) = case defn of
  ExternInput _ -> Nothing
  ExternOutput (ExternOutputData lm) -> Just $ do
    cexpr <- lm
    let !identExpr = C.identIsExpr ident
        !assignExpr = C.ExprAssign $ C.Assign
          (C.exprIsUnaryExpr identExpr)
          C.AEq
          (C.exprIsAssignExpr cexpr)
        !bm = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $ assignExpr
    addBlockItem bm

externInput
  :: String
  -> Object.Point.TypeRep t
  -> Inhabited t
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Varying Z t))))
externInput name trep inhabited = Repr.object $ programValue vrep $ do

  (ident, identCopy) <- ProgramM $ do
    let fullName = "input_" ++ name
        fullNameCopy = "input_copy_" ++ name
    ident <- assertValidStringIdentifierM (Except.throwE (InvalidExternName name)) fullName
    -- If input_<name> is valid, so is input_copy_<name>
    let !identCopy = assertValidStringIdentifier fullNameCopy
    pure (ident, identCopy)

  tyName <- valueMInProgramM $ typeName inhabited (Constant trep)
  
  let inputData :: ExternInputData
      inputData = ExternInputData identCopy
  
      defn :: ExternIODefn
      defn = ExternInput inputData
  
      externIO = ExternIO
        { extern_io_type  = trep
        , extern_io_inhabited = inhabited
        , extern_io_type_name = tyName
        , extern_io_ident = ident
        , extern_io_defn  = defn
        }

  ProgramM $ do
    st <- Trans.lift State.get
    let is = program_state_impure_state st
        key = ExternId name
    case Map.lookup key (impure_state_extern_io is) of
      Nothing -> pure ()
      Just _  -> Except.throwE (DuplicateExternName name)
    let !is' = is { impure_state_extern_io = Map.insert key externIO (impure_state_extern_io is) }
        !st' = st { program_state_impure_state = is' }
    Trans.lift (State.put st')

  --  The varying value is a single expression, which is just the copy
  --  identifier.
  let vrep = Obj (Varying Z_Rep trep)
      cexpr = identIsExpr identCopy
      value = varyingValue_ vrep inhabited tyName (VCons cexpr VNil)

  pure $ Repr.object value

  where
  vrep = Obj (Varying Z_Rep trep)

externOutput
  :: String
  -> Object.Point.TypeRep t
  -> Repr.Repr ValueM Value (Obj (Varying Z t) :-> Obj (Program Meta.Terminal))
externOutput name trep = Repr.fun $ \stream -> Repr.object $ programValue Meta.terminal_t $ do

  let fullName = "output_" ++ name
  ident <- ProgramM $ assertValidStringIdentifierM (Except.throwE (InvalidExternName name)) fullName

  -- Run the ValueM of the stream here, and store the resulting LocalM in the
  -- state to be elaborated when we generate the translation unit.
  (obj, inhabited, tyName) <- valueMInProgramM $ do
    obj <- Repr.getRepr stream
    let inhabited = varyingValueIsInhabited (Repr.fromObject obj)
    tyName <- typeName inhabited (Constant trep)
    pure (obj, inhabited, tyName)

  let outputData :: ExternOutputData
      outputData = case valueVaryingExprs (Repr.fromObject obj) of
        VCons it VNil -> ExternOutputData it

      defn :: ExternIODefn
      defn = ExternOutput outputData

      externIO = ExternIO
        { extern_io_type  = trep
        , extern_io_inhabited = inhabited
        , extern_io_type_name = tyName
        , extern_io_ident = ident
        , extern_io_defn  = defn
        }

  ProgramM $ do
    st <- Trans.lift State.get
    let is = program_state_impure_state st
        key = ExternId name
    case Map.lookup key (impure_state_extern_io is) of
      Nothing -> pure ()
      Just _  -> Except.throwE (DuplicateExternName name)
    let !is' = is { impure_state_extern_io = Map.insert key externIO (impure_state_extern_io is) }
        !st' = st { program_state_impure_state = is' }
    Trans.lift (State.put st')

  pure Repr.terminal


data DeferredKnot = forall s t i r . DeferredKnot
  { deferred_knot_signature :: !(Object.Knot s t i r)
  , deferred_knot_names     :: !(StaticVaryingNames r)
  -- TODO these need to not have any ValueM, only LocalM.
  -- So set ValueM to Identity.
  , deferred_knot_nexts     :: !(StaticVaryingNexts t)
  , deferred_knot_inits     :: !(StaticVaryingInits s i)
  }

-- | Array and index declarations.
--
-- NB: the arrays are uninitialized. They will be initialized by an init
-- function, also generated from the DeferredKnot.
deferredKnotStaticDeclarations :: DeferredKnot -> [C.Decln]
deferredKnotStaticDeclarations (DeferredKnot _ names _ _) = go names

  where

  -- There are no declarations required for varyings over uninhabited types.

  go :: StaticVaryingNames r -> [C.Decln]
  go (StaticVaryingNamesTied nrep trep inhabited tyName names) =
    [ arrayDeclaration (static_array_name names) nrep trep tyName
    , indexDeclaration (static_array_index_name names)
    ]
  go (StaticVaryingNamesTie nrep trep inhabited tyName names rec) =
    [ arrayDeclaration (static_array_name names) nrep trep tyName
    , indexDeclaration (static_array_index_name names)
    ] ++ go rec

  arrayDeclaration
    :: C.Ident
    -> NatRep ('S n)
    -> Object.Point.TypeRep t
    -> C.TypeName
    -> C.Decln
  arrayDeclaration ident sizeLessOne trep (C.TypeName specQualList mAbsDeclr) =
    let specs = C.specQualListToDeclnSpecs specQualList

        mPtr = C.mAbstractDeclrToPtr mAbsDeclr

        identDeclr :: C.DirectDeclr
        identDeclr = C.DirectDeclrIdent ident

        arraySize :: Natural
        arraySize = natToIntegral sizeLessOne + 1

        sizeExpr :: C.Expr
        sizeExpr = C.constIntExpr arraySize

        declr = C.Declr mPtr $ C.DirectDeclrArray1 identDeclr Nothing (Just (C.exprIsAssignExpr sizeExpr))

    in  C.Decln specs $ Just $ C.InitDeclrBase $ C.InitDeclr declr

  indexDeclaration :: C.Ident -> C.Decln
  indexDeclaration ident = C.Decln indexSpecs $ Just $ C.InitDeclrBase $
    C.InitDeclrInitr (C.Declr Nothing (C.DirectDeclrIdent ident)) (C.InitExpr (C.exprIsAssignExpr zero))

  -- Indices are always size_t
  indexSpecs :: C.DeclnSpecs
  indexSpecs = C.DeclnSpecsType (C.TTypedef (C.TypedefName ident_size_t)) Nothing

  zero :: C.Expr
  zero = C.constIntExpr 0

-- | Makes a LocalM which has all of the block items required to initialize the
-- arrays in this knot.
deferredKnotInits :: DeferredKnot -> LocalM ()
deferredKnotInits (DeferredKnot knotSig names _ inits) = go knotSig names inits

  where

  go :: Object.Knot s t i r
     -> StaticVaryingNames r
     -> StaticVaryingInits s i
     -> LocalM ()
  go (Object.Tied _ _) (StaticVaryingNamesTied (S_Rep _) _ _ _ names) (StaticVaryingInitsTied arep inhabited vec) = do
    cexprs <- vecSequence vec
    initOne names cexprs

  go (Object.Tie _ _ recKnot) (StaticVaryingNamesTie (S_Rep _) _ _ _ names recNames) (StaticVaryingInitsTie arep inhabited vec recInits) = do
    cexprs <- vecSequence vec
    initOne names cexprs
    go recKnot recNames recInits

  initOne names cexprs = forM_ (Prelude.zip [0..] (vecToList cexprs)) $ \(i, cexpr) -> do
    let arrayName = C.identIsExpr $ static_array_name names
        index = C.constIntExpr i
        arrayAtIndex :: C.Expr
        arrayAtIndex = C.postfixExprIsExpr $ C.PostfixIndex
          (exprIsPostfixExpr arrayName)
          index
        assignment :: C.Expr
        assignment = C.ExprAssign $ C.Assign
          (exprIsUnaryExpr arrayAtIndex)
          C.AEq
          (exprIsAssignExpr cexpr)
        bm = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just assignment
    addBlockItem bm

-- | For each of the arrays we make an assignment statement
--
--   <array_name>[(<index_name> + <array_size - 1>) % <array_size>] = <cexpr>
--
-- i.e. the _write_ index of the array is always one behind the read index.
deferredKnotArrayUpdates :: DeferredKnot -> LocalM ()
deferredKnotArrayUpdates (DeferredKnot knotSig names nexts _) = go knotSig names nexts

  where

  go :: Object.Knot s t i r
     -> StaticVaryingNames r
     -> StaticVaryingNexts t
     -> LocalM ()

  go (Object.Tied _ _) (StaticVaryingNamesTied nrep _ _ _ names) (StaticVaryingNextsTied _ inhabited exprM) = do
    cexpr <- exprM
    updateOne nrep names cexpr

  go (Object.Tie _ _ kn) (StaticVaryingNamesTie  nrep _ _ _ names recNames) (StaticVaryingNextsTie _ inhabited exprM recNexts) = do
    cexpr <- exprM
    updateOne nrep names cexpr
    go kn recNames recNexts

  updateOne nrep names cexpr =
    let arrayName = C.identIsExpr $ static_array_name names
        indexName = C.identIsExpr $ static_array_index_name names

        arraySize :: Natural
        arraySize = natToIntegral nrep + 1

        modulus :: C.Expr
        modulus = C.constIntExpr arraySize

        one :: C.Expr
        one = C.constIntExpr 1

        offsetExpr :: C.Expr
        offsetExpr = modulus `subtractExpr` one

        indexExpr :: C.Expr
        indexExpr = (indexName `addExpr` offsetExpr) `moduloExpr` modulus

        arrayAtWriteIndex :: C.Expr
        arrayAtWriteIndex = arrayIndexExpr arrayName indexExpr

        newValueExpr :: C.Expr
        newValueExpr = cexpr

        assignExpr :: C.Expr
        assignExpr = C.ExprAssign $ C.Assign
          (C.exprIsUnaryExpr arrayAtWriteIndex)
          C.AEq
          (C.exprIsAssignExpr newValueExpr)

        bm :: C.BlockItem
        bm = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $ assignExpr

    in  addBlockItem bm

-- | For each of the indices we make an assignment statement
--
--   <index_name> = (<index_name> + 1) % <array_size>
--
-- This is the _read_ index, so on the next frame the streams will appear to
-- have advanced.
deferredKnotIndexUpdates :: DeferredKnot -> LocalM ()
deferredKnotIndexUpdates (DeferredKnot _ names _ _) = go names

  where

  go :: StaticVaryingNames r -> LocalM ()
  go (StaticVaryingNamesTied nrep _ _ _ names) = updateOne nrep names
  go (StaticVaryingNamesTie nrep _ _ _ names rec) = do
    updateOne nrep names
    go rec

  updateOne nrep names =
    let indexName = C.identIsExpr $ static_array_index_name names

        arraySize :: Natural
        arraySize = natToIntegral nrep  + 1

        modulus :: C.Expr
        modulus = C.constIntExpr arraySize

        one :: C.Expr
        one = C.constIntExpr 1

        newIndexExpr :: C.Expr
        newIndexExpr = addExpr indexName one `moduloExpr` modulus

        assignExpr :: C.Expr
        assignExpr = C.ExprAssign $ C.Assign
          (C.exprIsUnaryExpr indexName)
          C.AEq
          (C.exprIsAssignExpr newIndexExpr)

        bm :: C.BlockItem
        bm = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $ assignExpr

    in  addBlockItem bm


-- | The 's' parameter is here to help GHC with, for example, judging pattern
-- match exhaustiveness. With only the 't' parameter, it's not such a good
-- story, because it is always set to the type family Object.Vector.
data StaticVaryingInits (s :: Meta.Type Object.Type) (t :: Meta.Type Object.Type) where

  StaticVaryingInitsTied
    :: Object.Point.TypeRep a
    -> Inhabited a
    -> Vec (S n) (LocalM C.Expr)
    -> StaticVaryingInits (Obj (Varying n a)) (Object.Vector ('S n) (Obj (Constant a)))

  StaticVaryingInitsTie
    :: Object.Point.TypeRep a
    -> Inhabited a
    -> Vec (S n) (LocalM C.Expr)
    -> StaticVaryingInits ss is
    -> StaticVaryingInits (Obj (Varying n a) :* ss) (Object.Vector ('S n) (Obj (Constant a)) :* is)

staticVaryingInits
  :: forall s t i r .
     Object.Knot s t i r
  -> Repr.Repr ValueM Value i
  -> ValueM (StaticVaryingInits s i)

staticVaryingInits (Object.Tied nrep arep) repr = do
  (inhabited, tyName, vec) <- staticVaryingInitVector arep nrep repr
  pure $ StaticVaryingInitsTied arep inhabited vec

staticVaryingInits (Object.Tie nrep arep knotSig) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  (inhabited, tyName, vec) <- staticVaryingInitVector arep nrep l
  vss <- staticVaryingInits knotSig r
  pure $ StaticVaryingInitsTie arep inhabited vec vss

-- | Construct the Vec of initial values for a static array, given the
-- appropriately-sized Vector (a type family) of constants.
--
staticVaryingInitVector
  :: forall n a .
     Object.Point.TypeRep a
  -> NatRep ('S n)
  -> Repr.Repr ValueM Value (Object.Vector ('S n) (Obj (Constant a)))
  -> ValueM (Inhabited a, C.TypeName, Vec ('S n) (LocalM C.Expr))

staticVaryingInitVector arep (S_Rep Z_Rep) repr = do
  v <- Repr.fromObject <$> Repr.getRepr repr
  pure $ case valueDefn v of
    ValueConstant inhabited tyName expr -> (inhabited, tyName, VCons expr VNil)

staticVaryingInitVector arep (S_Rep nrep@(S_Rep _)) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  v <- Repr.fromObject <$> Repr.getRepr l
  case valueDefn v of
    ValueConstant inhabited tyName expr -> do
      (_inhabited, _, vec) <- staticVaryingInitVector arep nrep r
      pure $ (inhabited, tyName, VCons expr vec)

staticVaryingNexts
  :: forall s t i r .
     Object.Knot s t i r
  -> Repr.Repr ValueM Value t
  -> ValueM (StaticVaryingNexts t)

staticVaryingNexts (Object.Tied _ arep) repr = do
  (inhabited, tyName, expr) <- staticVaryingNext arep repr
  pure $ StaticVaryingNextsTied arep inhabited expr

staticVaryingNexts (Object.Tie _ arep knotSig) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  (inhabited, tyName, expr) <- staticVaryingNext arep l
  rec <- staticVaryingNexts knotSig r
  pure $ StaticVaryingNextsTie arep inhabited expr rec


staticVaryingNext
  :: forall a .
     Object.Point.TypeRep a
  -> Repr.Repr ValueM Value (Obj (Varying Z a))
  -> ValueM (Inhabited a, C.TypeName, LocalM C.Expr)

staticVaryingNext arep repr = do
  v <- Repr.fromObject <$> Repr.getRepr repr
  pure $ case valueDefn v of
    ValueVarying inhabited tyName (VCons it VNil) -> (inhabited, tyName, it)


data StaticVaryingNexts (t :: Meta.Type Object.Type) where
  StaticVaryingNextsTied
    :: Object.Point.TypeRep t
    -> Inhabited t
    -> LocalM C.Expr
    -> StaticVaryingNexts (Obj (Varying Z t))
  StaticVaryingNextsTie
    :: Object.Point.TypeRep t
    -> Inhabited t
    -> LocalM C.Expr
    -> StaticVaryingNexts ts
    -> StaticVaryingNexts (Obj (Varying Z t) :* ts)


data ImpureState = ImpureState
  { -- | Determines the declarations required to implement all recursive knots
    -- used in the program.
    impure_state_knots           :: !(Seq DeferredKnot)
    -- | For generating new names for static arrays
  , impure_state_static_array_gen :: !StaticArrayGen
    -- | Extern declarations for I/O and for library functions.
  , impure_state_extern_io       :: !(Map ExternId ExternIO)
    -- | C source files to include.
  , impure_state_includes        :: !()
    -- | The programmer-friendly interface: determines declarations for functions
    -- and types which will be in the I/O interface for the generated C.
  , impure_state_interface       :: !()
  }

initialImpureState :: ImpureState
initialImpureState = ImpureState
  { impure_state_knots = Seq.empty
  , impure_state_static_array_gen = Gen 0
  , impure_state_extern_io = Map.empty
  , impure_state_includes = ()
  , impure_state_interface = ()
  }

type StaticArrayGen = Gen

genStaticArrayId :: ProgramM Integer
genStaticArrayId = ProgramM $ do
  st <- Trans.lift $ State.get
  let (name, !st') = genValue
        (impure_state_static_array_gen . program_state_impure_state)
        (\x s -> s { program_state_impure_state = (program_state_impure_state s) { impure_state_static_array_gen = x } })
        (\x -> x)
        st
  Trans.lift $ State.put st'
  pure name

mkStaticArrayName :: Integer -> String
mkStaticArrayName = (++) "memory_stream_data_" . show

mkStaticArrayIndexName :: Integer -> String
mkStaticArrayIndexName = (++) "memory_stream_index_" . show

genStaticArrayNames :: ProgramM StaticArrayNames
genStaticArrayNames = do
  n <- genStaticArrayId
  let arrayName = mkStaticArrayName n
      indexName = mkStaticArrayIndexName n
  pure $ StaticArrayNames
    { static_array_name       = assertValidStringIdentifier arrayName
    , static_array_index_name = assertValidStringIdentifier indexName
    }

addDeferredKnot :: DeferredKnot -> ProgramM ()
addDeferredKnot defKnot = ProgramM $ do
  st <- Trans.lift State.get
  let is = program_state_impure_state st
      ks = impure_state_knots is
      !is' = is { impure_state_knots = ks Seq.|> defKnot }
      !st' = st { program_state_impure_state = is' }
  Trans.lift $ State.put st'
  pure ()

-- TODO rename? KnotSignature?
data StaticVaryingNames (r :: Meta.Type Object.Type) where

  StaticVaryingNamesTied
    :: NatRep ('S n)
    -> Object.Point.TypeRep a
    -> Inhabited a
    -> C.TypeName
    -> StaticArrayNames
    -> StaticVaryingNames (Obj (Varying ('S n) a))

  StaticVaryingNamesTie
    :: NatRep ('S n)
    -> Object.Point.TypeRep a
    -> Inhabited a
    -> C.TypeName
    -> StaticArrayNames
    -> StaticVaryingNames r
    -> StaticVaryingNames (Obj (Varying ('S n) a) :* r)

data StaticArrayNames = StaticArrayNames
  { static_array_name       :: !C.Ident
  , static_array_index_name :: !C.Ident
  }

-- | Makes a vector of expressions of the form
--
--    array_name[(index_name + i) % size]
--
-- for every i <= n, so that if you give a NatRep 'Z you get only
-- one expression. The modulus size is a parameter. It's not always supposed
-- to be the same as the length of the vector.
--
-- This is used to make a `Value (Obj (Varying n t))` for a memory stream.
-- This consists of `S n` `LocalM C.Expr`s, where the array size is 1 plus
-- `S n`, because there is an extra "write cell" for updating at the end of
-- a frame.
--
-- So for example if there is a memory stream of prefix size 0, then the array
-- has 2 cells, but there is only one expression to read from it, and it is
-- always `array_name[(index_name + 0) % 1]`.
--
staticArrayIndexExprs
  :: forall n .
     StaticArrayNames
  -> Natural -- ^ Array size / modulus
  -> NatRep n
  -> Vec (S n) C.Expr
staticArrayIndexExprs names arraySize nrep = vecMap mkIndexExpr offsets

  where

  offsets :: Vec (S n) C.Expr
  offsets = mkOffsets nrep 0

  mkOffsets :: forall n . NatRep n -> Natural -> Vec (S n) C.Expr
  mkOffsets Z_Rep     m = VCons (C.constIntExpr m) VNil
  mkOffsets (S_Rep n) m = VCons (C.constIntExpr m) (mkOffsets n (m + 1))

  arrayName = C.identIsExpr $ static_array_name names
  indexName = C.identIsExpr $ static_array_index_name names
  
  modulus :: C.Expr
  modulus = C.constIntExpr arraySize

  mkIndexExpr :: C.Expr -> C.Expr
  mkIndexExpr n = arrayIndexExpr arrayName (mkOffsetExpr n)

  mkOffsetExpr :: C.Expr -> C.Expr
  mkOffsetExpr n = moduloExpr (addExpr indexName n) modulus

genStaticVaryingNames
  :: forall s t i r .
     Meta.TypeRep Object.TypeRep r
  -> Object.Knot s t i r
  -> StaticVaryingInits s i
  -> ProgramM (StaticVaryingNames r)

genStaticVaryingNames (Obj (Varying _ arep)) (Object.Tied nrep _) (StaticVaryingInitsTied _ inhabited _) = do
  names <- genStaticArrayNames
  tyName <- valueMInProgramM $ typeName inhabited (Constant arep)
  pure $ StaticVaryingNamesTied nrep arep inhabited tyName names

genStaticVaryingNames (Obj (Varying _ arep) :* rs) (Object.Tie nrep _ kn) (StaticVaryingInitsTie _ inhabited _ recInits) = do
  names <- genStaticArrayNames
  tyName <- valueMInProgramM $ typeName inhabited (Constant arep)
  rec <- genStaticVaryingNames rs kn recInits
  pure $ StaticVaryingNamesTie nrep arep inhabited tyName names rec

-- TODO FIXME why can't GHC figure out that the above 2 clauses are an
-- exhaustive match? Should not have to give all of the following explicit
-- demonstrations.

genStaticVaryingNames (_ :-> _) it _ = case it of {}
genStaticVaryingNames ((_ :-> _) :* _) it _ = case it of {}
genStaticVaryingNames Meta.Terminal it _ = case it of {}
genStaticVaryingNames (Meta.Terminal :* _) it _ = case it of {}
genStaticVaryingNames ((_ :* _) :* _) it _ = case it of {}
genStaticVaryingNames (Obj (Program _)) it _ = case it of {}
genStaticVaryingNames (Obj (Constant _)) it _ = case it of {}
genStaticVaryingNames (Obj (Program _) :* _) it _ = case it of {}
genStaticVaryingNames (Obj (Constant _) :* _) it _ = case it of {}

-- | Use the names to get values of varyings. This is done by taking the
-- array name indexed at the array index value, plus each of the valid offsets,
-- modulo the size of the array.
staticVaryingValues :: StaticVaryingNames r -> Repr.Repr ValueM Value r

staticVaryingValues (StaticVaryingNamesTie nrep trep inhabited tyName names rec) = Repr.product
  ( Repr.object (varyingValue_ (Obj (Varying nrep trep)) inhabited tyName (staticArrayIndexExprs names arraySize nrep))
  , staticVaryingValues rec
  )
  where
  arraySize = natToIntegral nrep + 1

staticVaryingValues (StaticVaryingNamesTied nrep trep inhabited tyName names) = Repr.object $
  varyingValue_ (Obj (Varying nrep trep)) inhabited tyName (staticArrayIndexExprs names arraySize nrep)
  where
  arraySize = natToIntegral nrep + 1

-- | Just like 'staticVaryingValues' but everything has one less prefix index
-- size. Key feature however is that it relates s and r of a Knot.
--
-- NB: we call staticArrayIndexExprs with the same array size as the actual
-- array, but with a lower NatRep value, so that it will only index 1 fewer
-- than is possible, but the index arithmetic will still work out because the
-- modulus is correct.
shiftedStaticVaryingValues
  :: Object.Knot s t i r
  -> StaticVaryingNames r
  -> Repr.Repr ValueM Value s
shiftedStaticVaryingValues (Object.Tied _ _)   (StaticVaryingNamesTied (S_Rep nrep) trep inhabited tyName names)     = Repr.object $
  varyingValue_ (Obj (Varying nrep trep)) inhabited tyName (staticArrayIndexExprs names arraySize nrep)
  where
  arraySize = natToIntegral nrep + 2

shiftedStaticVaryingValues (Object.Tie _ _ kn) (StaticVaryingNamesTie  (S_Rep nrep) trep inhabited tyName names rec) = Repr.product
  ( Repr.object (varyingValue_ (Obj (Varying nrep trep)) inhabited tyName (staticArrayIndexExprs names arraySize nrep))
  , shiftedStaticVaryingValues kn rec
  )
  where
  arraySize = natToIntegral nrep + 2

transStateT :: Monad m => (s -> u) -> (u -> s -> s) -> StateT u m t -> StateT s m t
transStateT lget lset st = do
  s <- State.get
  let u = lget s
  (t, u') <- Trans.lift $ State.runStateT st u
  let s' = lset u' s
  State.put s'
  pure t

-- | This expresses the same thing as `return :: t -> IO t`: a `ValueM t` is
-- the representation of a "pure" computation (no memory streams, extern I/O
-- declarations, etc), and `valueMInProgramM` says that these can also be
-- treated as "impure". The definitions is trivial, since `ProgramM` has the
-- `ValueM` state transition built-in.
valueMInProgramM :: ValueM t -> ProgramM t
valueMInProgramM vm = ProgramM $ Trans.lift $
  transStateT program_state_pure_state (\x s -> s { program_state_pure_state = x }) (unValueM vm)

-- | A value is any C expression. However it's not meaningful on its own in
-- general; it requires context (type declarations, statements binding names,
-- etc.) which come from ValueM and LocalM monads.
data Value (t :: Object.Type) = Value
  { valueType  :: !(Object.TypeRep t)
  , valueDefn  :: !(ValueDefn t)
  }

-- | For constant and varying values, we include proof that they are inhabited.
-- Types which are not inhabited do not get a C representation, which should
-- in theory make it easier to define a correct interpretation.
data ValueDefn (t :: Object.Type) where
  ValueConstant :: Inhabited t -> !C.TypeName ->             LocalM C.Expr  -> ValueDefn (Constant   t)
  -- | A varying of prefix size 0 has 1 expression (the current, first/oldest
  -- value).
  ValueVarying  :: Inhabited t -> !C.TypeName -> Vec ('S n) (LocalM C.Expr) -> ValueDefn (Varying  n t)
  ValueProgram  :: ProgramM (Repr.Repr ValueM Value t) -> ValueDefn (Program    t)

-- | Change the type of a constant value without changing its C representation.
-- The TypeName does not change.
-- Use with care. It should only be used to change between values which do
-- indeed have the same C type and value.
changeConstantValueType
  :: (Object.Point.TypeRep s -> Object.Point.TypeRep t)
  -> (Inhabited s -> Inhabited t)
  -> Value (Constant s)
  -> Value (Constant t)
changeConstantValueType fty stillInhabited v = v'
  where
  v' = value (Constant (fty trep)) defn
  Constant trep = valueType v
  defn = case valueDefn v of
    ValueConstant inh tyName cExpr -> ValueConstant (stillInhabited inh) tyName cExpr

constantValueIsInhabited :: Value (Constant t) -> Inhabited t
constantValueIsInhabited v = case valueDefn v of
  ValueConstant inhabited _ _ -> inhabited

varyingValueIsInhabited :: Value (Varying n t) -> Inhabited t
varyingValueIsInhabited v = case valueDefn v of
  ValueVarying inhabited _ _ -> inhabited

noUninhabitedConstant :: Not (Inhabited t) -> Not (Value (Constant t))
noUninhabitedConstant uninhabited v = case valueDefn v of
  ValueConstant inhabited _ _ -> uninhabited inhabited

noUninhabitedVarying :: Not (Inhabited t) -> Not (Value (Varying n t))
noUninhabitedVarying uninhabited v = case valueDefn v of
  ValueVarying inhabited _ _ -> uninhabited inhabited

valueConstantType :: Value (Constant t) -> Object.Point.TypeRep t
valueConstantType v = case valueType v of
  Constant trep -> trep

valueConstantExpr :: Value (Constant t) -> LocalM C.Expr
valueConstantExpr v = case valueDefn v of
  ValueConstant _ _ e -> e

valueVaryingType :: Value (Varying n t) -> (NatRep n, Object.Point.TypeRep t)
valueVaryingType v = case valueType v of
  Varying nrep trep -> (nrep, trep)

valueVaryingExprs :: Value (Varying n t) -> Vec ('S n) (LocalM C.Expr)
valueVaryingExprs v = case valueDefn v of
  ValueVarying _ _ vs -> vs

valueProgramType :: Value (Program t) -> Meta.TypeRep Object.TypeRep t
valueProgramType v = case valueType v of
  Program trep -> trep

valueProgramRepr :: Value (Program t) -> ProgramM (Repr.Repr ValueM Value t)
valueProgramRepr v = case valueDefn v of
  ValueProgram it -> it

valueConstantTypeName :: Value (Constant t) -> C.TypeName
valueConstantTypeName v = case valueDefn v of
  ValueConstant _ tyName _ -> tyName

valueVaryingTypeName :: Value (Varying n t) -> C.TypeName
valueVaryingTypeName v = case valueDefn v of
  ValueVarying _ tyName _ -> tyName


constantValueToExpr
  :: Repr.Val ValueM Value (Obj (Constant t))
  -> LocalM C.Expr
constantValueToExpr = valueConstantExpr . Repr.fromObject

varyingValueToExpr
  :: Repr.Val ValueM Value (Obj (Varying n t))
  -> Index ('S n)
  -> LocalM C.Expr
varyingValueToExpr repr idx = index idx
  (valueVaryingExprs (Repr.fromObject repr))

dropVaryingValue :: Value (Varying ('S n) t) -> Value (Varying n t)
dropVaryingValue v = Value
  { valueType = case valueType v of
      Varying (S_Rep nrep) trep -> Varying nrep trep
  , valueDefn = case valueDefn v of
      ValueVarying inhabited tyName vec -> ValueVarying inhabited tyName (vecDropFirst vec)
  }

shiftVaryingValue :: Value (Varying ('S n) t) -> Value (Varying n t)
shiftVaryingValue v = Value
  { valueType = case valueType v of
      Varying (S_Rep nrep) trep -> Varying nrep trep
  , valueDefn = case valueDefn v of
      ValueVarying inhabited tyName vec -> ValueVarying inhabited tyName (vecDropLast vec)
  }

value
  :: Object.TypeRep t
  -> ValueDefn t
  -> Value t
value trep defn = Value { valueType = trep, valueDefn = defn }

constantValueType :: Value (Constant t) -> Object.Point.TypeRep t
constantValueType v = case valueType v of
  Object.Constant_r trep -> trep

-- | Make an _inhabited_ constant value.
constantValue
  :: Meta.TypeRep Object.TypeRep (Obj (Constant t))
  -> Inhabited t
  -> C.TypeName
  -> LocalM C.Expr
  -> Value (Constant t)
constantValue (Obj trep) inhabited tyName expr = value trep
  (ValueConstant inhabited tyName expr)

constantValue_
  :: Meta.TypeRep Object.TypeRep (Obj (Constant t))
  -> Inhabited t
  -> C.TypeName
  -> C.Expr
  -> Value (Constant t)
constantValue_ trep inhabited tyName cexpr = constantValue trep inhabited tyName (pure cexpr)

-- | Make an _inhabited_ varying value.
varyingValue
  :: Meta.TypeRep Object.TypeRep (Obj (Varying n t))
  -> Inhabited t
  -> C.TypeName
  -> Vec (S n) (LocalM C.Expr)
  -> Value (Varying n t)
varyingValue (Obj trep) inhabited tyName exprs = value trep (ValueVarying inhabited tyName exprs)

varyingValue_
  :: Meta.TypeRep Object.TypeRep (Obj (Varying n t))
  -> Inhabited t
  -> C.TypeName
  -> Vec (S n) C.Expr
  -> Value (Varying n t)
varyingValue_ trep inhabited tyName exprs = varyingValue trep inhabited tyName (vecMap pure exprs)

programValue
  :: Meta.TypeRep Object.TypeRep t
  -> ProgramM (Repr.Repr ValueM Value t)
  -> Value (Program t)
programValue trep progM = value (Object.program_t trep) (ValueProgram progM)

overObject1
  :: (Value t -> Value r)
  -> (Repr.Val ValueM Value (Obj t) -> Repr.Val ValueM Value (Obj r))
overObject1 f = Repr.Object . f . Repr.fromObject

overObject2
  :: (Value s -> Value t -> Value r)
  -> (Repr.Val ValueM Value (Obj s) -> Repr.Val ValueM Value (Obj t) -> Repr.Val ValueM Value (Obj r))
overObject2 f s t = Repr.Object (f (Repr.fromObject s) (Repr.fromObject t))

-- | Map a C expression level function over inhabited values.
overConstantValue1
  :: (Object.Point.TypeRep s -> Object.Point.TypeRep s)
  -> (C.Expr -> C.Expr)
  -> (Value (Constant s) -> Value (Constant s))
overConstantValue1 fty fexpr = \v ->
  let ty = fty (valueConstantType v)
      ex = fexpr <$> valueConstantExpr v
      inhabited = constantValueIsInhabited v
      tyName = valueConstantTypeName v
  in  value (Constant ty) (ValueConstant inhabited tyName ex)

-- | Specialization of 'overConstantValue1' for integers, possible because we
-- know that integer types are always inhabited, and we can get their type names
-- without ValueM context.
overConstantValue1Integer
  :: (Object.Point.TypeRep ('Object.Point.Integer_t s w) -> Object.Point.TypeRep ('Object.Point.Integer_t s' w'))
  -> (C.Expr -> C.Expr)
  -> (Value (Constant ('Object.Point.Integer_t s w)) -> Value (Constant ('Object.Point.Integer_t s' w')))
overConstantValue1Integer fty fexpr = \v ->
  let ty = fty (valueConstantType v)
      ex = fexpr <$> valueConstantExpr v
      inhabited = integerIsInhabited
      tyName = typeNameInteger ty
  in  value (Constant ty) (ValueConstant inhabited tyName ex)

overConstantValue1Heterogeneous
  :: Inhabited t
  -> C.TypeName -- ^ of t
  -> (Object.Point.TypeRep s -> Object.Point.TypeRep t)
  -> (C.Expr -> C.Expr)
  -> (Value (Constant s) -> Value (Constant t))
overConstantValue1Heterogeneous inhabited tyName fty fexpr = \v ->
  let ty = fty (valueConstantType v)
      ex = fexpr <$> valueConstantExpr v
  in  value (Constant ty) (ValueConstant inhabited tyName ex)

-- | Map a 2-arguemtn C expression level function over inhabited values.
overConstantValue2
  :: (Object.Point.TypeRep s -> Object.Point.TypeRep x -> Object.Point.TypeRep s)
  -> (C.Expr -> C.Expr -> C.Expr)
  -> (Value (Constant s) -> Value (Constant x) -> Value (Constant s))
overConstantValue2 fty fexpr = \v1 v2 ->
  let ty = fty (valueConstantType v1) (valueConstantType v2)
      ex = fexpr <$> valueConstantExpr v1 <*> valueConstantExpr v2
      inhabited = constantValueIsInhabited v1
      tyName = valueConstantTypeName v1
  in  value (Constant ty) (ValueConstant inhabited tyName ex)

interpC :: Repr.Interpret Object.Form ValueM Value
interpC trep form = case form of

  -- TODO may be best to put explicit type casts on these.
  Object.Integer_Literal_UInt8_f  w8  -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral w8)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_UInt16_f w16 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral w16)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_UInt32_f w32 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral w32)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_UInt64_f w64 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral w64)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep

  Object.Integer_Literal_Int8_f  i8  -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral i8)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_Int16_f i16 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral i16)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_Int32_f i32 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral i32)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep
  Object.Integer_Literal_Int64_f i64 -> Repr.object . constantValue_ trep integerIsInhabited tyName $
    integerLiteralExpr tyName (fromIntegral i64)
    where
    Obj (Constant irep) = trep
    tyName = typeNameInteger irep

  Object.Bytes_Literal_8_f  w8  -> Repr.object . constantValue_ trep bytesIsInhabited tyName $
    bytesLiteralExpr (typeNameBytes brep) (fromIntegral w8)
    where
    Obj (Constant brep) = trep
    tyName = typeNameBytes brep
  Object.Bytes_Literal_16_f w16 -> Repr.object . constantValue_ trep bytesIsInhabited tyName $
    bytesLiteralExpr (typeNameBytes brep) (fromIntegral w16)
    where
    Obj (Constant brep) = trep
    tyName = typeNameBytes brep
  Object.Bytes_Literal_32_f w32 -> Repr.object . constantValue_ trep bytesIsInhabited tyName $
    bytesLiteralExpr (typeNameBytes brep) (fromIntegral w32)
    where
    Obj (Constant brep) = trep
    tyName = typeNameBytes brep
  Object.Bytes_Literal_64_f w64 -> Repr.object . constantValue_ trep bytesIsInhabited tyName $
    bytesLiteralExpr tyName (fromIntegral w64)
    where
    Obj (Constant brep) = trep
    tyName = typeNameBytes brep

  Object.Integer_Add_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 addValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Integer_Subtract_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 subtractValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Integer_Multiply_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 multiplyValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Integer_Divide_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 divideValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Integer_Modulo_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 moduloValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Integer_Negate_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 negateValue <$> Repr.getRepr x)
  Object.Integer_Abs_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 absValue <$> Repr.getRepr x)

  Object.Integer_Compare_f -> error "TODO integer compare"

  Object.Bytes_And_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 andValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Bytes_Or_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 orValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Bytes_Xor_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 xorValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Bytes_Complement_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 complementValue <$> Repr.getRepr x)
  Object.Bytes_Shiftl_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 shiftlValue <$> Repr.getRepr x <*> Repr.getRepr y)
  Object.Bytes_Shiftr_f -> Repr.fun $ \x -> Repr.fun $ \y ->
    Repr.repr (overObject2 shiftrValue <$> Repr.getRepr x <*> Repr.getRepr y)

  Object.Cast_f cast -> Repr.fun $ \x -> Repr.objectf $ do
    vx <- Repr.getRepr x
    castValue trep cast (Repr.fromObject vx)

  Object.Stream_Shift_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 shiftVaryingValue <$> Repr.getRepr x)
  Object.Stream_Drop_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 dropVaryingValue <$> Repr.getRepr x)

  Object.Stream_Map_f nrep limage rimage -> interpMap trep nrep limage rimage

  -- The composite type intro/elim forms may introduce new required type
  -- declarations.

  Object.Product_Intro_f fields   -> Repr.fun $ interpProductIntro trep fields
  Object.Product_Elim_f  selector -> Repr.fun $ interpProductElim  trep selector
  Object.Sum_Intro_f variant -> Repr.fun $ interpSumIntro trep variant
  Object.Sum_Elim_f _ -> error "Sum_Elim_f not defined"

  -- The knot form will introduce static declarations for stream memory.
  Object.Stream_Knot_f kn -> interpKnot trep kn

  Object.Program_Map_f  -> interpProgramMap  trep
  Object.Program_Pure_f -> interpProgramPure trep
  Object.Program_Ap_f   -> interpProgramAp   trep
  Object.Program_Join_f -> interpProgramJoin trep

  -- Let will introduce a C assignment to a fresh name, and run the continuation
  -- with that name, rather than the whole expression.
  Object.Let_f -> Repr.fun $ \x -> Repr.fun $ \k -> interpLet trep x k


-- | A new name is generated, the object is evaluated here (i.e. in the
-- LocalM monad, possibly generating statements like assignments and
-- switch/cases), and the resulting expression is bound to the new name. The
-- continuation is then run with a value in LocalM which does nothing but
-- return the binder name.
interpLet
  :: forall s t .
     Meta.TypeRep Object.TypeRep (Obj (Constant s) :-> (Obj (Constant s) :-> t) :-> t)
  -> Repr.Repr ValueM Value (Obj (Constant s))
  -> Repr.Repr ValueM Value (Obj (Constant s) :-> t)
  -> Repr.Repr ValueM Value t
interpLet (Obj (Constant srep) :-> _) x k = Repr.valuef $ do
  constObj <- Repr.fromObject <$> Repr.getRepr x
  case valueDefn constObj of
    ValueConstant inhabited _ exprM -> do
      boundValue <- makeIdempotent srep inhabited exprM
      Repr.getRepr (k Repr.<@> Repr.object boundValue)


interpProductIntro
  :: forall r fields .
     Meta.TypeRep Object.TypeRep (r :-> Obj (Constant ('Object.Point.Product_t fields)))
  -> Object.Fields r fields
  -> Repr.Repr ValueM Value r
  -> Repr.Repr ValueM Value (Obj (Constant ('Object.Point.Product_t fields)))

interpProductIntro (rrep :-> Obj (Constant prep)) fields rval = Repr.objectf $ do
  (allInhabited, allArguments) <- takeFieldArguments fields rval
  let inhabited = productIsInhabited allInhabited
      Object.Point.Product_r fieldReps = prep
  pr <- productRepresentation inhabited fieldReps
  productIntroduction pr fields allArguments

  where

  takeFieldArguments
    :: forall r fields .
       Object.Fields r fields
    -> Repr.Repr ValueM Value r
    -> ValueM (All Inhabited fields, All (Compose Value Constant) fields)
  takeFieldArguments Object.F_All rval = do
    _ <- Repr.getRepr rval
    pure (All, All)
  takeFieldArguments (Object.F_And fields) rval = do
    (l, r) <- Repr.fromProduct <$> Repr.getRepr rval
    lval <- Repr.fromObject <$> Repr.getRepr l
    let inhabited = constantValueIsInhabited lval
    (allInhabited, allValues) <- takeFieldArguments fields r
    pure (And inhabited allInhabited, And (Compose lval) allValues)


interpProductElim
  :: forall fields field .
     Meta.TypeRep Object.TypeRep (Obj (Constant ('Object.Point.Product_t fields)) :-> Obj (Constant field))
  -> Object.Selector fields field
  -> Repr.Repr ValueM Value (Obj (Constant ('Object.Point.Product_t fields)))
  -> Repr.Repr ValueM Value (Obj (Constant field))

interpProductElim (Obj (Constant prep) :-> Obj (Constant trep)) selector valRepr = Repr.objectf $ do
  val <- Repr.fromObject <$> Repr.getRepr valRepr
  let inhabited = constantValueIsInhabited val
      Object.Point.Product_r fieldReps = constantValueType val
  pr <- productRepresentation inhabited fieldReps
  productElimination pr trep selector val


interpSumIntro
  :: forall r variants .
     Meta.TypeRep Object.TypeRep (r :-> Obj (Constant ('Object.Point.Sum_t variants)))
  -> Object.Variant r variants
  -> Repr.Repr ValueM Value r
  -> Repr.Repr ValueM Value (Obj (Constant ('Object.Point.Sum_t variants)))
interpSumIntro (rrep :-> Obj (Constant srep)) variant rval = Repr.objectf $ do
  undefined
  {-(someInhabited, someArgument) <- takeVariantArgument variants rval
  let inhabited = sumIsInhabited someInhabited
      Object.Point.Sum_r variantReps = srep
  sr <- sumRepresentation inhabited variantReps
  let val = sumIntroduction sr fields someArgument
  pure val-}


-- | This will use the ProgramM representation to come up with all the
-- necessary StaticVaryings, then put them into the state, and return the
-- basic varying representation
--
--   VCons (name[i]) (VCons (name[(i+1)%size]) ...)
--
-- If any of the point types involved is uninhabited, then the entire knot
-- is ... 
interpKnot
  :: forall s t i r .
     Meta.TypeRep Object.TypeRep ((s :-> t) :-> (i :-> Obj (Program r)))
  -> Object.Knot s t i r
  -> Repr.Repr ValueM Value ((s :-> t) :-> (i :-> Obj (Program r)))

interpKnot ((srep :-> trep) :-> (irep :-> Obj (Program rrep))) knotSig =
  Repr.fun $ \recDef ->
  Repr.fun $ \i -> Repr.object $ programValue rrep $ do

    -- This is a ProgramM do block.
    -- With the Knot TypeRep values in hand, we can generate fresh names for
    -- the static arrays and indices for every varying in this knot, and use
    -- these to back values.
    -- It's here where we run the ValueMs of the recDef function application
    -- and of the initial values, but we do _not_ run the resulting LocalMs
    -- until we generate the translation unit. They are stored in the state as
    -- a DeferredKnot value.

    -- Here we need to evaluate in ValueM, to get the LocalMs for all of the
    -- updates (`t`s) and inits (`i`s), then put those LocalMs into the
    -- state so they can be elaborated later on when we make a translation unit.
    inits <- valueMInProgramM $ staticVaryingInits knotSig i
    -- We need the inits because they contain proofs that each stream is
    -- inhabited.
    names <- genStaticVaryingNames rrep knotSig inits
    let r :: Repr.Repr ValueM Value r
        r = staticVaryingValues names
        s :: Repr.Repr ValueM Value s
        s = shiftedStaticVaryingValues knotSig names
        t :: Repr.Repr ValueM Value t
        t = recDef Repr.<@> s
    nexts <- valueMInProgramM $ staticVaryingNexts knotSig t
    let deferredKnot :: DeferredKnot
        deferredKnot = DeferredKnot
          { deferred_knot_signature = knotSig
          , deferred_knot_names     = names
          , deferred_knot_nexts     = nexts
          , deferred_knot_inits     = inits
          }
    addDeferredKnot deferredKnot
    pure r


interpProgramMap
  :: Meta.TypeRep Object.TypeRep ((s :-> t) :-> (Obj (Program s) :-> Obj (Program t)))
  -> Repr.Repr ValueM Value ((s :-> t) :-> (Obj (Program s) :-> Obj (Program t)))
interpProgramMap ((_ :-> trep) :-> _) = Repr.fun $ \f -> Repr.fun $ \progS -> Repr.objectf $ do
  it <- Repr.fromObject <$> Repr.getRepr progS
  let progM = fmap (f Repr.<@>) (valueProgramRepr it)
  pure $ programValue trep progM

interpProgramPure
  :: Meta.TypeRep Object.TypeRep (t :-> Obj (Program t))
  -> Repr.Repr ValueM Value (t :-> Obj (Program t))
interpProgramPure (trep :-> _) = Repr.fun $ \s -> Repr.object $
  let progM = pure s
  in  programValue trep progM

interpProgramAp
  :: Meta.TypeRep Object.TypeRep (Obj (Program (s :-> t)) :-> Obj (Program s) :-> Obj (Program t))
  -> Repr.Repr ValueM Value (Obj (Program (s :-> t)) :-> Obj (Program s) :-> Obj (Program t))
interpProgramAp (Obj (Program (_ :-> trep)) :-> _) = Repr.fun $ \progF -> Repr.fun $ \progS -> Repr.objectf $ do
  itF <- Repr.fromObject <$> Repr.getRepr progF
  itS <- Repr.fromObject <$> Repr.getRepr progS
  let progM = (Repr.<@>) <$> valueProgramRepr itF <*> valueProgramRepr itS
  pure $ programValue trep progM

-- | To do monadic join on the program, we need 'valueMInProgramM', because
-- type inside the 'ProgramM' is a 'ValueM'.
interpProgramJoin
  :: forall t .
     Meta.TypeRep Object.TypeRep (Obj (Program (Obj (Program t))) :-> Obj (Program t))
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Program t))) :-> Obj (Program t))
interpProgramJoin (Obj (Program (Obj (Program trep))) :-> _) = Repr.fun $ \progProg -> Repr.objectf $ do
  thisProg :: ProgramM (Repr.Repr ValueM Value (Obj (Program t)))
    <- tearDown progProg
  let nextProg :: ProgramM (ValueM (ProgramM (Repr.Repr ValueM Value t)))
      nextProg = tearDown <$> thisProg
      progM = Monad.join (Monad.join (valueMInProgramM <$> nextProg))
  pure $ programValue trep progM
  where
  tearDown :: forall x . Repr.Repr ValueM Value (Obj (Program x)) -> ValueM (ProgramM (Repr.Repr ValueM Value x))
  tearDown = fmap (valueProgramRepr . Repr.fromObject) . Repr.getRepr

-- | This is just like the pure implementation. The product of varyings gives
-- a product of vectors, which are zipped together to give a product of
-- constants fitting with the mapped function type. The mapped function is
-- evaluated and applied, and the results are unzipped to give the RHS product.
interpMap
  :: forall n s t q r .
     Meta.TypeRep Object.TypeRep ((s :-> t) :-> (q :-> r))
  -> NatRep n
  -> Object.MapImage n s q
  -> Object.MapImage n t r
  -> Repr.Repr ValueM Value ((s :-> t) :-> (q :-> r))
interpMap ((srep :-> _) :-> (_ :-> rrep)) nrep limage rimage =
  Repr.fun $ \preimage -> Repr.fun $ \q -> Repr.valuef $ do
    rolled  <- zipVarying srep nrep limage q
    f <- Repr.getRepr preimage
    let applied = applyVarying f rolled
    Repr.getRepr (unzipVarying rrep nrep rimage applied)

  where

  zipVarying
    :: forall n s q .
       Meta.TypeRep Object.TypeRep s
    -> NatRep n
    -> Object.MapImage n s q
    -> Repr.Repr ValueM Value q
    -> ValueM (Vec ('S n) (Repr.Repr ValueM Value s))

  zipVarying _              nrep Object.MapTerminal      _ = pure $
    vecReplicate (S_Rep nrep) Repr.terminal

  zipVarying trep           nrep Object.MapObject        v = do
    it <- Repr.getRepr v
    -- If the varying given is over an uninhabited constant type, then this
    -- corresponds to that same uninhabited type, and we can pass that
    -- through to the mapped arrow.
    case valueDefn (Repr.fromObject it) of
      ValueVarying inhabited tyName exprs -> pure $ vecMap
        (\expr -> Repr.object (constantValue trep inhabited tyName expr))
        exprs

  zipVarying (lrep :* rrep) nrep (Object.MapProduct l r) v = do
    it <- Repr.getRepr v
    let (lv, rv) = Repr.fromProduct it
    lefts  <- zipVarying lrep nrep l lv
    rights <- zipVarying rrep nrep r rv
    pure $ vecZip (Repr.<&) lefts rights

  applyVarying
    :: forall n s t .
       Repr.Val ValueM Value (s :-> t)
    -> Vec ('S n) (Repr.Repr ValueM Value s)
    -> Vec ('S n) (Repr.Repr ValueM Value t)
  applyVarying f vec = vecMap (Repr.fromArrow f) vec

  unzipVarying
    :: forall n t r .
       Meta.TypeRep Object.TypeRep r
    -> NatRep n
    -> Object.MapImage n t r
    -> Vec ('S n) (Repr.Repr ValueM Value t)
    -> Repr.Repr ValueM Value r

  unzipVarying _              nrep Object.MapTerminal      _ = Repr.terminal

  unzipVarying (Obj trep)     nrep Object.MapObject        v = Repr.objectf $ do
    w <- vecTraverse Repr.getRepr v
    let (inhabited, tyName, cexprs) = mkConstantExprs w
    pure $ varyingValue (Obj trep) inhabited tyName cexprs

  unzipVarying (lrep :* rrep) nrep (Object.MapProduct l r) v = Repr.valuef $ do
    w <- vecTraverse Repr.getRepr v
    let (lw, rw) = vecUnzip (\(Repr.Product (a, b)) -> (a, b)) w
        a = unzipVarying lrep nrep l lw
        b = unzipVarying rrep nrep r rw
    pure $ Repr.Product (a, b)

  -- Use the first element's inhabited proof, required in order to take the
  -- rest of the expressions.
  mkConstantExprs :: forall x n .
       Vec ('S n) (Repr.Val ValueM Value (Obj (Constant x)))
    -> (Inhabited x, C.TypeName, Vec ('S n) (LocalM C.Expr))
  mkConstantExprs vs@(VCons constObj _) = case valueDefn (Repr.fromObject constObj) of
    ValueConstant inhabited tyName _ ->
      (inhabited, tyName, vecMap constantValueToExpr vs)

-- | We don't even need to do any checking here, GHC should ensure that all of
-- our casts are safe (assuming the EDSL types are set up correctly).
--
-- It's in ValueM because it uses the Maybe type, a composite, which requires
-- some context (sum types are monomorphized and require unique names).
castValue
  :: forall a b .
     Meta.TypeRep Object.TypeRep (Obj (Constant a) :-> Obj (Constant b))
  -> Object.Cast a b
  -> Value (Constant a)
  -> ValueM (Value (Constant b))
castValue (_ :-> Obj (Constant brep)) cast valueA = case cast of

  Object.UpCastInteger _ -> pure $ overConstantValue1Heterogeneous
    integerIsInhabited (typeNameInteger brep) castTypeRep (castExpr (typeNameInteger brep)) valueA

  Object.UpCastBytes _ -> pure $ overConstantValue1Heterogeneous
    bytesIsInhabited (typeNameBytes brep) castTypeRep (castExpr (typeNameBytes brep)) valueA

  Object.UpCastToSigned _ -> pure $ overConstantValue1Heterogeneous
    integerIsInhabited (typeNameInteger brep) castTypeRep (castExpr (typeNameInteger brep)) valueA

  -- TODO implement this. It's not a simple C cast. It'll be a ternary
  -- expression
  --
  --   (i > MAX_VALUE) ? <intro nothing> : <intro just (<cast> i)>
  Object.CastToSigned -> error "CastToSigned not implemented"

  where

  castTypeRep :: Object.Point.TypeRep a -> Object.Point.TypeRep b
  castTypeRep _ = brep

castExpr :: C.TypeName -> C.Expr -> C.Expr
castExpr tyName expr = C.castExprIsExpr $ C.Cast tyName (C.exprIsCastExpr expr)

arrayIndexExpr :: C.Expr -> C.Expr -> C.Expr
arrayIndexExpr array index = postfixExprIsExpr $ C.PostfixIndex
  (C.exprIsPostfixExpr array)
  index

addValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
addValue = overConstantValue2 const addExpr

addExpr :: C.Expr -> C.Expr -> C.Expr
addExpr x y = C.addExprIsExpr $ C.AddPlus
  (C.exprIsAddExpr  x)
  (C.exprIsMultExpr y)

subtractValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
subtractValue = overConstantValue2 const subtractExpr

subtractExpr :: C.Expr -> C.Expr -> C.Expr
subtractExpr x y = C.addExprIsExpr $ C.AddMin
  (C.exprIsAddExpr  x)
  (C.exprIsMultExpr y)

multiplyValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
multiplyValue = overConstantValue2 const multiplyExpr

multiplyExpr :: C.Expr -> C.Expr -> C.Expr
multiplyExpr x y = C.multExprIsExpr $ C.MultMult
  (C.exprIsMultExpr x)
  (C.exprIsCastExpr y)

divideValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
divideValue = overConstantValue2 const divideExpr

divideExpr :: C.Expr -> C.Expr -> C.Expr
divideExpr x y = C.multExprIsExpr $ C.MultDiv
  (C.exprIsMultExpr x)
  (C.exprIsCastExpr y)

moduloValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
moduloValue = overConstantValue2 const moduloExpr

moduloExpr :: C.Expr -> C.Expr -> C.Expr
moduloExpr x y = C.multExprIsExpr $ C.MultMod
  (C.exprIsMultExpr x)
  (C.exprIsCastExpr y)

negateValue
  :: Value (Constant ('Object.Point.Integer_t sign width))
  -> Value (Constant ('Object.Point.Integer_t sign width))
negateValue = overConstantValue1 id negateExpr

negateExpr :: C.Expr -> C.Expr
negateExpr x = C.unaryExprIsExpr $ C.UnaryOp C.UOMin $
  (C.exprIsCastExpr x)

-- | For the absolute value form, we do a C type cast behind a ternary
-- operator
--
--   (uint<WIDTH>_t) ((x > 0) ? x : -x)
--
absValue
  :: Value (Constant ('Object.Point.Integer_t 'Object.Point.Signed_t   width))
  -> Value (Constant ('Object.Point.Integer_t 'Object.Point.Unsigned_t width))
absValue v = overConstantValue1Integer castf (absExpr tyName) v
  where
  castf :: Object.Point.TypeRep ('Object.Point.Integer_t 'Object.Point.Signed_t   width)
        -> Object.Point.TypeRep ('Object.Point.Integer_t 'Object.Point.Unsigned_t width)
  castf (Object.Point.Integer_r _ wrep) = Object.Point.Integer_r Object.Point.Unsigned_r wrep
  Constant trep = valueType v
  tyName = typeNameInteger trep

-- | The TypeName will be put around the 0 literal. It must be the same type
-- as that of the expression.
--
--   (x > (typeName) 0) ? x : -x
absExpr :: C.TypeName -> C.Expr -> C.Expr
absExpr tyName x = ternaryCondExpr
  (gtExpr x (integerLiteralExpr tyName 0))
  (x)
  (negateExpr x)

-- | first > second
gtExpr :: C.Expr -> C.Expr -> C.Expr
gtExpr l r = C.relExprIsExpr $ C.RelGT (C.exprIsRelExpr l) (C.exprIsShiftExpr r)

-- | (first) ? second : third
ternaryCondExpr :: C.Expr -> C.Expr -> C.Expr -> C.Expr
ternaryCondExpr scrutinee true false = C.condExprIsExpr $ C.Cond
  (C.exprIsLOrExpr scrutinee)
  (true)
  (C.exprIsCondExpr false)

andValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
andValue = overConstantValue2 const andExpr

andExpr :: C.Expr -> C.Expr -> C.Expr
andExpr x y = C.andExprIsExpr $ C.And
  (C.exprIsAndExpr x)
  (C.exprIsEqExpr  y)

orValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
orValue = overConstantValue2 const orExpr

orExpr :: C.Expr -> C.Expr -> C.Expr
orExpr x y = C.orExprIsExpr $ C.Or
  (C.exprIsOrExpr  x)
  (C.exprIsXOrExpr y)

xorValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
xorValue = overConstantValue2 const xorExpr

xorExpr :: C.Expr -> C.Expr -> C.Expr
xorExpr x y = C.xorExprIsExpr $ C.XOr
  (C.exprIsXOrExpr x)
  (C.exprIsAndExpr y)

complementValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t width))
complementValue = overConstantValue1 id complementExpr

complementExpr :: C.Expr -> C.Expr
complementExpr x = C.unaryExprIsExpr $ C.UnaryOp C.UOBNot
  (exprIsCastExpr x)

shiftlValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t 'Object.Point.W_One_t))
  -> Value (Constant ('Object.Point.Bytes_t width))
shiftlValue = overConstantValue2 const shiftlExpr

shiftlExpr :: C.Expr -> C.Expr -> C.Expr
shiftlExpr x y = C.shiftExprIsExpr $ C.ShiftLeft
  (exprIsShiftExpr x)
  (exprIsAddExpr   y)

shiftrValue
  :: Value (Constant ('Object.Point.Bytes_t width))
  -> Value (Constant ('Object.Point.Bytes_t 'Object.Point.W_One_t))
  -> Value (Constant ('Object.Point.Bytes_t width))
shiftrValue = overConstantValue2 const shiftrExpr

shiftrExpr :: C.Expr -> C.Expr -> C.Expr
shiftrExpr x y = C.shiftExprIsExpr $ C.ShiftRight
  (exprIsShiftExpr x)
  (exprIsAddExpr   y)

-- | Writes the integer literal in hex, with an explicit type annotation (a
-- cast).
integerLiteralExpr :: C.TypeName -> Integer -> C.Expr
integerLiteralExpr tyName n = C.castExprIsExpr $ C.Cast tyName (C.exprIsCastExpr literal)
  where
  literal :: C.Expr
  literal = if n < 0
    then C.unaryExprIsExpr $ C.UnaryOp C.UOMin $ C.constIsCastExpr $
      C.ConstInt $ C.IntHex (C.hexConst (fromIntegral (Prelude.abs n))) Nothing
    else C.constIsExpr $
      C.ConstInt $ C.IntHex (C.hexConst (fromIntegral              n))  Nothing

bytesLiteralExpr :: C.TypeName -> Integer -> C.Expr
bytesLiteralExpr = integerLiteralExpr

{-
-- We can indeed use anonymous unions for sum types
-- Can even use anonymous enums!
--
--   struct <sum_name> {
--     enum { ... } tag;
--     union { ... } variant;
--   }
--
-- however, anonymous enum names must be globally unique... so we'll say
--
--   <sum_name>_tag_<n>
--
taggedSumAnonymousUnion :: C.Decln
taggedSumAnonymousUnion = C.Decln (C.DeclnSpecsType tyspec Nothing) Nothing
  where
  tyspec = C.TStructOrUnion $ C.StructOrUnionDecln
    C.Struct (Just structIdent) structDecln

  structDecln = C.StructDeclnCons
    (C.StructDeclnBase tagDecln)
    unionDecln

  -- Just int because I don't want to write out the enum at the moment.
  tagDecln :: C.StructDecln
  tagDecln = C.StructDecln tagSpecQual $ C.StructDeclrBase $ C.StructDeclr $
    C.Declr Nothing (C.DirectDeclrIdent tagIdent)

  tagSpecQual :: C.SpecQualList
  tagSpecQual = C.specQualConst (C.specQualType C.TInt)

  unionDecln :: C.StructDecln
  unionDecln = C.StructDecln unionSpecQual $ C.StructDeclrBase $ C.StructDeclr $
    C.Declr Nothing (C.DirectDeclrIdent variantIdent)

  unionSpecQual :: C.SpecQualList
  unionSpecQual = flip C.SpecQualType Nothing $ C.TStructOrUnion $ C.StructOrUnionDecln
    C.Union Nothing $ C.StructDeclnCons
      (C.StructDeclnBase variantDecln1)
      variantDecln2

  variantDecln1 :: C.StructDecln
  variantDecln1 = C.StructDecln (C.specQualConst (C.specQualType C.TInt)) $ C.StructDeclrBase
    (C.StructDeclr $ C.Declr Nothing $ C.DirectDeclrIdent variantIdent1)

  variantDecln2 :: C.StructDecln
  variantDecln2 = C.StructDecln (C.specQualConst (C.specQualType C.TInt)) $ C.StructDeclrBase
    (C.StructDeclr $ C.Declr Nothing $ C.DirectDeclrIdent variantIdent2)

  structIdent = assertValidStringIdentifier "sum"
  tagIdent = assertValidStringIdentifier "tag"
  variantIdent = assertValidStringIdentifier "variant"
  variantIdent1 = assertValidStringIdentifier "variant_1"
  variantIdent2 = assertValidStringIdentifier "variant_2"
-}

-- Want: a term proving that some type is inhabited. That's more complicated
-- than Not (t :~: Void), because, for instance, a product featuring an
-- uninhabited type is also uninhabited.
-- So it's a conjunction of
--
--   - t is not the empty sum
--   - if t is a product then all of its fields are inhabited
--   - if t is a sum then one of its variants is inhabited

-- TODO move this stuff about Inhabited into a separate module. It's not
-- C-specific at all.

-- | Only inhabited types have a C representation. This includes the empty
-- product (unit type), which is represented by NULL.
data Inhabited t = Inhabited
  { notEmptySum          :: Not (t :~: Object.Point.Sum '[])
  , someInhabitedVariant :: forall vs . (t :~: Object.Point.Sum vs)     -> Some Inhabited vs
  , allInhabitedFields   :: forall fs . (t :~: Object.Point.Product fs) -> All Inhabited fs
  }

integerIsInhabited :: Inhabited ('Object.Point.Integer_t sign width)
integerIsInhabited = Inhabited
  { notEmptySum = \refl -> case refl of {}
  , someInhabitedVariant = \refl -> case refl of {}
  , allInhabitedFields = \refl -> case refl of {}
  }

bytesIsInhabited :: Inhabited ('Object.Point.Bytes_t width)
bytesIsInhabited = Inhabited
  { notEmptySum = \refl -> case refl of {}
  , someInhabitedVariant = \refl -> case refl of {}
  , allInhabitedFields = \refl -> case refl of {}
  }

unitIsInhabited :: Inhabited Object.Point.Unit
unitIsInhabited = Inhabited
  { notEmptySum = \refl -> case refl of {}
  , someInhabitedVariant = \refl -> case refl of {}
  , allInhabitedFields = \refl -> case refl of
      Refl -> All
  }

voidIsUninhabited :: Not (Inhabited Object.Point.Void)
voidIsUninhabited inhabited = notEmptySum inhabited isEmptySum
  where
  isEmptySum :: Object.Point.Void :~: Object.Point.Sum '[]
  isEmptySum = Refl

productIsInhabited :: All Inhabited fields -> Inhabited (Object.Point.Product fields)
productIsInhabited allFieldsInhabited = Inhabited
  { notEmptySum = \refl -> case refl of {}
  , someInhabitedVariant = \refl -> case refl of {}
  , allInhabitedFields = \refl -> case refl of Refl -> allFieldsInhabited
  }

productStillInhabited
  :: Inhabited t
  -> Inhabited (Object.Point.Product       ts)
  -> Inhabited (Object.Point.Product (t ': ts))
productStillInhabited inhabitedT inhabitedTS = productIsInhabited
  (And inhabitedT (allInhabitedFields inhabitedTS Refl))

newtype Uninhabited t = Uninhabited { isUninhabited :: Not (Inhabited t) }

productIsUninhabited
  :: Some Uninhabited fields
  -> Uninhabited (Object.Point.Product fields)
productIsUninhabited (Some (Uninhabited uninhabited)) = Uninhabited $ \inhabited ->
  case allInhabitedFields inhabited Refl of
    And inhabited _ -> uninhabited inhabited
productIsUninhabited (Or uninhabited) = Uninhabited $ 
  productStillUninhabited (isUninhabited (productIsUninhabited uninhabited))

productStillUninhabited
  :: Not (Inhabited (Object.Point.Product       ts))
  -> Not (Inhabited (Object.Point.Product (t ': ts)))
productStillUninhabited uninhabitedTS = \inhabited -> case counterexample inhabited of
  (_, inhabitedTS) -> uninhabitedTS inhabitedTS
  where
  counterexample
    :: forall t ts .
       Inhabited (Object.Point.Product (t ': ts))
    -> (Inhabited t, Inhabited (Object.Point.Product ts))
  counterexample inhabited = case allInhabitedFields inhabited Refl of
    And here there -> (here, productIsInhabited there)

sumIsInhabited :: Some Inhabited variants -> Inhabited (Object.Point.Sum variants)
sumIsInhabited someVariantInhabited = Inhabited
  { notEmptySum = \refl -> case someVariantInhabited of
      Some _ -> case refl of {}
      Or   _ -> case refl of {}
  , someInhabitedVariant = \refl -> case refl of Refl -> someVariantInhabited
  , allInhabitedFields = \refl -> case refl of {}
  }

sumStillUninhabited
  :: Not (Inhabited t)
  -> Not (Inhabited (Object.Point.Sum       ts))
  -> Not (Inhabited (Object.Point.Sum (t ': ts)))
sumStillUninhabited uninhabitedT uninhabitedTS = \inhabited -> case counterexample inhabited of
  Left  l -> uninhabitedT l
  Right r -> uninhabitedTS r
  where
  counterexample
    :: forall t ts .
       Inhabited (Object.Point.Sum (t ': ts))
    -> Either (Inhabited t) (Inhabited (Object.Point.Sum ts))
  counterexample inhabited = case someInhabitedVariant inhabited Refl of
    Some here -> Left  here
    Or  there -> Right (sumIsInhabited there)

sumStillInhabited
  :: Inhabited (Object.Point.Sum       ts)
  -> Inhabited (Object.Point.Sum (t ': ts))
sumStillInhabited inhabitedTS = case someInhabitedVariant inhabitedTS Refl of
  it -> sumIsInhabited (Or it)

maybeIsInhabited :: Inhabited (Object.Point.Maybe t)
maybeIsInhabited = sumIsInhabited (Some unitIsInhabited)

-- | If you select a field from an inhabited product, then that field must be
-- inhabited.
selectorPreservesInhabitedness
  :: Inhabited (Object.Point.Product_t fields)
  -> Object.Selector fields field
  -> Inhabited field
selectorPreservesInhabitedness inh = go (allInhabitedFields inh Refl)
  where
  go :: All Inhabited fields -> Object.Selector fields field -> Inhabited field
  go All sel = case sel of {}
  go (And _ all) (Object.S_There sel) = go all sel
  go (And inh _)  Object.S_Here       = inh



typeNameMeta
  :: Inhabited t
  -> Meta.TypeRep Object.TypeRep (Obj (Constant t))
  -> ValueM C.TypeName
typeNameMeta inhabited (Obj (Constant trep)) = typeNamePoint inhabited trep

typeName
  :: Inhabited t
  -> Object.TypeRep (Constant t)
  -> ValueM C.TypeName
typeName inhabited (Constant t) = typeNamePoint inhabited t

-- | The C TypeName for a point type.
typeNamePoint :: Inhabited t -> Object.Point.TypeRep t -> ValueM C.TypeName
typeNamePoint inhabited trep =
  ctypeInfoToTypeName <$> ctypeInfoPoint inhabited trep

-- | Determines the C representation: a type specifier, and whether it should
-- be a pointer to that spec.
data CTypeInfo = CTypeInfo
  { ctypeSpec :: !C.TypeSpec
  , cPointer  :: !(Maybe C.Ptr)
  }

-- | Always uses a const qualifier.
ctypeInfoToTypeName :: CTypeInfo -> C.TypeName
ctypeInfoToTypeName ctinfo = C.TypeName
  (ctypeInfoSpecQualList ctinfo)
  (fmap C.AbstractDeclr (cPointer ctinfo))

ctypeInfoSpecQualList :: CTypeInfo -> C.SpecQualList
ctypeInfoSpecQualList = C.specQualConst . C.specQualType . ctypeSpec

ctypeInfoToPtr :: CTypeInfo -> Maybe C.Ptr
ctypeInfoToPtr = cPointer


ctypeInfoPoint :: Inhabited t -> Object.Point.TypeRep t -> ValueM CTypeInfo

-- Integers are non-pointers to the canonical integer types uint8_t, int16_t,
-- etc.
ctypeInfoPoint _ it@(Object.Point.Integer_r _ _) = pure $ ctypeInfoInteger it

ctypeInfoPoint _ it@(Object.Point.Bytes_r _) = pure $ ctypeInfoBytes it

ctypeInfoPoint inhabited (Object.Point.Product_r fields)   = ctypeInfoProduct inhabited fields
ctypeInfoPoint inhabited (Object.Point.Sum_r     variants) = ctypeInfoSum     inhabited variants


ctypeInfoInteger :: Object.Point.TypeRep ('Object.Point.Integer_t s w) -> CTypeInfo
ctypeInfoInteger it = CTypeInfo
  { ctypeSpec = typeSpecInteger it
  , cPointer  = Nothing
  }


ctypeInfoBytes :: Object.Point.TypeRep ('Object.Point.Bytes_t w) -> CTypeInfo
ctypeInfoBytes it = CTypeInfo
  { ctypeSpec = typeSpecBytes it
  , cPointer  = Nothing
  }


typeSpecInteger :: Object.Point.TypeRep ('Object.Point.Integer_t s w) -> C.TypeSpec
typeSpecInteger (Object.Point.Integer_r s w) = C.TTypedef
  (C.TypedefName (integerTypeIdent s w))

typeNameInteger :: Object.Point.TypeRep ('Object.Point.Integer_t s w) -> C.TypeName
typeNameInteger = ctypeInfoToTypeName . ctypeInfoInteger

typeSpecBytes :: Object.Point.TypeRep ('Object.Point.Bytes_t w) -> C.TypeSpec
typeSpecBytes (Object.Point.Bytes_r w) = typeSpecInteger
  (Object.Point.Integer_r Object.Point.Unsigned_r w)

typeNameBytes :: Object.Point.TypeRep ('Object.Point.Bytes_t w) -> C.TypeName
typeNameBytes = ctypeInfoToTypeName . ctypeInfoBytes

integerTypeIdent
  :: Object.Point.SignednessRep s
  -> Object.Point.WidthRep w
  -> C.Ident
integerTypeIdent Object.Point.Signed_r   Object.Point.W_One_r   = ident_int8_t
integerTypeIdent Object.Point.Signed_r   Object.Point.W_Two_r   = ident_int16_t
integerTypeIdent Object.Point.Signed_r   Object.Point.W_Four_r  = ident_int32_t
integerTypeIdent Object.Point.Signed_r   Object.Point.W_Eight_r = ident_int64_t
integerTypeIdent Object.Point.Unsigned_r Object.Point.W_One_r   = ident_uint8_t
integerTypeIdent Object.Point.Unsigned_r Object.Point.W_Two_r   = ident_uint16_t
integerTypeIdent Object.Point.Unsigned_r Object.Point.W_Four_r  = ident_uint32_t
integerTypeIdent Object.Point.Unsigned_r Object.Point.W_Eight_r = ident_uint64_t

bytesTypeIdent :: Object.Point.WidthRep w -> C.Ident
bytesTypeIdent = integerTypeIdent Object.Point.Unsigned_r


-- | All we need to know about a product's C representation.
data ProductRepresentation (fields :: [Object.Point.Type]) = ProductRepresentation
  { productCTypeInfo :: !CTypeInfo
  , productIntroduction
      :: forall r .
         Object.Fields r fields
      -> All (Compose Value Constant) fields
      -> ValueM (Value (Constant ('Object.Point.Product_t fields)))
  , productElimination
      :: forall field .
         Object.Point.TypeRep field
      -> Object.Selector fields field
      -> Value (Constant ('Object.Point.Product_t fields))
      -> ValueM (Value (Constant field))
  }

data SumRepresentation (variants :: [Object.Point.Type]) = SumRepresentation
  { sumCTypeInfo :: !CTypeInfo
  , sumIntroduction
      :: forall r .
         Object.Variant r variants
      -> Some (Compose Value Constant) variants
      -> ValueM (Value (Constant ('Object.Point.Sum_t variants)))
  , sumElimination
      :: forall r .
         Object.Cases variants r
      -> Value (Constant ('Object.Point.Sum_t variants))
      -> ValueM (Repr.Val ValueM Value r)
  }


ctypeInfoProduct
  :: Inhabited (Object.Point.Product fields)
  -> All Object.Point.TypeRep fields
  -> ValueM CTypeInfo
ctypeInfoProduct inhabited fields =
  productCTypeInfo <$> productRepresentation inhabited fields


-- | If you select any of the fields of a product which normalizes to unit,
-- then the thing selected also normalizes to unit.
selectingFromUnitIsUnit
  :: NonUnitFields fields '[]
  -> Object.Selector fields r
  -> NormalizedType r ('Object.Point.Product_t '[])
selectingFromUnitIsUnit NonUnitNil sel = case sel of {}
selectingFromUnitIsUnit (NonUnitAbsorb _ _ rec) (Object.S_There sel) =
  selectingFromUnitIsUnit rec sel
selectingFromUnitIsUnit (NonUnitAbsorb nty isUnit _) Object.S_Here = case isUnit of
  Refl -> nty


-- | A non-normalized value can be made into a normalized value without
-- actually changing the C representation, because we _always_ represent them
-- in normalized form. All we do here is change the type rep (the C.TypeName
-- in the value is always for the normalized form).
--
-- This is just an axiom, GHC can't know anything substantial about it because
-- the C representations do not have rich type information.
toNormalRepresentation
  :: NormalizedType a b
  -> Value (Constant a)
  -> Value (Constant b)
toNormalRepresentation nty v = value (Constant ty) defn
  where
  Constant trep = valueType v
  ty = normalizedTypeRep nty trep
  defn = case valueDefn v of
    ValueConstant inhabited tyName expr -> ValueConstant
      (normalizationPreservesInhabitedness nty inhabited)
      tyName
      expr

-- | See 'toNormalRepresentation'. Values are always represented in their
-- normalized form.
fromNormalRepresentation
  :: NormalizedType a b
  -> Value (Constant b)
  -> Value (Constant a)
fromNormalRepresentation nty v = value (Constant ty) defn
  where
  Constant trep = valueType v
  ty = typeRepFromNormalized nty trep
  defn = case valueDefn v of
    ValueConstant inhabited tyName expr -> ValueConstant
      (inhabitedFromNormalized nty inhabited)
      tyName
      expr


-- | This is intended to completely encapsulate the representation of products.
--
-- In here there are definitions which aren't kept in check by GHC, because we
-- drop down to the C representation, which is of course not annotated with
-- our type domain.
productRepresentation
  :: forall fields .
     Inhabited (Object.Point.Product fields)
  -> All Object.Point.TypeRep fields
  -> ValueM (ProductRepresentation fields)

productRepresentation inhabited fields = case normalizedType trep of

  Of nty -> case nty of

    NormalizedProduct nonUnitFields normP -> case normP of

      -- The unit (empty product) is represented by (void *const restrict) NULL.
      UnitIsNormal -> pure $ ProductRepresentation
        { productCTypeInfo = unitCTypeInfo

          -- Introduction of the empty product is the literal NULL.
        , productIntroduction = \_ _ -> pure $ unitRepresentation trep nty

          -- This is a weird one. While you cannot select from an empty product,
          -- you _can_ of course select from a product which normalizes to the
          -- empty product. But, it's guaranteed that you'll get another
          -- empty product... and so... we can simply give back this
          -- representation.
          --
          -- What we know is that whatever you select, it _normalizes_ to
          -- unit. So we can use the selector to find the thing, and also
          -- obtain proof that it normalizes to unit. And then, since
          -- normalization does not change representation, we can just "cast"
          -- to/from.
          --
        , productElimination = \_ selector value -> pure $
            let rNormalizesToUnit = selectingFromUnitIsUnit nonUnitFields selector
            in  fromNormalRepresentation rNormalizesToUnit (toNormalRepresentation nty value)
        }

      -- A product which normalizes to a single non-unit thing is represented
      -- by that thing's representation.
      NormalizedProductSingleton -> do
        let ntyRep = normalizedTypeRep nty trep
        -- TODO should have a function that we can call to get the type info
        -- of an already normalized type, so we don't have to renormalize it
        -- (we have an idempotency proof anyway so it's fine for correctness).
        ctypeInfo <- ctypeInfoPoint (normalizationPreservesInhabitedness nty inhabited) ntyRep
        pure $ ProductRepresentation
          { productCTypeInfo = ctypeInfo

            -- For introduction, pick out the 1 and only 1 field which has the
            -- same representation as the product.
          , productIntroduction = \fields vals -> pure $
              fromNormalRepresentation nty (introProductSingleton nonUnitFields fields vals)

            -- For elimination, only the selector which hits the 1 and only 1
            -- non unit field will give a non unit.
          , productElimination = \trepResult selector value -> pure $
              elimProductSingleton nonUnitFields trepResult selector
                (toNormalRepresentation nty value)

          }

      -- Here we take all of the components (There are at least 2) and
      -- we use ctypeInfoPoint on each of them to come up with type names,
      -- required in order to make the struct declaration.
      -- We also generate a new identifier for this product.
      NormalizedProductProper -> do
        let ntyRep = normalizedTypeRep nty trep
        -- Important to do this here before withCompositeTypeId, for we require
        -- that if a product A contains another product B, then B has a lower
        -- serial number than A. This property is used to ensure that the
        -- type declarations in the C translation unit are properly ordered.
        components <- properProductComponents
          nonUnitFields
          fields
          (allInhabitedFields inhabited Refl)
        -- Check whether the _normalized_ type rep of this product has already
        -- been seen. If not, we give its representation, so that it can be
        -- recovered from the ValueM state and made into a declaration in the
        -- translation unit.
        --
        -- NB: this part is idempotent, we'll always get the same compId for
        -- any two types which have the same normalized type.
        compId <- withCompositeTypeId (Object.Point.SomeTypeRep ntyRep) $ \compId -> do
          let !decln = properProductStructDecln compId components
          pure $ decln NE.:| []
        let ctypeInfo = properProductCTypeInfo compId
        pure $ ProductRepresentation
          { productCTypeInfo = ctypeInfo

            -- Makes a struct initializer using the (normal) representations
            -- of the non-unit fields given.
          , productIntroduction = \fields vals -> pure $
              introProductProper trep inhabited nonUnitFields ntyRep ctypeInfo fields vals

            -- Here we use the selector to get the CTypeInfo and inhabitedness
            -- proof for the resulting field.
          , productElimination = \trepResult selector value -> do
              let inh = selectorPreservesInhabitedness inhabited selector
              ctypeInfoField <- ctypeInfoPoint inh trepResult
              pure $ elimProductProper trepResult inh ctypeInfoField nonUnitFields selector value
          }

  where
 
  trep = Object.Point.Product_r fields

  unitRepresentation
    :: Object.Point.TypeRep t
    -> NormalizedType t ('Object.Point.Product_t '[])
    -> Value (Constant t)
  unitRepresentation trep nty = constantValue_
    (Obj (Constant trep))
    (inhabitedFromNormalized nty unitIsInhabited)
    (ctypeInfoToTypeName unitCTypeInfo)
    (C.identIsExpr C.ident_NULL)


  unitCTypeInfo = CTypeInfo
    { ctypeSpec = C.TVoid
    , cPointer  = Just $ C.PtrBase $ Just $ C.TypeQualCons
        (C.TypeQualBase C.QConst)
        C.QRestrict
    }


  -- C type information for a proper product: it's a struct, named using the
  -- given CompositeTypeId.
  properProductCTypeInfo
    :: CompositeTypeId
    -> CTypeInfo
  properProductCTypeInfo compId = CTypeInfo
    { ctypeSpec = C.TStructOrUnion $ C.StructOrUnionForwDecln C.Struct
        (properProductStructIdentifier compId)
    , cPointer = Nothing
    }


  -- TODO define this. We'll have to include it into the ValueM state so that
  -- it gets declared when the translation unit is written out.
  properProductStructDecln
    :: CompositeTypeId
    -> NonEmpty CTypeInfo -- The fields
    -> C.Decln
  properProductStructDecln compId typeInfos = flip C.Decln Nothing $ C.DeclnSpecsType specs Nothing
    where
    specs = C.TStructOrUnion (C.StructOrUnionDecln C.Struct (Just ident) structDeclnList)
    ident = properProductStructIdentifier compId
    structDeclnList = structFields (NE.zip structFieldNames typeInfos)

  structFields :: NonEmpty (C.Ident, CTypeInfo) -> C.StructDeclnList
  structFields ((ident, info) NE.:| []) = C.StructDeclnBase
    (C.StructDecln (ctypeInfoSpecQualList info) (C.StructDeclrBase (C.StructDeclr (C.Declr (ctypeInfoToPtr info) (C.DirectDeclrIdent ident)))))
  structFields ((ident, info) NE.:| (x:xs)) = C.StructDeclnCons
    (structFields (x NE.:| xs))
    (C.StructDecln (ctypeInfoSpecQualList info) (C.StructDeclrBase (C.StructDeclr (C.Declr (ctypeInfoToPtr info) (C.DirectDeclrIdent ident)))))

  properProductStructIdentifier :: CompositeTypeId -> C.Ident
  properProductStructIdentifier = assertValidStringIdentifier . ("field_" ++) . show . getCompositeTypeId

  -- | Field names for a struct which represents a proper product. They are
  -- field_<n> where n increases from 0 as the product components go from left
  -- to right.
  structFieldNames :: NonEmpty C.Ident
  structFieldNames = NE.fromList $
    (assertValidStringIdentifier . ("field_" ++) . show) <$> ([0..] :: [Integer])


  introProductSingleton
    :: forall r fields nonUnit .
       NonUnitFields fields '[nonUnit]
    -> Object.Fields r fields
    -> All (Compose Value Constant) fields
    -> Value (Constant nonUnit)
  introProductSingleton nu Object.F_All          _              = case nu of {}
  introProductSingleton nu (Object.F_And fields) (And val vals) = case nu of
    -- The value is unit so we just ignore it.
    NonUnitAbsorb _ _ rec -> introProductSingleton rec fields vals
    NonUnitCons nty _ _ -> toNormalRepresentation nty (getCompose val)
 
  -- The selector picks out units for everything which is the not the sole
  -- non-unit field.
  elimProductSingleton
    :: forall field fields nonUnit .
       NonUnitFields fields '[nonUnit]
    -> Object.Point.TypeRep field
    -> Object.Selector fields field
    -> Value (Constant nonUnit) -- ^ Has the same representation as a product of the
                                -- fields, because those fields normalize to a singleton.
    -> Value (Constant field)

  elimProductSingleton (NonUnitAbsorb nty isUnit _) trep Object.S_Here _ = case isUnit of
    Refl -> unitRepresentation trep nty
  elimProductSingleton nu@(NonUnitCons nty _ _)     trep Object.S_Here val =
    fromNormalRepresentation nty val
  elimProductSingleton (NonUnitAbsorb _ _ rec) trep (Object.S_There sel) val =
    elimProductSingleton rec trep sel val
  -- We pass the only non-unit, so it's unit
  elimProductSingleton (NonUnitCons _ _ rec) trep (Object.S_There sel) val =
    mustBeUnit rec sel trep

    where

    mustBeUnit
      :: forall field fields .
         NonUnitFields fields '[]
      -> Object.Selector fields field
      -> Object.Point.TypeRep field
      -> Value (Constant field)
    mustBeUnit NonUnitNil it _ = case it of {}
    mustBeUnit (NonUnitAbsorb _ _ rec) (Object.S_There sel) trep = 
      mustBeUnit rec sel trep
    mustBeUnit (NonUnitAbsorb nty isUnit _) Object.S_Here trep = case isUnit of
      Refl -> unitRepresentation trep nty


  -- Creates a struct literal with the given TypeName.
  introProductProper
    :: forall r fields a b c .
       Object.Point.TypeRep ('Object.Point.Product_t fields)
    -> Inhabited ('Object.Point.Product_t fields)
    -> NonUnitFields fields (a ': b ': c)
    -> Object.Point.TypeRep ('Object.Point.Product_t (a ': b ': c))
    -> CTypeInfo
    -> Object.Fields r fields
    -> All (Compose Value Constant) fields
    -> Value (Constant ('Object.Point.Product_t fields))
  introProductProper trep inh nonUnitFields ntyRep ctypeInfo _ values = constantValue
    (Obj (Constant trep))
    inh
    (ctypeInfoToTypeName ctypeInfo)
    (properProductStructInitializer (ctypeInfoToTypeName ctypeInfo)
      (NE.zip structFieldNames (properProductInits nonUnitFields values))
    )


  elimProductProper
    :: forall fields field a b c .
       Object.Point.TypeRep field
    -> Inhabited field
    -> CTypeInfo -- ^ For the field
    -> NonUnitFields fields (a ': b ': c)
    -> Object.Selector fields field
    -> Value (Constant ('Object.Point.Product_t fields))
    -> Value (Constant field)
  elimProductProper trep inh ctypeInfo nonUnitFields selector val =
    selectProperProductField
      nonUnitFields trep inh ctypeInfo selector
      (valueConstantExpr val) structFieldNames

  -- Selects the field according to the selector. We need the TypeRep, Inhabited
  -- proof, and CTypeInfo for the field, since if it's a non unit then we have
  -- to construct a value for it. If it's unit then we already have this
  -- information.
  selectProperProductField
    :: forall fields field nonUnits .
       NonUnitFields fields nonUnits
    -> Object.Point.TypeRep field
    -> Inhabited field
    -> CTypeInfo -- ^ For `field`
    -> Object.Selector fields field
    -> LocalM C.Expr    -- ^ Value to select from
    -> NonEmpty C.Ident -- ^ Field names. Is infinite length.
    -> Value (Constant field)

  selectProperProductField _ _ _ _ _ _ (_ NE.:| []) = error "selectProperProductField: impossible case"

  -- A product elimination always selects _some_ field.
  selectProperProductField NonUnitNil _ _ _ sel _ _ = case sel of {}

  -- Cases which do not recurse: either it's a unit (selected and absorb)
  -- or it's a non unit and we have to do a struct field access.

  selectProperProductField (NonUnitAbsorb nty isUnit _) trep _ _ Object.S_Here _   _ =
    case isUnit of
      Refl -> unitRepresentation trep nty

  selectProperProductField (NonUnitCons   nty _      _) trep inh ctypeInfo Object.S_Here val (ident NE.:| _) =
    constantValue
      (Obj (Constant trep))
      inh
      (ctypeInfoToTypeName ctypeInfo)
      (properProductStructFieldSelector val ident)

  -- Recursive cases: skip over non-selected fields, advancing the field
  -- identifier only if that field is not unit.

  selectProperProductField (NonUnitCons   _ _ rec) trep inh ctypeInfo (Object.S_There sel) val (_ NE.:| (x:xs)) =
    selectProperProductField rec trep inh ctypeInfo sel val (x NE.:| xs)

  selectProperProductField (NonUnitAbsorb _ _ rec) trep inh ctypeInfo (Object.S_There sel) val idents =
    selectProperProductField rec trep inh ctypeInfo sel val idents


  -- Since we represent proper products by structs, and they are _not_
  -- represented by pointers, we use the postfix dot accessor.
  properProductStructFieldSelector :: LocalM C.Expr -> C.Ident -> LocalM C.Expr
  properProductStructFieldSelector exprM ident = do
    expr <- exprM
    pure $ C.postfixExprIsExpr $ C.PostfixDot
      (C.exprIsPostfixExpr expr)
      ident


  properProductStructInitializer
    :: C.TypeName
    -> NonEmpty (C.Ident, LocalM C.Expr)
    -> LocalM C.Expr
  properProductStructInitializer tyName inits = do
    -- Traverse the identifier expression pairs to make them into things required
    -- for the C.InitList
    initItems :: NonEmpty (C.Design, C.Init) <- flip traverse inits $ \(ident, exprM) -> do
      expr <- exprM
      pure ( C.Design (C.DesigrBase (C.DesigrIdent ident))
           , C.InitExpr (C.exprIsAssignExpr expr)
           )
    let initList = properProductStructInitList initItems
    pure $ C.postfixExprIsExpr $ C.PostfixInits tyName initList

  properProductStructInitList :: NonEmpty (C.Design, C.Init) -> C.InitList
  properProductStructInitList ((design, init) NE.:| []) =
    C.InitBase (Just design) init
  properProductStructInitList ((design, init) NE.:| (x:xs)) =
    C.InitCons (properProductStructInitList (x NE.:| xs)) (Just design) init

  -- Takes just the non unit expressions.
  properProductInits
    :: forall fields a b .
       NonUnitFields fields (a ': b)
    -> All (Compose Value Constant) fields
    -> NonEmpty (LocalM C.Expr)
  properProductInits (NonUnitAbsorb _ _ rec) (And _ all) =
    properProductInits rec all
  properProductInits (NonUnitCons _ _ rec) (And val all) =
    valueConstantExpr (getCompose val) NE.:| properProductInits_ rec all

  properProductInits_
    :: forall fields anything .
       NonUnitFields fields anything
    -> All (Compose Value Constant) fields
    -> [LocalM C.Expr]
  properProductInits_ NonUnitNil All = []
  properProductInits_ (NonUnitAbsorb _ _ rec) (And _   all) =
    properProductInits_ rec all
  properProductInits_ (NonUnitCons _ _ rec)   (And val all) =
    valueConstantExpr (getCompose val) : properProductInits_ rec all


  -- Compute the CTypeInfo for each of the non unit fields.
  properProductComponents
    :: forall fields a b .
       NonUnitFields fields (a ': b)
    -> All Object.Point.TypeRep fields
    -> All Inhabited fields
    -> ValueM (NonEmpty CTypeInfo)

  properProductComponents
      (NonUnitAbsorb _ _ rec)
      (And _ fields)
      (And _ inhs) =
    properProductComponents rec fields inhs

  properProductComponents
      (NonUnitCons nty isNotUnit rec)
      (And trep treps)
      (And inh inhs) = do
    let ntyRep = normalizedTypeRep nty trep
    info <- ctypeInfoPoint (normalizationPreservesInhabitedness nty inh) ntyRep
    infos <- properProductComponents_ rec treps inhs
    pure $ info NE.:| infos


  properProductComponents_
    :: forall fields a .
       NonUnitFields fields a
    -> All Object.Point.TypeRep fields
    -> All Inhabited fields
    -> ValueM [CTypeInfo]

  properProductComponents_ NonUnitNil All All = pure []

  properProductComponents_
      (NonUnitAbsorb _ _ rec)
      (And _ fields)
      (And _ inhs) =
    properProductComponents_ rec fields inhs

  properProductComponents_
      (NonUnitCons nty isNotUnit rec)
      (And trep treps)
      (And inh inhs) = do
    let ntyRep = normalizedTypeRep nty trep
    info <- ctypeInfoPoint (normalizationPreservesInhabitedness nty inh) ntyRep
    infos <- properProductComponents_ rec treps inhs
    pure $ info : infos


ctypeInfoSum
  :: Inhabited (Object.Point.Sum variants)
  -> All Object.Point.TypeRep variants
  -> ValueM CTypeInfo
ctypeInfoSum inhabited variants =
  sumCTypeInfo <$> sumRepresentation inhabited variants

sumRepresentation
  :: Inhabited (Object.Point.Sum variants)
  -> All Object.Point.TypeRep variants
  -> ValueM (SumRepresentation variants)
sumRepresentation inhabited variants = undefined
