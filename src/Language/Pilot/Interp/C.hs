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
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
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

-- | Evaluates a constant value and elaborates it to a C function called
-- "step". Useful for debugging / toying around.
stepFunctionConstant :: Repr.Repr ValueM Value (Obj (Constant t)) -> C.FunDef
stepFunctionConstant repr = elaborateConstantToFunction ident v
  where
  v = Repr.fromObject (runValueM_ (Repr.getRepr repr))
  !ident = assertValidStringIdentifier "step"

-- | Same as 'stepFunctionConstant' but for a 0-prefix Varying.
stepFunctionVarying :: Repr.Repr ValueM Value (Obj (Varying 'Z t)) -> C.FunDef
stepFunctionVarying repr = elaborateVaryingToFunction ident v
  where
  v = Repr.fromObject (runValueM_ (Repr.getRepr repr))
  !ident = assertValidStringIdentifier "step"

-- | Make the translation unit and write it to a file.
elaborateProgramAndWrite
  :: forall n t .
     IO.FilePath
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Varying n t))))
  -> IO (Either ProgramError ())
elaborateProgramAndWrite fileName repr = case elaborateProgram repr of
  Left err -> pure (Left err)
  Right tu -> IO.writeFile fileName (prettyPrintC tu) >> pure (Right ())

-- | Elaborate a program to a C translation unit. This is:
--
-- - [ ] Type declarations for every compound type needed
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
     Repr.Repr ValueM Value (Obj (Program (Obj (Varying n t))))
  -> Either ProgramError C.TransUnit
elaborateProgram repr = fmap (mkTransUnit pstate) result
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
    Repr.fromObject <$> valueMInProgramM (Repr.getRepr repr)

  (result, pstate) = runProgramM progM pureState

mkTransUnit :: forall n t . ProgramState -> Value (Varying n t) -> C.TransUnit
mkTransUnit pstate v =
  declns
  `appendTransUnitL`
  (appendTransUnit initFun stepFun)

  where

  -- TODO
  -- this is type declarations
  -- followed by static array declarations
  -- followed by extern I/O declarations
  declns :: Maybe C.TransUnit
  declns =
    transUnitFromDeclns typeDeclns
    `C.appendTransUnitLR`
    transUnitFromDeclns externDeclns
    `C.appendTransUnitLR`
    transUnitFromDeclns knotDeclns

  -- TODO
  typeDeclns :: [C.Decln]
  typeDeclns = []

  externIOs :: [ExternIO]
  externIOs = Map.elems (impure_state_extern_io (program_state_impure_state pstate))

  externDeclns :: [C.Decln]
  externDeclns = concatMap externIOStaticDeclns externIOs

  copyExternInputs, copyExternOutputs :: [LocalM ()]
  copyExternInputs = mapMaybe externIOCopyInput externIOs
  copyExternOutputs = mapMaybe externIOCopyOutput externIOs

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

  (_, ty) = valueVaryingType v
  tyName = typeName (Constant ty)

  varyingExpr :: LocalM C.Expr
  VCons varyingExpr _ = valueVaryingExprs v

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
    retIdent <- makeBinding ty cexpr
    -- Copy outputs to their extern locations.
    sequence copyExternOutputs
    -- The static array indices must advance now, so that on the next frame
    -- the streams will have appeared to have moved forward.
    updateStaticArrayIndices
    pure $ C.identIsExpr retIdent

  !identStep = assertValidStringIdentifier "step"
  !identInit = assertValidStringIdentifier "init"

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
  -> LocalM C.Expr
  -> ValueM (Value (Constant t))
makeIdempotent trep lm = do
  binderId <- genBinderId
  pure $ constantValue (Obj (Constant trep)) $ LocalM $ do
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
            ident <- unLocalM $ makeBinding trep cexpr
            -- Even though makeBinding has added the block item, we must also
            -- update the BinderId map.
            unLocalM $ addBinding binderId ident cexpr
            pure $ C.identIsExpr ident

-- | Makes an identifier for the binding and adds the block item to do the
-- assignment.
makeBinding :: Object.Point.TypeRep t -> C.Expr -> LocalM C.Ident
makeBinding trep cexpr = do
  ident <- genFreshName
  let !bm = C.blockItemInitialize (typeNameMeta (Obj (Constant trep))) ident cexpr
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
elaborateConstantToFunction :: C.Ident -> Value (Constant t) -> C.FunDef
elaborateConstantToFunction funName v = elaborateToFunction funName tyName (Just <$> lm)
  where
  ty = valueConstantType v
  tyName = typeName (Constant ty)
  lm = valueConstantExpr v

elaborateVaryingToFunction :: C.Ident -> Value (Varying Z t) -> C.FunDef
elaborateVaryingToFunction funName v = elaborateToFunction funName tyName (Just <$> lm)
  where
  (_, ty) = valueVaryingType v
  tyName = typeName (Constant ty)
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


-- |
-- = Compound type representations
--
-- It would be nice to normalize sum and product types so that they are either
-- - Void
-- - Unit
-- - A product of 2 or more non-void and non-unit types
-- - A sum of 2 or more non-void and non-unit types
--
-- - Void and Unit are represented by NULL and have type void*.
--   Unit introduction can just give NULL, since it can never be eliminated.
--   Void elimination can generate no code, since it can never be introduced.
--
-- - Singleton sums and products are represented by the underlying types.
-- - 

-- | This is the state that must accompany a C Expr in order to give it meaning.
-- The expression may make reference to names assumed to be bound in the local
-- scope, and to names assumed to be declared by C type declarations.
-- Values which include sum elimination require switch statements; these are
-- tracked here, as a list of C BlockItems.
data PureState = PureState
  { -- | For non-empty sum and product types, we need enum, union, and struct
    -- declarations, and we need to know the names of these things and of
    -- their constructors.
    pure_state_type_decls  :: !() -- (Map (Some Object.Point.TypeRep) ())
    -- | A "global" counter to identify let bindings.
    -- It is used to generate `LetBindId`, which are used as keys in the
    -- `LocalM` state.
  , pure_state_binder_id_gen :: !BinderIdGen
  }

initialPureState :: PureState
initialPureState = PureState
  { pure_state_type_decls = ()
  , pure_state_binder_id_gen = Gen 0
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
    -- | Identifier of the extern storage class name.
  , extern_io_ident :: !C.Ident
  , extern_io_defn  :: !ExternIODefn
    -- TODO says what the user-facing type is and how to marshall it to/from
    -- the internal type.
  --, extern_io_meta :: !()
  }

-- | Static declarations required for an `ExternIO`.
externIOStaticDeclns :: ExternIO -> [C.Decln]
externIOStaticDeclns (ExternIO trep ident defn) = case defn of
  ExternOutput _ -> [externOutputStaticDecln trep ident]
  ExternInput (ExternInputData i) ->
    let (a, b) = externInputStaticDeclns trep ident i in [a, b]

-- | For extern outputs, there is just one declaration: an extern of the
-- appropriate type.
externOutputStaticDecln :: Object.Point.TypeRep t -> C.Ident -> C.Decln
externOutputStaticDecln trep ident = C.Decln specs (Just initList)
  where
  specs = C.DeclnSpecsStorage C.SExtern (Just (C.specQualListToDeclnSpecs tySpecs))
  initList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent ident)
  mPtr = C.mAbstractDeclrToPtr mAbsDeclr
  C.TypeName tySpecs mAbsDeclr = typeName (Constant trep)

externInputStaticDeclns :: Object.Point.TypeRep t -> C.Ident -> C.Ident -> (C.Decln, C.Decln)
externInputStaticDeclns trep ident identCopy = (externDecln, copyDecln)
  where
  externDecln = C.Decln (C.DeclnSpecsStorage C.SExtern (Just specs)) (Just externInitList)
  copyDecln   = C.Decln                                      specs   (Just copyInitList)

  externInitList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent ident)
  copyInitList = C.InitDeclrBase $ C.InitDeclr $ C.Declr mPtr (C.DirectDeclrIdent identCopy)

  specs = C.specQualListToDeclnSpecs tySpecs
  mPtr = C.mAbstractDeclrToPtr mAbsDeclr
  C.TypeName tySpecs mAbsDeclr = typeName (Constant trep)

-- | Elaborates to the LocalM which copies the extern input to its copy
-- location. Gives Nothing if the ExternIO is an output.
externIOCopyInput :: ExternIO -> Maybe (LocalM ())
externIOCopyInput (ExternIO trep ident defn) = case defn of
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
externIOCopyOutput (ExternIO trep ident defn) = case defn of
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
  -> Repr.Repr ValueM Value (Obj (Program (Obj (Varying Z t))))
externInput name trep = Repr.object $ programValue vrep $ do

  (ident, identCopy) <- ProgramM $ do
    let fullName = "input_" ++ name
        fullNameCopy = "input_copy_" ++ name
    ident <- assertValidStringIdentifierM (Except.throwE (InvalidExternName name)) fullName
    -- If input_<name> is valid, so is input_copy_<name>
    let !identCopy = assertValidStringIdentifier fullNameCopy
    pure (ident, identCopy)
  
  let inputData :: ExternInputData
      inputData = ExternInputData identCopy
  
      defn :: ExternIODefn
      defn = ExternInput inputData
  
      externIO = ExternIO
        { extern_io_type  = trep
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
      value = varyingValue_ vrep (VCons cexpr VNil)

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
  obj <- valueMInProgramM $ Repr.getRepr stream

  let outputData :: ExternOutputData
      outputData = case valueVaryingExprs (Repr.fromObject obj) of
        VCons it VNil -> ExternOutputData it

      defn :: ExternIODefn
      defn = ExternOutput outputData

      externIO = ExternIO
        { extern_io_type  = trep
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

  go :: StaticVaryingNames r -> [C.Decln]
  go (StaticVaryingNamesTied nrep trep names) =
    [ arrayDeclaration (static_array_name names) nrep trep
    , indexDeclaration (static_array_index_name names)
    ]
  go (StaticVaryingNamesTie nrep trep names rec) =
    [ arrayDeclaration (static_array_name names) nrep trep
    , indexDeclaration (static_array_index_name names)
    ] ++ go rec

  arrayDeclaration :: C.Ident -> NatRep ('S n) -> Object.Point.TypeRep t -> C.Decln
  arrayDeclaration ident sizeLessOne trep =
    let C.TypeName specQualList mAbsDeclr = typeName (Constant trep)

        specs = C.specQualListToDeclnSpecs specQualList

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
  go (Object.Tied _ _) (StaticVaryingNamesTied (S_Rep _) _ names) (StaticVaryingInitsTied arep vec) = do
    cexprs <- vecSequence vec
    initOne names cexprs
  go (Object.Tie _ _ recKnot) (StaticVaryingNamesTie (S_Rep _) _ names recNames) (StaticVaryingInitsTie arep vec recInits) = do
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
  go (Object.Tied _ _) (StaticVaryingNamesTied nrep _ names) (StaticVaryingNextsTied _ lm) = do
    cexpr <- lm
    updateOne nrep names cexpr
  go (Object.Tie _ _ kn) (StaticVaryingNamesTie  nrep _ names recNames) (StaticVaryingNextsTie _ lm recNexts) = do
    cexpr <- lm
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
  go (StaticVaryingNamesTied nrep _ names) = updateOne nrep names
  go (StaticVaryingNamesTie nrep _ names rec) = do
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
    :: Object.Point.TypeRep i
    -> Vec (S n) (LocalM C.Expr)
    -> StaticVaryingInits (Obj (Varying n a)) (Object.Vector ('S n) (Obj (Constant i)))
  StaticVaryingInitsTie
    :: Object.Point.TypeRep i
    -> Vec (S n) (LocalM C.Expr)
    -> StaticVaryingInits ss is
    -> StaticVaryingInits (Obj (Varying n a) :* ss) (Object.Vector ('S n) (Obj (Constant i)) :* is)

staticVaryingInits
  :: forall s t i r .
     Object.Knot s t i r
  -> Repr.Repr ValueM Value i
  -> ValueM (StaticVaryingInits s i)

staticVaryingInits (Object.Tied nrep arep) repr = do
  vs <- staticVaryingInitVector arep nrep repr
  pure $ StaticVaryingInitsTied arep vs

staticVaryingInits (Object.Tie nrep arep knotSig) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  vs <- staticVaryingInitVector arep nrep l
  vss <- staticVaryingInits knotSig r
  pure $ StaticVaryingInitsTie arep vs vss


staticVaryingInitVector
  :: forall n a .
     Object.Point.TypeRep a
  -> NatRep ('S n)
  -> Repr.Repr ValueM Value (Object.Vector ('S n) (Obj (Constant a)))
  -> ValueM (Vec ('S n) (LocalM C.Expr))

staticVaryingInitVector arep (S_Rep Z_Rep) repr = do
  v <- Repr.fromObject <$> Repr.getRepr repr
  pure $ VCons (valueConstantExpr v) VNil

staticVaryingInitVector arep (S_Rep nrep@(S_Rep _)) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  v <- Repr.fromObject <$> Repr.getRepr l
  vs <- staticVaryingInitVector arep nrep r
  pure $ VCons (valueConstantExpr v) vs


staticVaryingNexts
  :: forall s t i r .
     Object.Knot s t i r
  -> Repr.Repr ValueM Value t
  -> ValueM (StaticVaryingNexts t)

staticVaryingNexts (Object.Tied _ arep) repr = do
  lexpr <- staticVaryingNext arep repr
  pure $ StaticVaryingNextsTied arep lexpr

staticVaryingNexts (Object.Tie _ arep knotSig) repr = do
  (l, r) <- Repr.fromProduct <$> Repr.getRepr repr
  lexpr <- staticVaryingNext arep l
  lexprs <- staticVaryingNexts knotSig r
  pure $ StaticVaryingNextsTie arep lexpr lexprs


staticVaryingNext
  :: forall a .
     Object.Point.TypeRep a
  -> Repr.Repr ValueM Value (Obj (Varying Z a))
  -> ValueM (LocalM C.Expr)

staticVaryingNext arep repr = do
  v <- Repr.fromObject <$> Repr.getRepr repr
  case valueVaryingExprs v of
    VCons it VNil -> pure it


data StaticVaryingNexts (t :: Meta.Type Object.Type) where
  StaticVaryingNextsTied
    :: Object.Point.TypeRep t
    -> LocalM C.Expr
    -> StaticVaryingNexts (Obj (Varying Z t))
  StaticVaryingNextsTie
    :: Object.Point.TypeRep t
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
    -> StaticArrayNames
    -> StaticVaryingNames (Obj (Varying ('S n) a))
  StaticVaryingNamesTie
    :: NatRep ('S n)
    -> Object.Point.TypeRep a
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
  -> ProgramM (StaticVaryingNames r)
genStaticVaryingNames (Obj (Varying _ arep))       (Object.Tied nrep _)    = do
  names <- genStaticArrayNames
  pure $ StaticVaryingNamesTied nrep arep names
genStaticVaryingNames (Obj (Varying _ arep) :* rs) (Object.Tie  nrep _ kn) = do
  names <- genStaticArrayNames
  rec <- genStaticVaryingNames rs kn
  pure $ StaticVaryingNamesTie nrep arep names rec

-- | Use the names to get values of varyings. This is done by taking the
-- array name indexed at the array index value, plus each of the valid offsets,
-- modulo the size of the array.
staticVaryingValues :: StaticVaryingNames r -> Repr.Repr ValueM Value r

staticVaryingValues (StaticVaryingNamesTie  nrep trep names rec) = Repr.product
  ( Repr.object (varyingValue_ (Obj (Varying nrep trep)) (staticArrayIndexExprs names arraySize nrep))
  , staticVaryingValues rec
  )
  where
  arraySize = natToIntegral nrep + 1

staticVaryingValues (StaticVaryingNamesTied nrep trep names) = Repr.object $
  varyingValue_ (Obj (Varying nrep trep)) (staticArrayIndexExprs names arraySize nrep)
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
shiftedStaticVaryingValues (Object.Tied _ _)   (StaticVaryingNamesTied (S_Rep nrep) trep names)     = Repr.object $
  varyingValue_ (Obj (Varying nrep trep)) (staticArrayIndexExprs names arraySize nrep)
  where
  arraySize = natToIntegral nrep + 2

shiftedStaticVaryingValues (Object.Tie _ _ kn) (StaticVaryingNamesTie  (S_Rep nrep) trep names rec) = Repr.product
  ( Repr.object (varyingValue_ (Obj (Varying nrep trep)) (staticArrayIndexExprs names arraySize nrep))
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
-- etc.).
data Value (t :: Object.Type) = Value
  { valueType :: Object.TypeRep t
  , valueDefn :: ValueDefn t
  }

data ValueDefn (t :: Object.Type) where
  ValueConstant ::            (LocalM C.Expr) -> ValueDefn (Constant   t)
  -- | A varying of prefix size 0 has 1 expression (the current, first/oldest
  -- value).
  ValueVarying  :: Vec ('S n) (LocalM C.Expr) -> ValueDefn (Varying  n t)
  ValueProgram  :: ProgramM (Repr.Repr ValueM Value t) -> ValueDefn (Program t)

valueConstantType :: Value (Constant t) -> Object.Point.TypeRep t
valueConstantType v = case valueType v of
  Constant trep -> trep

valueConstantExpr :: Value (Constant t) -> LocalM C.Expr
valueConstantExpr v = case valueDefn v of
  ValueConstant e -> e

valueVaryingType :: Value (Varying n t) -> (NatRep n, Object.Point.TypeRep t)
valueVaryingType v = case valueType v of
  Varying nrep trep -> (nrep, trep)

valueVaryingExprs :: Value (Varying n t) -> Vec ('S n) (LocalM C.Expr)
valueVaryingExprs v = case valueDefn v of
  ValueVarying vs -> vs

valueProgramType :: Value (Program t) -> Meta.TypeRep Object.TypeRep t
valueProgramType v = case valueType v of
  Program trep -> trep

valueProgramRepr :: Value (Program t) -> ProgramM (Repr.Repr ValueM Value t)
valueProgramRepr v = case valueDefn v of
  ValueProgram it -> it

constantValueToExpr :: Repr.Val ValueM Value (Obj (Constant t)) -> LocalM C.Expr
constantValueToExpr v = case valueDefn (Repr.fromObject v) of
  ValueConstant e -> e

varyingValueToExpr :: Repr.Val ValueM Value (Obj (Varying n t)) -> Index ('S n) -> LocalM C.Expr
varyingValueToExpr v i = case valueDefn (Repr.fromObject v) of
  ValueVarying vs -> index i vs

dropVaryingValue :: Value (Varying ('S n) t) -> Value (Varying n t)
dropVaryingValue v = Value
  { valueType = case valueType v of
      Varying (S_Rep nrep) trep -> Varying nrep trep
  , valueDefn = case valueDefn v of
      ValueVarying vec -> ValueVarying (vecDropFirst vec)
  }

shiftVaryingValue :: Value (Varying ('S n) t) -> Value (Varying n t)
shiftVaryingValue v = Value
  { valueType = case valueType v of
      Varying (S_Rep nrep) trep -> Varying nrep trep
  , valueDefn = case valueDefn v of
      ValueVarying vec -> ValueVarying (vecDropLast vec)
  }

value :: Object.TypeRep t -> ValueDefn t -> Value t
value trep defn = Value { valueType = trep, valueDefn = defn }

constantValueType :: Value (Constant t) -> Object.Point.TypeRep t
constantValueType v = case valueType v of
  Object.Constant_r trep -> trep

constantValue
  :: Meta.TypeRep Object.TypeRep (Obj (Constant t))
  -> LocalM C.Expr
  -> Value (Constant t)
constantValue (Obj trep) expr = value trep (ValueConstant expr)

constantValue_
  :: Meta.TypeRep Object.TypeRep (Obj (Constant t))
  -> C.Expr
  -> Value (Constant t)
constantValue_ trep cexpr = constantValue trep (pure cexpr)

varyingValue
  :: Meta.TypeRep Object.TypeRep (Obj (Varying n t))
  -> Vec (S n) (LocalM C.Expr)
  -> Value (Varying n t)
varyingValue (Obj trep) exprs = value trep (ValueVarying exprs)

varyingValue_
  :: Meta.TypeRep Object.TypeRep (Obj (Varying n t))
  -> Vec (S n) C.Expr
  -> Value (Varying n t)
varyingValue_ trep exprs = varyingValue trep (vecMap pure exprs)

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

overConstantValue1
  :: (Object.Point.TypeRep s -> Object.Point.TypeRep t)
  -> (C.Expr -> C.Expr)
  -> (Value (Constant s) -> Value (Constant t))
overConstantValue1 fty fexpr = \v ->
  let ty = fty (valueConstantType v)
      ex = fexpr <$> valueConstantExpr v
  in  value (Constant ty) (ValueConstant ex)

overConstantValue2
  :: (Object.Point.TypeRep s -> Object.Point.TypeRep t -> Object.Point.TypeRep u)
  -> (C.Expr -> C.Expr -> C.Expr)
  -> (Value (Constant s) -> Value (Constant t) -> Value (Constant u))
overConstantValue2 fty fexpr = \v1 v2 ->
  let ty = fty (valueConstantType v1) (valueConstantType v2)
      ex = fexpr <$> valueConstantExpr v1 <*> valueConstantExpr v2
  in  value (Constant ty) (ValueConstant ex)

interpC :: Repr.Interpret Object.Form ValueM Value
interpC trep form = case form of

  -- TODO may be best to put explicit type casts on these.
  Object.Integer_Literal_UInt8_f  w8  -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral w8)
  Object.Integer_Literal_UInt16_f w16 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral w16)
  Object.Integer_Literal_UInt32_f w32 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral w32)
  Object.Integer_Literal_UInt64_f w64 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral w64)

  Object.Integer_Literal_Int8_f  i8  -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral i8)
  Object.Integer_Literal_Int16_f i16 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral i16)
  Object.Integer_Literal_Int32_f i32 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral i32)
  Object.Integer_Literal_Int64_f i64 -> Repr.object . constantValue_ trep $
    integerLiteralExpr (typeNameMeta trep) (fromIntegral i64)

  Object.Bytes_Literal_8_f  w8  -> Repr.object . constantValue_ trep $
    bytesLiteralExpr (typeNameMeta trep) (fromIntegral w8)
  Object.Bytes_Literal_16_f w16 -> Repr.object . constantValue_ trep $
    bytesLiteralExpr (typeNameMeta trep) (fromIntegral w16)
  Object.Bytes_Literal_32_f w32 -> Repr.object . constantValue_ trep $
    bytesLiteralExpr (typeNameMeta trep) (fromIntegral w32)
  Object.Bytes_Literal_64_f w64 -> Repr.object . constantValue_ trep $
    bytesLiteralExpr (typeNameMeta trep) (fromIntegral w64)

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

  Object.Cast_f cast -> Repr.fun $ \x ->
    Repr.repr (overObject1 (castValue trep cast) <$> Repr.getRepr x)

  Object.Stream_Shift_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 shiftVaryingValue <$> Repr.getRepr x)
  Object.Stream_Drop_f -> Repr.fun $ \x ->
    Repr.repr (overObject1 dropVaryingValue <$> Repr.getRepr x)

  Object.Stream_Map_f nrep limage rimage -> interpMap trep nrep limage rimage

  -- The composite type intro/elim forms may introduce new required type
  -- declarations.

  Object.Product_Intro_f _ -> error "Product_Intro_f not defined"
  Object.Sum_Intro_f _ -> error "Sum_Intro_f not defined"
  Object.Product_Elim_f _ -> error "Product_Elim_f not defined"
  -- This one is not so obvious.
  -- If the result were always an object, it'd be fine, but if it's a product
  -- or a function, then what? We always want to express the same structure
  -- of course:
  --
  --   switch (sum.tag) {
  --     case tag_0: {
  --       ...
  --       break;
  --     }
  --     ...
  --   }
  --
  -- If the result is an object, then in each variant we would set a value
  --
  --   resultType r;
  --   switch (sum.tag) {
  --     case tag_0: {
  --       ...
  --       r = x;
  --       break;
  --     }
  --     ...
  --   }
  --   // now r can be used
  --
  -- If the result is a product? 
  --
  -- If the result is a function, then when that function is applied, the whole
  -- elimination construction comes out. Think of it like floating the function
  -- abstraction out front.
  --
  --   \arg -> case s of
  --     A -> X
  --     B -> Y
  --
  -- is the same as
  --
  --   case s of
  --     A -> \arg -> X
  --     B -> \arg -> Y
  --
  -- and what about for products?
  --
  --   case s of
  --     A -> (X1, X2)
  --     B -> (Y1, Y2)
  --
  -- is the same as
  --
  --   (case s of { A -> X1; B -> Y1 }, case s of { A -> X2, B -> Y2 })
  --
  -- So there you have it...
  -- If the result of the sum elimination is
  --
  --   - Terminal, then the whole thing is terminal
  --   - A function, then we float it out
  --   - A product, then we float it out
  --   - An object, then we make an uninitialized variable and assign it at
  --     the end of each branch
  --
  -- To do this, I think we just have to match on the TypeRep? Yeah, we should
  -- be able to recursively pull out all of the products and functions until
  -- we have a Sum_Elim_f where the Cases r type is Obj.
  --
  -- The same story will happen for Product_Elim_f, since the selector can
  -- also give a function.
  --
  -- What about
  --
  --   let x = (let y = z in q) in r
  --   _____________________________
  --   let y = z in (let x = q in r)
  --
  -- The intro forms are simple though.
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
  -- Evaluting constObj here in ValueM does not elaborate any block items,
  -- but it does make binding identifiers for other let bindings.
  --
  -- The 'valueConstantExpr' is the 'LocalM' which _will_ elaborate block
  -- items, including initializer declarations for let bindings, in an
  -- idempotent fashion.
  let cexprM :: LocalM C.Expr
      cexprM = valueConstantExpr constObj
  boundValue <- makeIdempotent srep cexprM
  Repr.getRepr (k Repr.<@> Repr.object boundValue)


-- | This will use the ProgramM representation to come up with all the
-- necessary StaticVaryings, then put them into the state, and return the
-- basic varying representation
--
--   VCons (name[i]) (VCons (name[(i+1)%size]) ...)
--
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

    names <- genStaticVaryingNames rrep knotSig
    let r :: Repr.Repr ValueM Value r
        r = staticVaryingValues names
        s :: Repr.Repr ValueM Value s
        s = shiftedStaticVaryingValues knotSig names
        t :: Repr.Repr ValueM Value t
        t = recDef Repr.<@> s
    -- Here we need to evaluate in ValueM, to get the LocalMs for all of the
    -- updates (`t`s) and inits (`i`s), then put those LocalMs into the
    -- state so they can be elaborated later on when we make a translation unit.
    inits <- valueMInProgramM $ staticVaryingInits knotSig i
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
interpMap ((srep :-> _) :-> (_ :-> rrep)) nrep limage rimage = Repr.fun $ \preimage -> Repr.fun $ \q -> Repr.valuef $ do
  rolled  <- zipVarying srep nrep limage q
  f <- Repr.getRepr preimage
  let applied = applyVarying f rolled
  Repr.getRepr (unzipVarying rrep nrep rimage applied)

  where

  zipVarying
    :: forall n t r .
       Meta.TypeRep Object.TypeRep t
    -> NatRep n
    -> Object.MapImage n t r
    -> Repr.Repr ValueM Value r
    -> ValueM (Vec ('S n) (Repr.Repr ValueM Value t))

  zipVarying _              nrep Object.MapTerminal      _ = pure $ vecReplicate (S_Rep nrep) Repr.terminal

  zipVarying trep           nrep Object.MapObject        v = do
    it <- Repr.getRepr v
    case valueDefn (Repr.fromObject it) of
      ValueVarying exprs -> pure $ vecMap (\expr -> Repr.object (constantValue trep expr)) exprs

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

  unzipVarying _              nrep Object.MapTerminal      _   = Repr.terminal

  unzipVarying (Obj trep)     nrep Object.MapObject        v = Repr.objectf $ do
    w <- vecTraverse (fmap constantValueToExpr . Repr.getRepr) v
    pure $ value trep (ValueVarying w)

  unzipVarying (lrep :* rrep) nrep (Object.MapProduct l r) v = Repr.valuef $ do
    w <- vecTraverse Repr.getRepr v
    let (lw, rw) = vecUnzip (\(Repr.Product (a, b)) -> (a, b)) w
        a = unzipVarying lrep nrep l lw
        b = unzipVarying rrep nrep r rw
    pure $ Repr.Product (a, b)

-- | We don't even need to do any checking here, GHC should ensure that all of
-- our casts are safe (assuming the EDSL types are set up correctly).
castValue
  :: forall a b .
     Meta.TypeRep Object.TypeRep (Obj (Constant a) :-> Obj (Constant b))
  -> Object.Cast a b
  -> Value (Constant a)
  -> Value (Constant b)
castValue (_ :-> Obj brep@(Constant rep)) cast =
  overConstantValue1 castTypeRep (castExpr (typeName brep))

  where

  castTypeRep :: Object.Point.TypeRep a -> Object.Point.TypeRep b
  castTypeRep _ = rep

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
absValue v = overConstantValue1 castf (absExpr tyName) v
  where
  castf :: Object.Point.TypeRep ('Object.Point.Integer_t 'Object.Point.Signed_t   width)
        -> Object.Point.TypeRep ('Object.Point.Integer_t 'Object.Point.Unsigned_t width)
  castf (Object.Point.Integer_r _ wrep) = Object.Point.Integer_r Object.Point.Unsigned_r wrep
  tyName = typeName (valueType v)

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

typeNameMeta :: Meta.TypeRep Object.TypeRep (Obj (Constant t)) -> C.TypeName
typeNameMeta (Obj (Constant trep)) = typeNameConstant trep

typeName :: Object.TypeRep (Constant t) -> C.TypeName
typeName (Constant   t) = typeNameConstant t

-- TODO products and sums.
typeNameConstant :: Object.Point.TypeRep t -> C.TypeName
typeNameConstant (Object.Point.Integer_r srep wrep) = typeNameInteger srep wrep
typeNameConstant (Object.Point.Bytes_r   wrep     ) = typeNameBytes        wrep

typeNameInteger
  :: Object.Point.SignednessRep s
  -> Object.Point.WidthRep w
  -> C.TypeName
typeNameInteger s w = C.TypeName (C.SpecQualType (C.TTypedef (C.TypedefName (integerTypeIdent s w))) Nothing) Nothing

typeNameBytes :: Object.Point.WidthRep w -> C.TypeName
typeNameBytes = typeNameInteger Object.Point.Unsigned_r

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
