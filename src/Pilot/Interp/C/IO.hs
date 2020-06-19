{-|
Module      : Pilot.Interp.C.IO
Description : Definition of IO in the C backend (externs and triggers)
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pilot.Interp.C.IO
  ( externInput
  , externOutput
  , codeGenExternInput
  , codeGenExternOutput
  ) where

import Control.Monad (when)
import Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.State.Strict (gets, modify')

import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

import qualified Language.C99.AST as C

import Pilot.EDSL.Expr
import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Nat

import Pilot.Interp.Exec as Exec
import Pilot.Interp.C.AST
import Pilot.Interp.C.CodeGen as C
import Pilot.Interp.C.Eval

-- | Declare an input to the C program. It will appear as an extern of the
-- given type.
--
-- TODO put the externs into a heade.r
-- TODO take a metadata GADT with programmer-controlled field/variant names and
--   a typedef for the whole type. Also generate macros for intro/elim of
--   compound types.
--
-- Note that the parameter `edsl` is free here, except for its kind which is
-- specialized to the stream/point domain.
-- This means that the term certainly does not use the "interpret"
-- continuation, i.e. it can compose with an `Exec` over any `edsl` so long as
-- it agrees on the C point/stream values types.
externInput
  :: String
  -> Point.TypeRep t
  -> Exec edsl (C.Stream s) (C.CodeGen s) (C.Stream s ('Stream.Stream 'Z t))
externInput name trep = Exec.impl (codeGenExternInput name trep)

-- | Declare an output of the C program. It will appear as an extern of the
-- given type, and will be updated at each eval step.
--
-- TODO same TODOs as for externInput.
externOutput
  :: String
  -> Stream s ('Stream.Stream 'Z t)
  -> Exec edsl (C.Stream s) (C.CodeGen s) ()
externOutput name stream = Exec.impl (codeGenExternOutput name stream)

-- | Create a stream which will appear as a C extern. This is the way in
-- which external real world input appears.
--
-- NB: this gives a stream expression, but it's behind the C CodeGen monad.
-- That's to say, it does not go directly into an expression AST, it must be
-- declared up-front and its value may be treated like any other stream.
codeGenExternInput
  :: forall s t .
     String
  -> Point.TypeRep t
  -> CodeGen s (C.Stream s ('Stream.Stream 'Z t))
codeGenExternInput name trep = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExternInputs
  when exists $ codeGenError $ CodeGenDuplicateExternName name
  -- Prefix with "input_" so that it's impossible to clash with names
  -- that we choose internally for other things.
  ident <- maybeError
    (CodeGenInvalidExternName name)
    (pure (stringIdentifier ("input_" ++ name)))
  tinfo <- type_info NotShared trep
  let !typeSpec = ctypeSpec tinfo
      !mPtr = if ctypePtr tinfo then Just (C.PtrBase Nothing) else Nothing
      !externDeclr = ExternObjectDeclr
        Nothing
        typeSpec
        mPtr
        ident
      !cexpr = identIsCondExpr ident
      !stream = Stream
        { streamVal       = StreamValNonStatic (VCons (pure cexpr) VNil)
        , streamTypeRep   = Stream.Stream_t Z_t trep
        , streamCTypeInfo = tinfo
        }
  CodeGen $ Trans.lift $ modify' $ \cgs ->
    cgs { cgsExternInputs = Map.insert name externDeclr (cgsExternInputs cgs) }
  pure stream

-- | Given a stream value, this will assign its value at each frame to an
-- extern of the given name.
codeGenExternOutput :: String -> Stream s ('Stream.Stream 'Z t) -> CodeGen s ()
codeGenExternOutput name stream = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExternOutputs
  when exists $ codeGenError $ CodeGenDuplicateExternName name
  ident <- maybeError
    (CodeGenInvalidExternName name)
    (pure (stringIdentifier ("output_" ++ name)))
  cexpr <- streamExprNow (streamVal stream)
  -- Where externInput produces a Stream value and returns it, here we must
  -- add a block item to the context which assigns the stream expression to
  -- the output extern
  let typeSpec = streamTypeSpec stream
      mPtr = if streamPtr stream then Just (C.PtrBase Nothing) else Nothing
      !externDeclr = ExternObjectDeclr
        Nothing
        typeSpec
        mPtr
        ident
      assignExpr :: C.AssignExpr
      !assignExpr = C.Assign
        (identIsUnaryExpr ident)
        C.AEq
        (condExprIsAssignExpr cexpr)
      assignItem :: C.BlockItem
      !assignItem = C.BlockItemStmt $ C.StmtExpr $ C.ExprStmt $ Just $
        C.ExprAssign assignExpr
  addBlockItem assignItem
  CodeGen $ Trans.lift $ modify' $ \cgs ->
    cgs { cgsExternOutputs = Map.insert name externDeclr (cgsExternOutputs cgs) }
