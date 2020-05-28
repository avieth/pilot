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

module Pilot.Interp.C.IO
  ( externInput
  , externOutput
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

import Pilot.Interp.C.AST
import Pilot.Interp.C.CodeGen
import Pilot.Interp.C.Eval

-- | Create a stream which will appear as a C extern. This is the way in
-- which external real world _input_ appears.
--
-- NB: this gives a stream expression, but it's behind the C CodeGen monad. In
-- order to get and use that expression, one must run it in the ExprM monad
-- by way of 'Pilot.EDSL.Expr.special'.
--
-- Also note that, unlike externOutput, this does not fix the static stream
-- value and interpreter parts to be in the pure interpreter. That's because
-- externInput does not actually need to evaluate any streams (i.e. generate
-- any C for a stream).
externInput
  :: String
  -> Point.TypeRep t
  -> CodeGen s
       (Expr
         (Stream.ExprF (Expr Point.ExprF cval cf) (Expr Point.ExprF sval sf))
         (Stream s)
         (CodeGen s)
         ('Stream.Stream 'Z t)
       )
externInput name trep = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExternInputs
  when exists $ codeGenError $ CodeGenDuplicateExternName name
  -- Prefix with "input_" so that it's impossible to clash with names
  -- that we choose internally for other things.
  ident <- maybeError
    (CodeGenInvalidExternName name)
    (pure (stringIdentifier ("input_" ++ name)))
  tinfo <- type_info NotShared trep
  let typeSpec = ctypeSpec tinfo
      mPtr = if ctypePtr tinfo then Just (C.PtrBase Nothing) else Nothing
      !externDeclr = ExternObjectDeclr
        Nothing
        typeSpec
        mPtr
        ident
      !cexpr = identIsCondExpr ident
      stream = Stream
        { streamVal       = StreamValNonStatic (VCons (pure cexpr) VNil)
        , streamTypeRep   = Stream.Stream_t Z_t trep
        , streamCTypeInfo = tinfo
        }
  CodeGen $ Trans.lift $ modify' $ \cgs ->
    cgs { cgsExternInputs = Map.insert name externDeclr (cgsExternInputs cgs) }
  pure $ knownValue stream

-- | Use this stream to make an output. It will appear as an uninitialized
-- C static variable, which will be written on each evalauation of the system
-- (each main function call in the generated C).
--
-- NB: consistent with 'externInput', if this term appears in the expression,
-- then the extern appears and the output will be written.
--
-- It _may_ be prefereable, moving forward, to give an explicit IO type for
-- the C backend. Extern inputs and outputs would appear within these, and
-- typical pure streams could be lifted into it. We would encoter types like
-- this:
--
--   ExprM (Stream.ExprF) (Stream s) (CodeGen s) (IO s t)
--
externOutput
  :: String
  -> StreamExpr s ('Stream.Stream 'Z t)
  -> CodeGen s ()
externOutput name expr = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExternOutputs
  when exists $ codeGenError $ CodeGenDuplicateExternName name
  ident <- maybeError
    (CodeGenInvalidExternName name)
    (pure (stringIdentifier ("output_" ++ name)))
  stream <- eval_stream expr
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
  pure ()
