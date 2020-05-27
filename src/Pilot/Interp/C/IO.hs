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
  ( extern
  ) where

import Control.Monad (when)
import Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.State.Strict (gets, modify')

import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

import qualified Language.C99.AST as C

import qualified Pilot.EDSL.Point as Point
import qualified Pilot.EDSL.Stream as Stream

import Pilot.Types.Nat

import Pilot.Interp.C.AST
import Pilot.Interp.C.CodeGen
import Pilot.Interp.C.Eval

-- | Create a stream which will appear as a C extern. This is the way in
extern :: String -> Point.TypeRep t -> CodeGen s (Stream s ('Stream.Stream 'Z t))
extern name trep = do
  exists <- CodeGen $ Trans.lift $ gets $ isJust . Map.lookup name . cgsExterns
  when exists $ codeGenError $ CodeGenDuplicateExtern name
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
