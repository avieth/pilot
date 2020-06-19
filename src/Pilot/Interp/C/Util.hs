{-|
Module      : Pilot.Interp.C.Util
Description : Convenient stuff for generating C.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE DataKinds #-}

module Pilot.Interp.C.Util
  ( codeGenString
  , codeGenToFile
  , writePointExpr
  , writeStreamExpr
  , writeStreamExec
  ) where

import Control.Exception (throwIO)

import Pilot.EDSL.Expr
import qualified Pilot.EDSL.Stream as EDSL
import qualified Pilot.EDSL.Stream as Stream
import qualified Pilot.EDSL.Point as EDSL
import qualified Pilot.EDSL.Point as Point

import Pilot.Types.Represented
import Pilot.Types.Nat

import Pilot.Interp.Exec
import qualified Pilot.Interp.Pure as Pure
import Pilot.Interp.C.CodeGen
import Pilot.Interp.C.Eval

-- | Generates the concrete syntax for the translation unit.
codeGenString
  :: CodeGenOptions
  -> CodeGen s (Stream s ('EDSL.Stream n x))
  -> Either CodeGenError String
codeGenString opts cg = fmap prettyPrint (genTransUnit opts cg)

-- | Generates the translation unit and writes it to a file.
--
-- Puts in stdint.h and stdio.h includes.
codeGenToFile
  :: String
  -> CodeGenOptions
  -> CodeGen s (Stream s ('EDSL.Stream n x))
  -> IO ()
codeGenToFile fp opts cg = case codeGenString opts cg of
  Left  err -> throwIO (userError (show err))
  Right str -> writeFile fp $ includes ++ str
  where
  includes = mconcat
    [ "#include <stdint.h>\n"
    , "#include <stdio.h>\n"
    , "\n"
    ]

-- | Generate and write C for a point expression, by making it a constant
-- stream.
writePointExpr
  :: (EDSL.KnownType t)
  => String
  -> Bool
  -> Expr Point.ExprF (Point s) t
  -> IO ()
writePointExpr fp b expr = writeStreamExpr fp b (EDSL.constant auto Z_t expr)

writeStreamExpr
  :: String
  -> Bool
  -> StreamExpr s ('EDSL.Stream n x)
  -> IO ()
writeStreamExpr fp b expr = codeGenToFile fp opts (eval_stream expr)
  where
  opts = CodeGenOptions { cgoCompoundTypeTreatment = if b then Shared else NotShared }

writeStreamExec
  :: String
  -> Bool
  -> Exec (Stream.ExprF (Expr Point.ExprF (Point s)) (Expr Point.ExprF Pure.Point))
          (Stream s)
          (CodeGen s)
          -- TODO should not need this. Translation unit generation should not
          -- demand an expression at the end.
          (Stream s ('EDSL.Stream n x))
  -> IO ()
writeStreamExec fp b exec = codeGenToFile fp opts (runExec exec eval_stream)
  where
  opts = CodeGenOptions { cgoCompoundTypeTreatment = if b then Shared else NotShared }
