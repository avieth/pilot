{-|
Module      : Pilot.Interp.C
Description : Sink for useful C code generation stuff.
Copyright   : (c) Alexander Vieth, 2020
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

module Pilot.Interp.C
  ( IO.externInput
  , IO.externOutput
  , CodeGen
  , Stream
  , Point
  , module Util
  , StreamExpr
  , StreamExprF
  ) where

import Pilot.Interp.C.CodeGen
import Pilot.Interp.C.IO as IO
import Pilot.Interp.C.Util as Util
import Pilot.Interp.C.CodeGen (StreamExpr, StreamExprF)
