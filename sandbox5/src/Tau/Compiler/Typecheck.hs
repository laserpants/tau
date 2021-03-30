{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Tau.Lang
import Tau.Tool
import Tau.Type


