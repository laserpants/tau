{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Writer
import Tau.Compiler.Substitution
import Tau.Compiler.Typecheck
import Tau.Compiler.Unification
import Tau.Core
import Tau.Env
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Type
import qualified Tau.Env as Env

main = print "Main"
