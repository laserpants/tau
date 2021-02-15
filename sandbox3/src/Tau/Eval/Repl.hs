{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
module Tau.Eval.Repl where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Util
import Text.Megaparsec (runParser)
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env


