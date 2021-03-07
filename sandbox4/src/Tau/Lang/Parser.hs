{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Parser where

import Control.Monad (when, void)
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.List (sortOn, nub)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Text (Text, pack, unpack)
import Data.Tuple.Extra (first)
import Data.Void
import Tau.Comp.Type.Substitution
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util (Name, Fix(..), embed, project, cata, to, (<$$>), traceShowM)
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Comp.Type.Substitution as Sub
import qualified Text.Megaparsec.Char as Megaparsec
import qualified Text.Megaparsec.Char.Lexer as Lexer

type ParseError = ParseErrorBundle Text Void

type Parser = Parsec Void Text


