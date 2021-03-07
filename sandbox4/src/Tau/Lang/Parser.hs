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

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaces

spaces :: Parser ()
spaces = Lexer.space
    space1
    (Lexer.skipLineComment "--")
    (Lexer.skipBlockComment "{-" "-}")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

surroundedBy :: Parser Text -> Parser a -> Parser a
surroundedBy p = between p p

validChar :: Parser Char
validChar = alphaNumChar <|> char '_'

withInitial :: Parser Char -> Parser Text
withInitial pchar = pack <$> ((:) <$> pchar <*> many validChar)

keyword :: Text -> Parser ()
keyword tok =
    Megaparsec.string tok
        *> notFollowedBy alphaNumChar
        *> spaces

reserved :: [Text]
reserved =
    [ "let"
    , "fix"
    , "in"
    , "if"
    , "then"
    , "else"
    , "match"
    , "with"
    , "when"
    , "as"
    , "or"
    , "fun"
    , "not"
    , "forall"
    , "True"
    , "False"
    , "List"
    , "Void"
    , "Unit"
    ]

word :: Parser Text -> Parser Text
word parser = lexeme $ try $ do
    var <- parser
    if var `elem` reserved
        then fail ("Reserved keyword " <> unpack var)
        else pure var

name :: Parser Text
name = word (withInitial (lowerChar <|> char '_'))

constructor_ :: Parser Name
constructor_ = word (withInitial upperChar)

-- ============================================================================
-- == Operators
-- ============================================================================

operator :: [[Operator Parser (Expr () p q r (Op1 ()) (Op2 ()))]]
operator = 
    [
      -- 9
      [ InfixR (op2Expr () (OLArr ()) <$ symbol "<<")
      , InfixL (op2Expr () (ORArr ()) <$ symbol ">>")
      ]
      -- 8
    , [ InfixR (op2Expr () (OPow ()) <$ symbol "^")
      ]
      -- 7
    , [ InfixL (op2Expr () (OMul ()) <$ symbol "*")
      , InfixL (op2Expr () (ODiv ()) <$ try (symbol "/" <* notFollowedBy (symbol "=")))
      ]
      -- 6
    , [ InfixL (op2Expr () (OAdd ()) <$ symbol "+")
      , InfixL (op2Expr () (OSub ()) <$ symbol "-")
      ]
      -- 5
    , [ InfixR (listCons <$ symbol "::")
      ]
      -- 4
    , [ InfixN (op2Expr () (OEq ()) <$ symbol "==")
      , InfixN (op2Expr () (ONEq ()) <$ symbol "/=")
      , InfixN (op2Expr () (OLt ()) <$ try (symbol "<" <* notFollowedBy (symbol "=")))
      , InfixN (op2Expr () (OGt ()) <$ try (symbol ">" <* notFollowedBy (symbol "=")))
      , InfixN (op2Expr () (OLtE ()) <$ symbol "<=")
      , InfixN (op2Expr () (OGtE ()) <$ symbol ">=")
      ]
      -- 3
    , [ InfixR (op2Expr () (OAnd ()) <$ symbol "&&")
      ]
      -- 2
    , [ InfixR (op2Expr () (OOr ()) <$ symbol "||")
      , Prefix (op1Expr () (ONot ()) <$ (keyword "not" *> spaces))
      ]
      -- 1
    , [ 
      ]
      -- 0
    , [ InfixL (op2Expr () (OFPipe ()) <$ symbol "|>")
      , InfixR (op2Expr () (OBPipe ()) <$ symbol "<|")
      ]
    ]

listCons :: Expr () p q r n o -> Expr () p q r n o -> Expr () p q r n o
listCons hd tl = conExpr () "(::)" [hd, tl]

-- ============================================================================
-- == 
-- ============================================================================

