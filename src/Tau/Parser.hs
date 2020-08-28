{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Applicative ((<|>))
import Control.Monad (void)
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Functor.Foldable
import Data.Text (Text, pack, unpack)
import Data.Void
import Tau.Juice hiding (($>), name)
import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, letterChar, printChar, space1)
import qualified Text.Megaparsec.Char as Megaparsec
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = Parsec Void String

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: String -> Parser String
symbol = Lexer.symbol spaces

spaces :: Parser ()
spaces = Lexer.space
    space1
    (Lexer.skipLineComment "--")
    (Lexer.skipBlockComment "{-" "-}")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

withInitial :: Parser Char -> Parser String
withInitial char = do
    head <- char
    tail <- many alphaNumChar
    pure (head : tail)

keyword :: String -> Parser ()
keyword token =
    Megaparsec.string token
        *> notFollowedBy alphaNumChar
        *> spaces

reserved :: [String]
reserved =
    [ "let"
    , "in"
    , "if"
    , "then"
    , "else"
    , "True"
    , "False"
    , "not"
    ]

identifier :: Parser String
identifier = lexeme $ try $ do
    var <- withInitial letterChar
    if var `elem` reserved
        then fail ("Reserved keyword " <> var)
        else pure var

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

ast :: Parser Expr
ast = do
    atoms <- some atom
    pure $ case atoms of
        (e:_) -> e
        exprs -> appS exprs
  where
    atom = unit
        <|> parens expr
        <|> ifClause
        <|> letRecBinding
        <|> letBinding
        <|> lambda
        <|> number
        <|> bool
        <|> char
        <|> string
        <|> variable

operator :: [[Operator Parser Expr]]
operator =
    [
      [ Prefix (negS <$ symbol "-")
      ]
    , [ Prefix (notS <$ (symbol "not" *> spaces))
      ]
    , [ InfixL (mulS <$ symbol "*")
      , InfixL (divS <$ symbol "/")
      ]
    , [ InfixL (addS <$ symbol "+")
      , InfixL (subS <$ symbol "-")
      ]
    , [ InfixN (eqS <$ symbol "==")
      , InfixN (ltS <$ symbol "<")
      , InfixN (gtS <$ symbol ">")
      ]
    ]

expr :: Parser Expr
expr = makeExprParser ast operator

parseExpr :: String -> Either (ParseErrorBundle String Void) Expr
parseExpr = parse (spaces *> expr <* eof) ""

name :: Parser Text
name = pack <$> identifier

ifClause :: Parser Expr
ifClause = do
    cond  <- keyword "if"   *> expr
    true  <- keyword "then" *> expr
    false <- keyword "else" *> expr
    pure (ifS cond true false)

letRecBinding :: Parser Expr
letRecBinding = parseLet recS "let rec"

letBinding :: Parser Expr
letBinding = parseLet letS "let"

parseLet :: (Name -> Expr -> Expr -> Expr) -> String -> Parser Expr
parseLet con kword = do
    var  <- keyword kword *> name
    exp  <- symbol  "="   *> expr
    body <- keyword "in"  *> expr
    pure (con var exp body)

lambda :: Parser Expr
lambda = do
    var  <- symbol "\\" *> name
    body <- symbol "->" *> expr
    pure (lamS var body)

unit :: Parser Expr
unit = symbol "()" $> litUnit

bool :: Parser Expr
bool = true <|> false
  where
    true  = keyword "True"  $> litBool True
    false = keyword "False" $> litBool False

int :: Parser Expr
int = litInt <$> lexeme Lexer.decimal

float :: Parser Expr
float = litFloat <$> lexeme Lexer.float

number :: Parser Expr
number = try float <|> int

char :: Parser Expr
char = litChar <$> between (symbol "'") (symbol "'") printChar

string :: Parser Expr
string = litString . pack <$> str
  where
    chr = Megaparsec.char
    str = chr '"' *> takeWhileP Nothing (/= '"') <* chr '"'

variable :: Parser Expr
variable = varS <$> name
