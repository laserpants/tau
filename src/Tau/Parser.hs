{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Applicative ((<|>))
import Control.Monad (void)
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Text (Text, pack, unpack)
import Data.Void
import Tau.Juice hiding (($>), name)
import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, letterChar, space1)
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
    name <- withInitial letterChar
    if name `elem` reserved 
        then fail ("Reserved keyword " <> name)
        else pure name

{-# ANN module ("HLint: ignore Use <$>" :: String) #-}

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

ast :: Parser Expr
ast = appS <$> some atom
  where
    atom = unit
        <|> parens expr
        <|> ifClause
        <|> letBinding
        <|> letrecBinding
        <|> lambda
        <|> int
        <|> bool
        <|> variable

operator :: [[Operator Parser Expr]]
operator = []

expr :: Parser Expr
expr = makeExprParser ast operator

parseExpr :: String -> Either (ParseErrorBundle String Void) Expr
parseExpr = parse (spaces *> expr <* eof) ""

name :: Parser Text
name = pack <$> identifier

unit :: Parser Expr
unit = symbol "()" $> litUnit

ifClause :: Parser Expr
ifClause = do
    cond  <- keyword "if"   *> expr
    true  <- keyword "then" *> expr
    false <- keyword "else" *> expr
    pure (ifS cond true false)

letrecBinding :: Parser Expr
letrecBinding = parseLet "let rec"

letBinding :: Parser Expr
letBinding = parseLet "let"

parseLet :: String -> Parser Expr
parseLet kword = do
    var  <- keyword kword *> name
    exp  <- symbol  "="   *> expr
    body <- keyword "in"  *> expr
    pure (letS var exp body)

lambda :: Parser Expr
lambda = do
    var  <- symbol "\\" *> name
    body <- symbol "->" *> expr
    pure (lamS var body)

int :: Parser Expr
int = litInt <$> lexeme Lexer.decimal

bool :: Parser Expr
bool = true <|> false 
  where
    true  = keyword "True"  $> litBool True
    false = keyword "False" $> litBool False

variable :: Parser Expr
variable = varS <$> name
