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
import Text.Megaparsec.Char (alphaNumChar, letterChar, printChar, space1, lowerChar, upperChar)
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
    , "match"
    , "with"
    , "True"
    , "False"
    , "not"
    ]

identifier :: Parser String
identifier = lexeme $ try $ do
    var <- withInitial lowerChar
    if var `elem` reserved
        then fail ("Reserved keyword " <> var)
        else pure var

constructor :: Parser String
constructor = lexeme $ try $ withInitial upperChar

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

ast :: Parser Expr
ast = do
    exprs <- appS <$> some atom
    pure $ case unfix exprs of
        AppS [e] -> e
        _        -> exprs
  where
    atom = ifClause
        <|> letRecBinding
        <|> letBinding
        <|> matchWith
        <|> lambda
        <|> literal
        <|> parens expr
        <|> variable

prim :: Parser Prim
prim = unit
    <|> bool
    <|> number
    <|> char
    <|> string

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

matchWith :: Parser Expr
matchWith = do
    expr <- keyword "match" *> expr
    clss <- keyword "with"  *> many clause
    pure (matchS expr clss)

clause :: Parser (Pattern, Expr)
clause = do
    pat  <- symbol "|"  *> parsePattern
    expr <- symbol "->" *> expr
    pure (pat, expr)

parsePattern :: Parser Pattern
parsePattern = wildcard
    <|> conPattern
    <|> litPattern
    <|> varPattern

varPattern :: Parser Pattern
varPattern = varP <$> name

conPattern :: Parser Pattern
conPattern = do
    con <- pack <$> constructor
    pts <- many parsePattern
    pure (conP con pts)

litPattern :: Parser Pattern
litPattern = litP <$> prim

wildcard :: Parser Pattern
wildcard = symbol "_" $> anyP

lambda :: Parser Expr
lambda = do
    var  <- symbol "\\" *> name
    body <- symbol "->" *> expr
    pure (lamS var body)

unit :: Parser Prim
unit = symbol "()" $> Unit

bool :: Parser Prim
bool = true <|> false
  where
    true  = keyword "True"  $> Bool True
    false = keyword "False" $> Bool False

int :: Parser Prim
int = Int <$> lexeme Lexer.decimal

float :: Parser Prim
float = Float <$> lexeme Lexer.float

number :: Parser Prim
number = try float <|> int

char :: Parser Prim
char = Char <$> between (symbol "'") (symbol "'") printChar

string :: Parser Prim
string = String . pack <$> str
  where
    chr = Megaparsec.char
    str = chr '"' *> takeWhileP Nothing (/= '"') <* chr '"'

literal :: Parser Expr
literal = litS <$> prim

variable :: Parser Expr
variable = varS <$> name
