{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad.Combinators.Expr
import Data.Char (isUpper)
import Data.Function ((&))
import Data.Functor (($>))
import Data.Functor.Foldable (Fix(..), unfix)
import Data.Text (Text, pack, unpack)
import Data.Void
import Tau.Juice hiding (($>), name)
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Data.Text as Text
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

surroundedBy :: Parser Text -> Parser a -> Parser a
surroundedBy p = between p p

withInitial :: Parser Char -> Parser Text
withInitial char = do
    head <- char
    tail <- many alphaNumChar
    pure $ pack (head:tail)

keyword :: Text -> Parser ()
keyword token =
    Megaparsec.string token
        *> notFollowedBy alphaNumChar
        *> spaces

reserved :: [Text]
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

word :: Parser Text -> Parser Text
word parser = lexeme $ try $ do
    var <- parser
    if var `elem` reserved
        then fail ("Reserved keyword " <> unpack var)
        else pure var

name :: Parser Text
name = word (withInitial lowerChar)

constructor :: Parser Name
constructor = word (withInitial upperChar)

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

ast :: Parser Expr
ast = do
    app <- appS <$> some atom
    pure $ case unfix app of
        AppS [e] -> e
        _ -> app
  where
    atom = ifClause
        <|> letRecBinding
        <|> letBinding
        <|> matchWith
        <|> lamMatch
        <|> lambda
        <|> literal
        <|> parens expr
        <|> identifier

prim :: Parser Prim
prim = unit
    <|> bool
    <|> number
    <|> charPrim
    <|> stringPrim

literal :: Parser Expr
literal = litS <$> prim

identifier :: Parser Expr
identifier = varS <$> word (withInitial letterChar)

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
    , [ InfixN (orS  <$ symbol "||")
      , InfixN (andS <$ symbol "&&")
      ]
    ]

expr :: Parser Expr
expr = makeExprParser ast operator

parseExpr :: Text -> Either ParseError Expr
parseExpr = parse (spaces *> expr <* eof) ""

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

parseLet :: (Name -> Expr -> Expr -> Expr) -> Text -> Parser Expr
parseLet con kword = do
    var  <- keyword kword *> name
    exp  <- symbol  "="   *> expr
    body <- keyword "in"  *> expr
    pure (con var exp body)

matchWith :: Parser Expr
matchWith = do
    expr <- keyword "match" *> expr
    clss <- keyword "with"  *> some clause
    pure (matchS expr clss)

lamMatch :: Parser Expr
lamMatch = do
    clss <- keyword "\\match" *> some clause
    pure (lamMatchS clss)

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
    <|> parens parsePattern

varPattern :: Parser Pattern
varPattern = varP <$> name

conPattern :: Parser Pattern
conPattern = do
    name <- constructor
    pats <- many parsePattern
    pure (conP name pats)

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

integral :: Parser Prim
integral = do
    n <- lexeme Lexer.decimal
    pure $ if n > max || n < min
        then Integer n
        else Int (fromIntegral n)
  where
    max = fromIntegral (maxBound :: Int)
    min = fromIntegral (minBound :: Int)

float :: Parser Prim
float = Float <$> lexeme Lexer.float

number :: Parser Prim
number = try float <|> integral

charPrim :: Parser Prim
charPrim = Char <$> surroundedBy (symbol "'") printChar

stringPrim :: Parser Prim
stringPrim = lexeme (String . pack <$> chars) where
    chars = char '\"' *> manyTill Lexer.charLiteral (char '\"')
