{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, unpack)
import Data.Void
import Tau.Expr
import Tau.Type
import Tau.Util
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
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
withInitial pchar = pack <$> ((:) <$> pchar <*> many alphaNumChar)

keyword :: Text -> Parser ()
keyword tok =
    Megaparsec.string tok
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
    , "True"
    , "False"
    , "not"
    , "forall"
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
-- == Ast
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
parseExpr = runParser (spaces *> expr <* eof) ""

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
    term <- symbol  "="   *> expr
    body <- keyword "in"  *> expr
    pure (con var term body)

matchWith :: Parser Expr
matchWith = do
    term  <- keyword "match" *> expr
    first <- clause "="
    rest  <- many (clause "|")
    pure (matchS term (first:rest))

lamMatch :: Parser Expr
lamMatch = do
    keyword "\\match"
    first <- clause "="
    rest  <- many (clause "|")
    pure (lamMatchS (first:rest))

clause :: Text -> Parser (Pattern, Expr)
clause sym = do
    pat  <- symbol sym  *> parsePattern
    term <- symbol "=>" *> expr
    pure (pat, term)

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
    con <- constructor
    pats <- many parsePattern
    pure (conP con pats)

litPattern :: Parser Pattern
litPattern = litP <$> prim

wildcard :: Parser Pattern
wildcard = symbol "_" $> anyP

lambda :: Parser Expr
lambda = do
    var  <- symbol "\\" *> name
    body <- symbol "=>" *> expr
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
    pure $ if n > maxInt || n < minInt
        then Integer n
        else Int (fromIntegral n)
  where
    maxInt = fromIntegral (maxBound :: Int)
    minInt = fromIntegral (minBound :: Int)

float :: Parser Prim
float = Float <$> lexeme Lexer.float

number :: Parser Prim
number = try float <|> integral

charPrim :: Parser Prim
charPrim = Char <$> surroundedBy (symbol "'") printChar

stringPrim :: Parser Prim
stringPrim = lexeme (String . pack <$> chars) where
    chars = char '\"' *> manyTill Lexer.charLiteral (char '\"')

-- ============================================================================
-- == Type
-- ============================================================================

type_ :: Parser Type
type_ = makeExprParser parser [[ InfixR (arrT <$ symbol "->") ]]
  where
    parser = do
        atoms <- some atom
        pure (foldl1 appT atoms)

    atom = parens type_
       <|> varT <$> name
       <|> conT <$> constructor

tyClass :: Parser TyClass
tyClass = TyCl <$> constructor <*> type_

quantifier :: Parser (Maybe [Name])
quantifier = optional (keyword "forall" *> some name <* symbol ".")

classConstraints :: Parser (Maybe [TyClass])
classConstraints = optional (parens (some tyClass) <* symbol "=>")

scheme :: Parser Scheme
scheme = Forall <$> (fromMaybe [] <$> quantifier)
                <*> (fromMaybe [] <$> classConstraints)
                <*> type_
