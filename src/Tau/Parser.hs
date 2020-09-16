{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad (when, void)
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
    , "with"
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
        <|> list_
        <|> tuple
        <|> identifier

prim :: Parser Prim
prim = bool
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
      [ InfixR (cmpS <$ symbol "<<")
      ]
    , [ Prefix (negS <$ symbol "-")
      ]
    , [ Prefix (notS <$ (keyword "not" *> spaces))
      ]
    , [ InfixL (mulS <$ symbol "*")
      , InfixL (divS <$ try (symbol "/" <* notFollowedBy (symbol "=")))
      ]
    , [ InfixL (addS <$ symbol "+")
      , InfixL (subS <$ symbol "-")
      ]
    , [ InfixR (cons <$ symbol "::")
      ]
    , [ InfixN (eqS  <$ symbol "==")
      , InfixN (neqS <$ symbol "/=")
      , InfixN (ltS  <$ symbol "<")
      , InfixN (gtS  <$ symbol ">")
      ]
    , [ InfixR (andS <$ symbol "&&")
      ]
    , [ InfixR (orS  <$ symbol "||")
      ]
    , [ InfixL (dotS <$ symbol ".")
      ]
    ]

cons :: Expr -> Expr -> Expr
cons hd tl = appS [varS "Cons", hd, tl]

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
    pats <- many pattern_
    term <- symbol  "="   *> expr
    body <- keyword "in"  *> expr
    pure (con var (expandLam term pats) body)

matchWith :: Parser Expr
matchWith = do
    term  <- keyword "match" *> expr
    first <- clause with
    rest  <- many (clause pipe)
    pure (matchS term (first:rest))

with :: Parser ()
with = void $ keyword "with" *> optional (symbol "|")

lamMatch :: Parser Expr
lamMatch = do
    keyword "\\match"
    first <- clause (void (optional pipe))
    rest  <- many (clause pipe)
    pure (lamMatchS (first:rest))

pipe :: Parser ()
pipe = void (symbol "|")

clause :: Parser () -> Parser (Pattern, Expr)
clause sep = do
    pat  <- sep *> pattern_
    term <- symbol "=>" *> expr
    pure (pat, term)

pattern_ :: Parser Pattern
pattern_ = makeExprParser patternExpr [[ InfixR (patternCons <$ symbol "::") ]]

patternCons :: Pattern -> Pattern -> Pattern
patternCons hd tl = conP "Cons" [hd, tl]

patternExpr :: Parser Pattern
patternExpr = wildcard
    <|> conPattern
    <|> litPattern
    <|> varPattern
    <|> listPattern
    <|> tuplePattern

listPattern :: Parser Pattern
listPattern = do
    void (symbol "[")
    elems <- pattern_ `sepBy` symbol ","
    void (symbol "]")
    pure $ case elems of
        [] -> conP "Nil" []
        _  -> conP "Cons" (elems <> [varP "Nil"])

tuplePattern :: Parser Pattern
tuplePattern = do
    void (symbol "(")
    elems <- pattern_ `sepBy` symbol ","
    void (symbol ")")
    when (length elems > 8) (fail "Tuples can only have up to 8 elements")
    pure (mkTuple conP litP elems)

varPattern :: Parser Pattern
varPattern = varP <$> name

conPattern :: Parser Pattern
conPattern = do
    con <- constructor
    pats <- many pattern_
    pure (conP con pats)

litPattern :: Parser Pattern
litPattern = litP <$> prim

wildcard :: Parser Pattern
wildcard = symbol "_" $> anyP

lambda :: Parser Expr
lambda = do
    void (symbol "\\")
    pats <- some pattern_
    body <- symbol "=>" *> expr
    pure (expandLam body pats)

expandLam :: Expr -> [Pattern] -> Expr
expandLam term pats =
    if and (isVar <$> pats)
        then foldr lamS term (concatMap patternVars pats)
        else foldr (\pat a -> lamMatchS [(pat, a)]) term pats

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
-- == Lists and Tuples
-- ============================================================================

list_ :: Parser Expr
list_ = do
    void (symbol "[")
    elems <- expr `sepBy` symbol ","
    void (symbol "]")
    pure (foldr cons1 (appS [varS "Nil"]) elems)
  where
    cons1 hd tl = appS [varS "Cons", hd, tl]

tuple :: Parser Expr
tuple = do
    void (symbol "(")
    elems <- expr `sepBy` symbol ","
    void (symbol ")")
    when (length elems > 8) (fail "Tuples can only have up to 8 elements")
    pure (mkTuple (\con -> appS . (varS con :)) litS elems)

mkTuple :: (Text -> [a] -> a) -> (Prim -> a) -> [a] -> a
mkTuple con nil = \case
    []                       -> nil Unit
    [a, b]                   -> con "Tuple2" [a, b]
    [a, b, c]                -> con "Tuple3" [a, b, c]
    [a, b, c, d]             -> con "Tuple4" [a, b, c, d]
    [a, b, c, d, e]          -> con "Tuple5" [a, b, c, d, e]
    [a, b, c, d, e, f]       -> con "Tuple6" [a, b, c, d, e, f]
    [a, b, c, d, e, f, g]    -> con "Tuple7" [a, b, c, d, e, f, g]
    [a, b, c, d, e, f, g, h] -> con "Tuple8" [a, b, c, d, e, f, g, h]
    a:_                      -> a

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

-- ============================================================================
-- == Kind
-- ============================================================================

kind :: Parser Kind
kind = makeExprParser parser [[ InfixR (arrK <$ symbol "->") ]] where
    parser = parens kind <|> (symbol "*" $> starK)
