{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad (when, void)
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.List (sortOn, nub)
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc hiding (pipe, parens)
import Data.Tuple.Extra (first)
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
        <|> record
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
    ]

cons :: Expr -> Expr -> Expr
cons hd tl = appS [varS "Cons", hd, tl]

expr :: Parser Expr
expr = flip makeExprParser operator $ do
    term <- ast
    dots <- many (symbol "." *> name)
    pure (foldl (flip dotS) term dots)

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
    term <- keyword "match" *> expr
    strt <- clause with
    rest <- many (clause pipe)
    pure (matchS term (strt:rest))

with :: Parser ()
with = void $ keyword "with" *> optional (symbol "|")

lamMatch :: Parser Expr
lamMatch = do
    keyword "\\match"
    strt <- clause (void (optional pipe))
    rest <- many (clause pipe)
    pure (lamMatchS (strt:rest))

pipe :: Parser ()
pipe = void (symbol "|")

clause :: Parser () -> Parser (Pattern, Expr)
clause sym = do
    pat  <- sym *> pattern_
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
    <|> recordPattern

recordPattern :: Parser Pattern
recordPattern = do
    pairs <- fields "=" pattern_
    let con = "#Struct" <> intToText (length pairs)
    pure (uncurry (recP con) (unzip pairs))

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
    elems <- components pattern_
    pure $ case elems of
        []  -> litP Unit
        [p] -> p
        _   -> conP ("#Tuple" <> intToText (length elems)) elems

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
    elems <- components expr
    pure $ case elems of
        []  -> litS Unit
        [e] -> e
        _   -> appS (varS ("#Tuple" <> intToText (length elems)):elems)

components :: Parser a -> Parser [a]
components parser = do
    void (symbol "(")
    elems <- parser `sepBy` symbol ","
    void (symbol ")")
    when (length elems > 8) (fail "Tuples can only have up to 8 elements")
    pure elems

-- ============================================================================
-- == Records
-- ============================================================================

record :: Parser Expr
record = structS <$> fields "=" expr

fields :: Text -> Parser a -> Parser [(Name, a)]
fields sym parser = do
    void (symbol "{")
    pairs <- sortOn fst <$> field `sepBy` symbol ","
    void (symbol "}")
    when (hasDups (fst <$> pairs)) (fail "A field name appears more than once in record")
    pure pairs
  where
    hasDups names = length names /= length (nub names)
    field = do
        key <- name
        val <- symbol sym *> parser
        pure (key, val)

-- ============================================================================
-- == Type
-- ============================================================================

type_ :: Parser Type
type_ = makeExprParser parser [[ InfixR (arrT <$ symbol "->") ]]
  where
    parser = do
        atoms <- some atom
        pure (foldl1 appT atoms)

    atom = varT <$> name
       <|> conT <$> constructor
       <|> tupleType
       <|> recordType

tupleType :: Parser Type
tupleType = do
    elems <- components type_
    case elems of
        []  -> fail "Not a type"
        [t] -> pure t
        _   -> pure (foldl appT (conT ("#Tuple" <> intToText (length elems))) elems)

recordType :: Parser Type
recordType = do
    pairs <- fields ":" type_
    let con = "#Struct" <> intToText (length pairs)
    pure (foldl appT (conT con) (unpairs (first conT <$> sortOn fst pairs)))

tyClass :: Parser TyClass
tyClass = TyCl <$> constructor <*> type_

quantifier :: Parser [Name]
quantifier = keyword "forall" *> some name <* symbol "."

classConstraints :: Parser [TyClass]
classConstraints = parens (tyClass `sepBy1` symbol ",") <* symbol "=>"

scheme :: Parser Scheme
scheme = Forall
    <$> (fromMaybe [] <$> optional quantifier)
    <*> (try classConstraints <|> pure [])
    <*> type_

-- ============================================================================
-- == Kind
-- ============================================================================

kind :: Parser Kind
kind = makeExprParser parser [[ InfixR (arrK <$ symbol "->") ]] where
    parser = parens kind <|> (symbol "*" $> starK)

-- ============================================================================
-- == Data types
-- ============================================================================

data Product = Prod Name [Type]
    deriving (Show, Eq)

data Data = Sum Type [Product]
    deriving (Show, Eq)

instance Pretty Data where
    pretty (Sum ty prods) = 
        "type" <+> pretty ty <+> "=" 
               <+> hsep (punctuate "|" (pretty <$> prods))

instance Pretty Product where
    pretty (Prod con types) = pretty con <+> hsep (pretty <$> types)

datatype :: Parser Data
datatype = do
    keyword "type"
    tcon  <- constructor
    tvars <- many (varT <$> name) 
    void (symbol "=")
    prods <- prod `sepBy` symbol "|"
    pure (Sum (foldl appT (conT tcon) tvars) prods)

prod :: Parser Product
prod = do
    data_ <- constructor
    types <- many $ try (varT <$> name) <|> type_
    pure (Prod data_ types)
