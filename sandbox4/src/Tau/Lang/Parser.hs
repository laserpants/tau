{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Parser where

import Control.Arrow ((>>>))
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Foldable
import Data.Functor (($>))
import Data.List (sortOn, nub)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Text (Text, pack, unpack)
import Data.Tuple.Extra (first)
import Data.Void
import Tau.Comp.Type.Substitution
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util hiding (parens, pipe, brackets)
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

indent2 :: Parser ()
indent2 = newline *> char ' ' *> char ' ' $> ()

spaces :: Parser ()
spaces = Lexer.space
    (void (char ' ' <|> char '\t') <|> try indent2)
    (Lexer.skipLineComment "--")
    (Lexer.skipBlockComment "{-" "-}")

--spaces_ :: Parser ()
--spaces_ = Lexer.space
--    space1
--    (Lexer.skipLineComment "--")
--    (Lexer.skipBlockComment "{-" "-}")

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
    , "letfix"
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

--dot1 a b = do
--    traceShow a
--      $ traceShow b
--        $ dotExpr () a b

operator :: [[Operator Parser ProgExpr]]
operator = 
    [
--      [ Postfix dotSuffix
      [ InfixL (dotExpr () <$ symbol ".")
      --[ InfixL (dot1 <$ symbol ".")
      ]
      -- 10
--    , [ InfixL (app <$ spaces)
--      ]
      -- 9
    , [ InfixR (op2Expr () (OLArr ()) <$ symbol "<<")
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
    , [ InfixL (op2Expr () (OAdd ()) <$ try (symbol "+" <* notFollowedBy (symbol "+")))
      , InfixL (op2Expr () (OSub ()) <$ symbol "-")
      ]
      -- 5
    , [ InfixR (listConsExpr () <$ symbol "::")
      , InfixR (op2Expr () (OScc ()) <$ symbol "++")
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
      , InfixN (op2Expr () (OOpt ()) <$ symbol "?")
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

app :: (Show p, Show q, Show r, Show n, Show o) => Expr () p q r n o c d -> Expr () p q r n o c d -> Expr () p q r n o c d
app e f =  
    case project e of
--        EDot _ a b    -> dotExpr () a (app b f)
        ECon _ con as -> conExpr () con (as <> [f])
        EApp _ es     -> appExpr () (es <> [f])
        _             -> appExpr () [e, f]

-- ============================================================================
-- == Prims
-- ============================================================================

unit :: Parser Prim
unit = symbol "()" $> TUnit

bool :: Parser Prim
bool = true <|> false
  where
    true  = keyword "True"  $> TBool True
    false = keyword "False" $> TBool False

integral :: Parser Prim
integral = do
    n <- lexeme Lexer.decimal
    pure $ if n > maxInt || n < minInt
        then TInteger n
        else TInt (fromIntegral n)
  where
    maxInt = fromIntegral (maxBound :: Int)
    minInt = fromIntegral (minBound :: Int)

float :: Parser Prim
float = TFloat <$> lexeme Lexer.float

number :: Parser Prim
number = try float <|> integral

charLit :: Parser Prim
charLit = TChar <$> surroundedBy (symbol "'") printChar

stringLit :: Parser Prim
stringLit = lexeme (TString . pack <$> chars) where
    chars = char '\"' *> manyTill Lexer.charLiteral (char '\"')

literal :: Parser Prim
literal = unit
    <|> bool
    <|> number
    <|> charLit
    <|> stringLit

-- ============================================================================
-- == Expressions
-- ============================================================================


--dotSuffix :: Parser (ProgExpr -> ProgExpr)
--dotSuffix = do
--    item <- symbol "." *> expr
--    pure $ \e -> 
--        case project item of
--            EDot () f g -> dotExpr () (dotExpr () e f) g
--            _           -> dotExpr () e item

--expr :: Parser ProgExpr
--expr = makeExprParser exprToken operator

expr :: Parser ProgExpr
expr = makeExprParser parser operator
  where
    parser :: Parser ProgExpr
    parser = do
        tok <- some exprToken
        case tok of
            [e] -> pure e
            []  -> fail "Not a valid expression"
            es  -> pure (foldl1 app es) -- pure (appExpr () es)

exprToken :: Parser ProgExpr
exprToken = ifClause 
    <|> fixBinding
    <|> letBinding
    <|> matchWith
    <|> lambda
    <|> funExpr
    <|> litExpr () <$> literal
    <|> listExpr
    <|> recordExpr
    <|> tupleExpr
    <|> (varExpr () <$> name)
    <|> (conExpr () <$> constructor_ <*> pure [])
    <|> parens expr

listExpr :: Parser ProgExpr
listExpr = lstExpr () <$> elements expr

tupleExpr :: Parser ProgExpr
tupleExpr = do
    elems <- components expr
    pure $ case elems of
        [e] -> e
        []  -> litExpr () TUnit
        _   -> tupExpr () elems

recordExpr :: Parser ProgExpr
recordExpr = recExpr () <$> fields "=" expr

funExpr :: Parser ProgExpr
funExpr = do
    keyword "fun" 
    patExpr () [] <$> clauses_

lambda :: Parser ProgExpr
lambda = do
    void (symbol "\\")
    try simple <|> patExpr () [] <$> clauses_
  where
    simple = do
        pats <- some patternExpr <* symbol "=>" 
        lamExpr () pats <$> expr <* notFollowedBy (symbol "|")
        
clauses_ :: Parser [Clause (Pattern () () ()) ProgExpr]
clauses_ = (:) <$> clause (void (optional pipe)) <*> many (clause pipe)

matchWith :: Parser ProgExpr
matchWith = do
    term <- keyword "match" *> expr
    patExpr () [term] <$> ((:) <$> clause with <*> many (clause pipe))

with :: Parser ()
with = void (keyword "with" *> optional pipe)

pipe :: Parser ()
pipe = void (symbol "|")

clause :: Parser () -> Parser (Clause (Pattern () () ()) ProgExpr)
clause sym = do 
    pat <- sym *> pattern_
    cond <- fromMaybe [] <$> optional when_
    symbol "=>" 
    term <- expr
    pure (Clause [pat] cond term)

--    pats <- sym *> some pattern_
--    cond <- fromMaybe [] <$> optional when_
--    term <- sym2 *> expr
--    pure (Clause pats cond term)

when_ :: Parser [ProgExpr]
when_ = keyword "when" *> (pure <$> expr)

--identifier :: Parser ProgExpr
--identifier = varExpr () <$> word (withInitial letterChar)

binding :: Parser (Binding (Pattern () () ()))
binding = try funBinding <|> normalBinding
  where
    funBinding = do
        fun <- name
        tok <- some patternExpr
        case tok of
            [] -> fail "Expected function arguments"
            ps -> pure (BFun fun ps)

    normalBinding = do
        BLet <$> pattern_

fixBinding :: Parser ProgExpr
fixBinding = do
    keyword "letfix"
    bind <- name
    term <- symbol  "="  *> expr
    body <- keyword "in" *> expr
    pure (fixExpr () bind term body)

letBinding :: Parser ProgExpr
letBinding = do
    keyword "let"
    bind <- binding
    term <- symbol  "="  *> expr
    body <- keyword "in" *> expr
    pure (letExpr () bind term body)

ifClause :: Parser ProgExpr
ifClause = do
    cond  <- keyword "if"   *> expr
    true  <- keyword "then" *> expr
    false <- keyword "else" *> expr
    pure (ifExpr () cond true false)

--literalExpr :: Parser ProgExpr
--literalExpr = litExpr () <$> literal

-- ============================================================================
-- == Types
-- ============================================================================

--type_ :: Parser (TypeT a)
type_ :: Parser Type
type_ = makeExprParser parser [[ InfixR (tArr <$ symbol "->") ]] where
    parser = do
        ts <- some typeExpr
        let kind = foldr1 kArr (fromJust . kindOf <$> ts)
        pure (setKind kind (foldl1 tApp ts))

setKind :: Kind -> TypeT a -> TypeT a
setKind k = project >>> \case
    TApp t1 t2 -> tApp (setKind k t1) t2
    TVar _ var -> tVar k var
    TCon _ con -> tCon k con
    t          -> embed t

--typeExpr :: Parser (TypeT a)
typeExpr :: Parser Type
typeExpr = tVar kTyp <$> name
    <|> tCon kTyp <$> constructor_
    <|> tupleType
    <|> recordType
    <|> parens type_

--tupleType :: Parser (TypeT a)
tupleType :: Parser Type
tupleType = do
    elems <- components type_
    case elems of
        [t] -> pure t
        []  -> fail "Not a type"
        _   -> pure (tTuple elems)

--recordType :: Parser (TypeT a)
recordType :: Parser Type
recordType = tRecord <$> fieldPairs ":" type_

-- ============================================================================
-- == Kinds
-- ============================================================================

kind :: Parser Kind
kind = makeExprParser parser [[ InfixR (kArr <$ symbol "->") ]] 
  where
    parser = parens kind <|> (symbol "*" $> kTyp)

-- ============================================================================
-- == Patterns
-- ============================================================================

pattern_ :: Parser (Pattern () () ())
pattern_ = makeExprParser parser
--    [ 
--      [ InfixR (orPat () <$ symbol "or") ]
--    , [ InfixR (listConsPat () <$ symbol "::") ]
--    , [ Postfix asPattern ]
--    ]
    [ 
      [ InfixR (orPat () <$ symbol "or") ]
    , [ Postfix asPattern ]
    , [ InfixR (listConsPat () <$ symbol "::") ]
    ]
  where
    parser :: Parser (Pattern () () ())
    parser = do
        tok <- some patternExpr
        case tok of
            [p] -> pure p
            (Fix (PCon () con _):args) -> 
                pure (conPat () con args)
            _ -> fail "Not a valid pattern"

patternExpr :: Parser (Pattern () () ())
patternExpr = wildcardPattern 
    <|> varPattern
    <|> conPattern
    <|> litPattern
    <|> listPattern
    <|> tuplePattern
    <|> recordPattern
    <|> parens pattern_

listPattern :: Parser (Pattern () () ())
listPattern = lstPat () <$> elements pattern_

asPattern :: Parser (Pattern () () () -> Pattern () () ())
asPattern = keyword "as" >> asPat () <$> name

--pattern_ :: Parser (Pattern ())
--pattern_ = do
--    tok <- some patternToken
--    case tok of
--        [p] -> pure p
--        (Fix (PCon () con _):args) -> 
--            pure (conPat () con args)
--        _ -> fail "Not a valid pattern"
--
--patternToken :: Parser (Pattern ())
--patternToken = makeExprParser patternExpr
--    [ [ InfixR (listConsPat <$ symbol "::") ]
--    , [ Postfix asPattern ]
--    , [ InfixN (orPat () <$ symbol "or") ]
--    ]
--
--asPattern :: Parser (Pattern () -> Pattern ())
--asPattern = keyword "as" >> asPat () <$> name
--
--listConsPat :: Pattern () -> Pattern () -> Pattern ()
--listConsPat hd tl = conPat () "(::)" [hd, tl]
--
--patternExpr :: Parser (Pattern ())
--patternExpr = varPattern
--    <|> conPattern
--    <|> litPattern
--    <|> tuplePattern
--    <|> recordPattern
--    <|> wildcardPattern
--    <|> parens pattern_

varPattern :: Parser (Pattern () () ())
varPattern = varPat () <$> name

conPattern :: Parser (Pattern () () ())
conPattern = do
    con <- constructor_
    pure (conPat () con [])

litPattern :: Parser (Pattern () () ())
litPattern = litPat () <$> literal

tuplePattern :: Parser (Pattern () () ())
tuplePattern = do
    elems <- components pattern_
    pure $ case elems of
        [p] -> p
        []  -> litPat () TUnit
        _   -> tupPat () elems

recordPattern :: Parser (Pattern () () ())
recordPattern = recPat () <$> fields "=" pattern_

wildcardPattern :: Parser (Pattern () () ())
wildcardPattern = symbol "_" $> anyPat ()

-- ============================================================================
-- == Combinators for lists and tuples
-- ============================================================================

commaSep :: Parser a -> Parser [a]
commaSep parser = parser `sepBy` symbol ","

elements :: Parser a -> Parser [a]
elements = brackets . commaSep 

components :: Parser a -> Parser [a]
components = parens . commaSep 

--list_ :: Parser (PatternExpr ())
--list_ = do
--    elems <- elements expr
--    pure (foldr cons (conExpr () "[]" []) elems)
--
--tuple :: Parser (PatternExpr ())
--tuple parser = do
--    elems <- components parser
--    pure $ case elems of
--        [e] -> e
--        []  -> litExpr () TUnit
--        _   -> conExpr () (tupleCon (length elems)) elems

-- ============================================================================
-- == Record combinators
-- ============================================================================

--record :: Parser (PatternExpr ())
--record = recExpr () <$> fields "=" expr

fields :: Text -> Parser a -> Parser (FieldSet () a)
fields sym parser = do 
    fs <- uncurry (Field ()) <$$> fieldPairs sym parser
    pure (fieldSet fs)

fieldPairs :: Text -> Parser a -> Parser [(Name, a)]
fieldPairs sym parser = do
    pairs <- symbol "{" *> (sortOn fst <$> field `sepBy1` symbol ",") <* symbol "}"
    when (hasDups (fst <$> pairs)) (fail "Duplicate field name in record")
    pure pairs
  where
    hasDups names = length names /= length (nub names)
    field = (,) <$> name <*> (symbol sym *> parser)

-- ============================================================================
-- == Algebraic data types
-- ============================================================================

datatype :: Parser Datatype
datatype = do
    keyword "type"
    tcon  <- constructor_
    tvars <- many name <* symbol "="
    prods <- prod `sepBy` symbol "|"
    pure (Sum tcon tvars prods)

prod :: Parser Product
prod = do
    data_ <- constructor_
    types <- many typeExpr
    pure (Prod data_ types)

-- ============================================================================
-- == Top-level definition
-- ============================================================================

-- fn 4 = 4 
-- fn x = 8
--   print abc 

-- fn x y =
--   x + y where
--     mu = f x
--   and
--     nu = g x
--
--

definition :: Parser Definition
definition = do
    ls@((fun, _):_) <- line `sepBy1` newline
    pure (Def fun (snd <$> ls) [])
  where
    line = do
        fun <- name
        tok <- many patternExpr
        cond <- fromMaybe [] <$> optional when_
        symbol "="
        term <- expr
        pure (fun, Clause tok cond term) -- ps, body) -- (Def fun ps body)
