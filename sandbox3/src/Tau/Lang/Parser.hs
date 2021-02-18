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
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Util (Name, Fix(..), embed, project, cata, to, (<$$>))
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Type.Substitution as Sub
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
    , "in"
    , "if"
    , "then"
    , "else"
    , "match"
    , "with"
    , "fun"
    , "not"
    , "forall"
    , "True"
    , "False"
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

constructor :: Parser Name
constructor = word (withInitial upperChar)

-- ============================================================================
-- == Expression tree
-- ============================================================================

ast :: Parser (PatternExpr ())
ast = do
    app <- appExpr () <$> some atom
    pure $ case project app of
        EApp () [e] -> e
        _           -> app
  where
    atom = ifClause
        <|> letBinding
        <|> matchWith
        <|> funExpr
        <|> lambda
        <|> literalExpr
        <|> list_
        <|> record
        <|> tuple
        <|> identifier

expr :: Parser (PatternExpr ())
expr = flip makeExprParser operator $ do
    term <- ast
    dots <- many (symbol "." *> name)
    pure (foldl (flip (dotOp ())) term dots)

funExpr :: Parser (PatternExpr ())
funExpr = do
    keyword "fun" 
    patExpr () [] <$> ((:) <$> clause (void (optional (symbol "|"))) <*> many (clause pipe))

matchWith :: Parser (PatternExpr ())
matchWith = do
    terms <- keyword "match" *> commaSep expr
    patExpr () terms <$> ((:) <$> clause with <*> many (clause pipe))

with :: Parser ()
with = void $ keyword "with" *> optional (symbol "|")

pipe :: Parser ()
pipe = void (symbol "|")

clause :: Parser () -> Parser (Clause (Pattern ()) (PatternExpr ()))
clause sym = do
    pats <- sym *> commaSep pattern_
    cond <- fromMaybe [] <$> optional whens
    term <- symbol "=>" *> expr
    pure (Clause pats cond term)

whens :: Parser [PatternExpr ()]
whens = keyword "when" *> (pure <$> expr)

letBinding :: Parser (PatternExpr ())
letBinding = do
    keyword "let"
    pats <- many pattern_
    term <- symbol  "="  *> expr
    body <- keyword "in" *> expr
    case pats of
        [pat]                -> pure (letExpr () pat term body)
        (Fix (PVar () f):ps) -> pure (lFnExpr () f ps term body)
        _                    -> fail "Invalid let-expression"

ifClause :: Parser (PatternExpr ())
ifClause = do
    cond  <- keyword "if"   *> expr
    true  <- keyword "then" *> expr
    false <- keyword "else" *> expr
    pure (ifExpr () cond true false)

lambda :: Parser (PatternExpr ())
lambda = do
    void (symbol "\\")
    pats <- some pattern_
    body <- symbol "=>" *> expr
    pure (lamExpr () pats body)

identifier :: Parser (PatternExpr ())
identifier = varExpr () <$> word (withInitial letterChar)

literalExpr :: Parser (PatternExpr ())
literalExpr = litExpr () <$> literal

unit :: Parser Literal
unit = symbol "()" $> LUnit

bool :: Parser Literal
bool = true <|> false
  where
    true  = keyword "True"  $> LBool True
    false = keyword "False" $> LBool False

integral :: Parser Literal
integral = do
    n <- lexeme Lexer.decimal
    pure $ if n > maxInt || n < minInt
        then LInteger n
        else LInt (fromIntegral n)
  where
    maxInt = fromIntegral (maxBound :: Int)
    minInt = fromIntegral (minBound :: Int)

float :: Parser Literal
float = LFloat <$> lexeme Lexer.float

number :: Parser Literal
number = try float <|> integral

charLit :: Parser Literal
charLit = LChar <$> surroundedBy (symbol "'") printChar

stringLit :: Parser Literal
stringLit = lexeme (LString . pack <$> chars) where
    chars = char '\"' *> manyTill Lexer.charLiteral (char '\"')

literal :: Parser Literal
literal = bool
    <|> number
    <|> charLit
    <|> stringLit

-- ============================================================================
-- == Operators
-- ============================================================================

operator :: [[Operator Parser (PatternExpr ())]]
operator = 
    [
      -- 8
      [ InfixR (powOp () <$ symbol "^")
      ]
      -- 7
    , [ InfixL (mulOp () <$ symbol "*")
      , InfixL (divOp () <$ try (symbol "/" <* notFollowedBy (symbol "=")))
      ]
      -- 6
    , [ InfixL (addOp () <$ symbol "+")
      , InfixL (subOp () <$ symbol "-")
      ]
      -- 5
    , [ InfixR (cons <$ symbol "::")
      ]
      -- 4
    , [ InfixN (eqOp  () <$ symbol "==")
      , InfixN (nEqOp () <$ symbol "/=")
      , InfixN (ltOp  () <$ try (symbol "<" <* notFollowedBy (symbol "=")))
      , InfixN (gtOp  () <$ try (symbol ">" <* notFollowedBy (symbol "=")))
      , InfixN (ltEOp () <$ symbol "<=")
      , InfixN (gtEOp () <$ symbol ">=")
      ]
      -- 3
    , [ InfixR (andOp () <$ symbol "&&")
      ]
      -- 2
    , [ InfixR (orOp  () <$ symbol "||")
      ]
      -- 1
    , [ InfixR (lArrOp () <$ symbol "<<")
      , InfixR (rArrOp () <$ symbol ">>")
      , InfixL (fPipeOp () <$ symbol "|>")
      , InfixR (bPipeOp () <$ symbol "<|")
      ]
      -- 0
    , [
      ]
    ]

cons :: PatternExpr () -> PatternExpr () -> PatternExpr ()
cons hd tl = conExpr () "(::)" [hd, tl]

-- ============================================================================
-- == Patterns
-- ============================================================================

pattern_ :: Parser (Pattern ())
pattern_ = makeExprParser patternExpr [[ InfixR (patternCons <$ symbol "::") ]]

patternCons :: Pattern () -> Pattern () -> Pattern ()
patternCons hd tl = conPat () "(::)" [hd, tl]

patternExpr :: Parser (Pattern ())
patternExpr = wildcard
    <|> conPattern
    <|> litPattern
    <|> varPattern
    <|> listPattern
    <|> tuplePattern
    <|> recordPattern

varPattern :: Parser (Pattern ())
varPattern = varPat () <$> name

conPattern :: Parser (Pattern ())
conPattern = do
    con <- constructor
    pats <- many pattern_
    pure (conPat () con pats)

litPattern :: Parser (Pattern ())
litPattern = litPat () <$> literal

wildcard :: Parser (Pattern ())
wildcard = symbol "_" $> anyPat ()

listPattern :: Parser (Pattern ())
listPattern = do
    elems <- elements pattern_
    pure $ case elems of
        [] -> conPat () "[]" []
        _  -> conPat () "(::)" (elems <> [conPat () "[]" []])

tuplePattern :: Parser (Pattern ())
tuplePattern = do
    elems <- components pattern_
    pure $ case elems of
        [p] -> p
        []  -> litPat () LUnit
        _   -> conPat () (tupleCon (length elems)) elems

recordPattern :: Parser (Pattern ())
recordPattern = recPat () <$> fields "=" pattern_

-- ============================================================================
-- == Lists and Tuples
-- ============================================================================

commaSep :: Parser a -> Parser [a]
commaSep parser = parser `sepBy` symbol ","

elements :: Parser a -> Parser [a]
elements = brackets . commaSep 

components :: Parser a -> Parser [a]
components = parens . commaSep 

list_ :: Parser (PatternExpr ())
list_ = do
    elems <- elements expr
    pure (foldr cons (conExpr () "[]" []) elems)

tuple :: Parser (PatternExpr ())
tuple = do
    elems <- components expr
    pure $ case elems of
        []  -> litExpr () LUnit
        [e] -> e
        _   -> conExpr () (tupleCon (length elems)) elems

-- ============================================================================
-- == Records
-- ============================================================================

record :: Parser (PatternExpr ())
record = recExpr () <$> fields "=" expr

fields :: Text -> Parser a -> Parser [Field () a]
fields sym parser = uncurry (Field ()) <$$> fieldPairs sym parser

fieldPairs :: Text -> Parser a -> Parser [(Name, a)]
fieldPairs sym parser = do
    pairs <- symbol "{" *> (sortOn fst <$> field `sepBy1` symbol ",") <* symbol "}"
    when (hasDups (fst <$> pairs)) (fail "Duplicate field name in record")
    pure pairs
  where
    hasDups names = length names /= length (nub names)
    field = (,) <$> name <*> (symbol sym *> parser)

-- ============================================================================
-- == Type
-- ============================================================================

type_ :: Parser (TypeT a)
type_ = makeExprParser parser [[ InfixR (tArr <$ symbol "->") ]]
  where
    parser = do
        atoms <- some atom
        pure (foldl1 app atoms)

    atom = tVar kTyp <$> name
       <|> tCon kTyp <$> constructor
       <|> tupleType
       <|> recordType
       <|> parens type_

    app :: TypeT a -> TypeT a -> TypeT a
    app (Fix (TCon _ con)) t = tApp (tCon (kind t) con) t
    app (Fix (TVar _ var)) t = tApp (tVar (kind t) var) t
    app s                  t = tApp s t

    kind = kArr kTyp . fromJust . kindOf 

tupleType :: Parser (TypeT a)
tupleType = do
    elems <- components type_
    case elems of
        []  -> fail "Not a type"
        [t] -> pure t
        _   -> pure (tTuple elems)

recordType :: Parser (TypeT a)
recordType = do
    (keys, vals) <- unzip <$> fieldPairs ":" type_
    pure (tRecord keys vals)

predicate :: Parser a -> Parser (PredicateT a)
predicate p = InClass <$> constructor <*> p

-- ============================================================================
-- == Type scheme
-- ============================================================================

quantifier :: Parser [Name]
quantifier = keyword "forall" *> some name <* symbol "."

constraints :: Parser [PredicateT Name]
constraints = components (predicate name) <* symbol "=>"

scheme :: Parser Scheme
scheme = do
    vs <- fromMaybe [] <$> optional quantifier
    ps <- try constraints <|> pure []
    ty <- type_
    let (names, kinds) = unzip (filter (flip elem vs . fst) (typeVars ty))
        sub = Map.fromList (zip names [0..])
    preds <- traverse (substPredicate sub) ps
    pure (Forall kinds preds (subst sub (upgrade ty)))
  where
    subst :: Map Name Int -> PolyType -> PolyType
    subst map = cata $ \case
        TVar kind var -> maybe (tVar kind var) tGen (Map.lookup var map)
        t             -> embed t

    substPredicate :: Map Name Int -> PredicateT Name -> Parser PolyPredicate
    substPredicate map (InClass name var) = 
        case Map.lookup var map of
            Nothing -> fail ("Variable " <> Text.unpack var <> " does not appear bound in type")
            Just n  -> pure (InClass name n)

-- ============================================================================
-- == Kind
-- ============================================================================

kind :: Parser Kind
kind = makeExprParser parser [[ InfixR (kArr <$ symbol "->") ]] where
    parser = parens kind <|> (symbol "*" $> kTyp)

-- ============================================================================
-- == Adts
-- ============================================================================

-- ============================================================================
-- == Module
-- ============================================================================

