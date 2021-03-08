{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Parser where

import Control.Monad (when, void)
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
-- == Kinds
-- ============================================================================

kind :: Parser Kind
kind = makeExprParser parser [[ InfixR (kArr <$ symbol "->") ]] 
  where
    parser = parens kind <|> (symbol "*" $> kTyp)

-- ============================================================================
-- == Literals
-- ============================================================================

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
-- == Expressions
-- ============================================================================


-- ============================================================================
-- == Patterns
-- ============================================================================

pattern_ :: Parser (Pattern ())
pattern_ = do
    tok <- some patternToken
    case tok of
        [p] -> pure p
        (Fix (PCon () con _):args) -> 
            pure (conPat () con args)
        _ -> fail "Not a valid pattern"

patternToken :: Parser (Pattern ())
patternToken = makeExprParser patternExpr
    [
      [ InfixR (patternListCons <$ symbol "::") ]
    , [ InfixR (asPattern <$ symbol "as") ]
    , [ InfixR (orPat () <$ symbol "or") ]
    ]

asPattern :: Pattern () -> Pattern () -> Pattern ()
asPattern pat name = 
    case project name of
        PVar () v -> asPat () v pat
        _         -> error "Hmm"       -- TODO

patternListCons :: Pattern () -> Pattern () -> Pattern ()
patternListCons hd tl = conPat () "(::)" [hd, tl]

patternExpr :: Parser (Pattern ())
patternExpr = varPattern
    <|> conPattern
    <|> litPattern
    <|> tuplePattern
    <|> recordPattern
    <|> wildcardPattern
    <|> parens pattern_

varPattern :: Parser (Pattern ())
varPattern = varPat () <$> name

conPattern :: Parser (Pattern ())
conPattern = do
    con <- constructor_
    pure (conPat () con [])

litPattern :: Parser (Pattern ())
litPattern = litPat () <$> literal

tuplePattern :: Parser (Pattern ())
tuplePattern = do
    elems <- components pattern_
    pure $ case elems of
        [p] -> p
        []  -> litPat () LUnit
        _   -> tupPat () elems

recordPattern :: Parser (Pattern ())
recordPattern = recPat () <$> fields "=" pattern_

wildcardPattern :: Parser (Pattern ())
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
--        []  -> litExpr () LUnit
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

