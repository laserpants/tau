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
name = word (withInitial (lowerChar <|> char '_'))

constructor :: Parser Name
constructor = word (withInitial upperChar)

-- ============================================================================
-- == Expression tree
-- ============================================================================

expr = undefined

-- ============================================================================
-- == Lists and Tuples
-- ============================================================================

components :: Parser a -> Parser [a]
components parser = symbol "(" *> parser `sepBy` symbol "," <* symbol ")"

-- ============================================================================
-- == Records
-- ============================================================================

record :: Parser (Expr () p q)
record = recExpr () <$> (uncurry (Field ()) <$$> fields "=" expr)

fields :: Text -> Parser a -> Parser [(Name, a)]
fields sym parser = do
    pairs <- symbol "{" *> (sortOn fst <$> field `sepBy1` symbol ",") <* symbol "}"
    when (hasDups (fst <$> pairs)) (fail "Duplicate field name in record")
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
    (keys, vals) <- unzip <$> fields ":" type_
    pure (foldl tApp (recordConstructor keys) vals)

predicate :: Parser a -> Parser (PredicateT a)
predicate p = InClass <$> constructor <*> p

-- ============================================================================
-- == Type scheme
-- ============================================================================

quantifier :: Parser [Name]
quantifier = keyword "forall" *> some name <* symbol "."

classConstraints :: Parser [PredicateT Name]
classConstraints = components (predicate name) <* symbol "=>"

scheme :: Parser Scheme
scheme = do
    vs <- fromMaybe [] <$> optional quantifier
    ps <- try classConstraints <|> pure []
    ty <- type_
    let (names, kinds) = unzip (filter (flip elem vs . fst) (typeVars ty))
        sub = Map.fromList (zip names [0..])
    preds <- traverse (substPredicate sub) ps
    pure (Forall kinds preds (subst sub (upgrade ty)))
  where
    subst :: Map Name Int -> PolyType -> PolyType
    subst map = cata $ \case
        TVar kind var -> 
            case Map.lookup var map of
                Nothing -> tVar kind var
                Just n  -> tGen n
        t -> Fix t

    substPredicate :: Map Name Int -> PredicateT Name -> Parser (PredicateT Int)
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

