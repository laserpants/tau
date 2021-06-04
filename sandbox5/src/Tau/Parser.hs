{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Text (Text, pack, unpack)
import Tau.Lang
import Tau.Tool hiding (parens, brackets, braces, commaSep)
import Tau.Type
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char as Megaparsec
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = Parsec Void Text

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

spaces :: Parser ()
spaces = Lexer.space
    space1
    (Lexer.skipLineComment "--")
    (Lexer.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaces

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

surroundedBy :: Parser Text -> Parser a -> Parser a
surroundedBy parser = between parser parser

validChar :: Parser Char
validChar = alphaNumChar <|> char '_'

withInitial :: Parser Char -> Parser Text
withInitial parser = pack <$> ((:) <$> parser <*> many validChar)

keyword :: Text -> Parser ()
keyword tok =
    Megaparsec.string tok
        *> notFollowedBy alphaNumChar
        *> spaces

reserved :: [Text]
reserved =
    [ "and"
    , "as"
    , "else"
    , "forall"
    , "fun"
    , "if"
    , "iff"
    , "in"
    , "let"
    , "match"
    , "or"
    , "otherwise"
    , "then"
    , "where"
    , "with"
    ]

word :: Parser Text -> Parser Text
word parser = lexeme $ try $ do
    var <- parser
    if var `elem` reserved
        then fail ("Reserved word " <> unpack var)
        else pure var

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

nameParser :: Parser Text
nameParser = word (withInitial (lowerChar <|> char '_'))

constructorParser :: Parser Name
constructorParser = word (withInitial upperChar)

commaSep :: Parser a -> Parser [a]
commaSep parser = parser `sepBy` symbol ","

elements :: Parser a -> Parser [a]
elements = brackets . commaSep 

components :: Parser a -> Parser [a]
components = parens . commaSep 

fields :: Name -> Parser a -> Parser [(Name, a)]
fields sep parser = braces $ commaSep $ do
    label <- nameParser
    symbol sep
    value <- parser
    pure (label, value)

rowParser :: Parser a -> (() -> Name -> a -> Maybe b -> b) -> Parser b
rowParser parser rowCon = do
    pairs <- fields "=" parser
    case pairs of
        (label, value):ps -> pure (foldr fn (rowCon () label value Nothing) ps)
        _                 -> fail "Empty record"
  where
    fn a = uncurry (rowCon ()) a . Just

argParser :: Parser [ProgPattern ()]
argParser = components patternParser >>= \case 
    [] -> fail "Expected at least one function argument"
    ps -> pure ps

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

primParser :: Parser Prim
primParser = parseUnit
    <|> parseTrue 
    <|> parseFalse
    <|> parseChar
    <|> parseString
    <|> try parseFloat 
    <|> parseIntegral
  where
    parseUnit      = symbol "()" $> TUnit
    parseTrue      = keyword "True"  $> TBool True
    parseFalse     = keyword "False" $> TBool False
    parseChar      = TChar <$> surroundedBy (symbol "'") printChar
    parseString    = lexeme (TString . pack <$> chars)
    parseFloat     = TDouble <$> lexeme Lexer.float
    parseIntegral  = TInteger <$> lexeme Lexer.decimal
    chars          = char '\"' *> manyTill Lexer.charLiteral (char '\"')

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

patternParser :: Parser (ProgPattern ())
patternParser = makeExprParser parser
    [ [ InfixR (orPat () <$ symbol "or") ]
    , [ Postfix parseAsPattern ]
    , [ InfixR (listPatCons () <$ symbol "::") ]
    , [ Postfix (symbol ":" *> (annPat <$> typeParser)) ]
    ]
  where
    parser = parseWildcard
      <|> parseVar
      <|> parseLit
      <|> parseCon
      <|> parseList
      <|> try (parens patternParser) <|> parseTuple
      <|> parseRecord

    parseWildcard  = symbol "_" $> anyPat ()
    parseAsPattern = keyword "as" >> asPat () <$> nameParser
    parseVar       = varPat () <$> nameParser
    parseLit       = litPat () <$> primParser
    parseList      = listPat () <$> elements patternParser
    parseTuple     = tuplePat () <$> components patternParser
    parseCon       = conPat () <$> constructorParser <*> components patternParser
    parseRecord    = recordPat () <$> rowParser patternParser rowPat

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

operator :: [[Operator Parser (ProgExpr ())]]
operator = 
    [
      -- 9
      [ InfixR (op2Expr () (OLarr ()) <$ symbol "<<")
      , InfixL (op2Expr () (ORarr ()) <$ symbol ">>")
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
    , [ InfixR (listExprCons () <$ symbol "::")
      , InfixR (op2Expr () (OStrc ()) <$ symbol "++")
      ]
      -- 4
    , [ InfixN (op2Expr () (OEq ()) <$ symbol "==")
      , InfixN (op2Expr () (ONeq ()) <$ symbol "/=")
      , InfixN (op2Expr () (OLt ()) <$ try (symbol "<" <* notFollowedBy (symbol "=")))
      , InfixN (op2Expr () (OGt ()) <$ try (symbol ">" <* notFollowedBy (symbol "=")))
      , InfixN (op2Expr () (OLte ()) <$ symbol "<=")
      , InfixN (op2Expr () (OGte ()) <$ symbol ">=")
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
    , [ InfixL (op2Expr () (OFpipe ()) <$ symbol "|>")
      , InfixR (op2Expr () (OBpipe ()) <$ symbol "<|")
      ]
    , [ Postfix (symbol ":" *> (annExpr <$> typeParser)) ]
    ]

exprParser :: Parser (ProgExpr ())
exprParser = makeExprParser parser operator
  where
    parser = parseIf
      <|> parseFun
--      <|> parseFix
      <|> parseLet
      <|> parseMatch
      <|> parseLam
      <|> parseVar
      <|> parseLit
      <|> parseCon
      <|> parseList
      <|> try (parens exprParser) <|> parseTuple
      <|> parseRecord

    parseIf = ifExpr () 
        <$> (keyword "if"   *> exprParser)
        <*> (keyword "then" *> exprParser)
        <*> (keyword "else" *> exprParser)

    parseLet = do
        keyword "let"
        letExpr () 
            <$> (try parseFunLet <|> parseNormalLet)
            <*> (symbol "=" *> exprParser)
            <*> (keyword "in" *> exprParser)

    parseMatch = patExpr () 
        <$> (pure <$> (keyword "match" *> exprParser))
        <*> (keyword "with" *> some parseClause)

    parseClause = do
        symbol "|"
        Clause ()
            <$> (pure <$> patternParser)
            <*> (try guarded <|> nonGuarded)

    guarded = do
        iffs <- some iffClause
        last <- optional (keyword "otherwise" *> symbol "=>" *> exprParser)
        pure (iffs <> maybe [] (pure . Guard []) last)

    iffClause = Guard 
        <$> (keyword "iff" *> (pure <$> exprParser) <* symbol "=>") 
        <*> exprParser

    nonGuarded = do
        expr <- symbol "=>" *> exprParser
        pure [Guard [] expr]

    parseFunLet    = BFun () <$> nameParser <*> argParser
    parseNormalLet = BLet () <$> patternParser
    parseLam       = lamExpr () <$> argParser <*> (symbol "=>" *> exprParser)
    parseFix       = undefined
    parseFun       = keyword "fun" *> (funExpr () <$> some parseClause)
    parseVar       = varExpr () <$> nameParser
    parseLit       = litExpr () <$> primParser
    parseList      = listExpr () <$> elements exprParser
    parseTuple     = tupleExpr () <$> components exprParser
    parseCon       = conExpr () <$> constructorParser <*> components exprParser
    parseRecord    = recordExpr () <$> rowParser exprParser rowExpr

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- TODO
typeParser :: Parser Type
typeParser = do
    symbol "Int"
    pure tInt
