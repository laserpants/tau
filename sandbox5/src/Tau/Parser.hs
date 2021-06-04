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

parseRow :: Parser a -> (() -> Name -> a -> Maybe b -> b) -> Parser b
parseRow parser rowCon = do
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
    parseRecord    = recordPat () <$> parseRow patternParser rowPat

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

operator :: [[Operator Parser (ProgExpr ())]]
operator = 
    [

      -- 5
      [ InfixR (listExprCons () <$ symbol "::")
      ]

    , [ Postfix (symbol ":" *> (annExpr <$> typeParser)) ]
    ]

exprParser :: Parser (ProgExpr ())
exprParser  = makeExprParser parser operator
  where
    parser = parseIf
--      <|> parseFix
      <|> parseLet
--      <|> parseMatch
      <|> parseLam
--      <|> parseFun
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

    parseFunLet    = BFun () <$> nameParser <*> argParser
    parseNormalLet = BLet () <$> patternParser
    parseLam       = lamExpr () <$> argParser <*> (symbol "=>" *> exprParser)
    parseFix       = undefined
    parseMatch     = undefined
    parseFun       = undefined
    parseVar       = varExpr () <$> nameParser
    parseLit       = litExpr () <$> primParser
    parseList      = listExpr () <$> elements exprParser
    parseTuple     = tupleExpr () <$> components exprParser
    parseCon       = conExpr () <$> constructorParser <*> components exprParser
    parseRecord    = recordExpr () <$> parseRow exprParser rowExpr

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- TODO
typeParser :: Parser Type
typeParser = do
    symbol "Int"
    pure tInt
