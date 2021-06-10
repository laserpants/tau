{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Parser where

import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, unpack)
import Tau.Lang
import Tau.Tooling hiding (parens, brackets, braces, commaSep)
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
fields sep parser = commaSep $ (,) <$> nameParser <*> (symbol sep *> parser)

rowParser 
  :: Parser a 
  -> (() -> Name -> a -> a -> a) 
  -> (() -> Name -> a) 
  -> (() -> a) 
  -> Parser a
rowParser parser rowCon varCon empty = braces $ do
    pairs <- fields "=" parser
    rest  <- optional (symbol "|" *> nameParser)
    let next = maybe (empty ()) (varCon ()) rest
    case pairs of
        (label, value):row -> 
            pure (foldr (uncurry (rowCon ())) (rowCon () label value next) row)

        _ -> 
            fail "Empty record"

argParser :: Parser p -> Parser [p]
argParser parser = components parser >>= \case 
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

annPatternParser :: Parser (ProgPattern ())
annPatternParser = makeExprParser (try (parens annPatternParser) <|> patternParser) 
    [[ Postfix (symbol ":" *> (annPat <$> typeParser)) ]]

patternParser :: Parser (ProgPattern ())
patternParser = makeExprParser (try (parens patternParser) <|> parser)
    [ [ InfixR (orPat () <$ symbol "or") ]
    , [ Postfix parseAsPattern ]
    , [ InfixR (listPatCons () <$ symbol "::") ]
    ]
  where
    parser = parseWildcard
      <|> parseVar
      <|> parseLit
      <|> parseCon
      <|> parseList
      <|> parseTuple
      <|> parseRecord

    parseWildcard  = symbol "_" $> anyPat ()
    parseAsPattern = keyword "as" >> asPat () <$> nameParser
    parseVar       = varPat () <$> nameParser
    parseLit       = litPat () <$> primParser
    parseList      = listPat () <$> elements annPatternParser
    parseTuple     = tuplePat () <$> components annPatternParser
    parseCon       = conPat () <$> constructorParser 
                               <*> (fromMaybe [] <$> optional (components annPatternParser))
    parseRecord    = recordPat () <$> rowParser annPatternParser rowPat varPat emptyRowPat

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
    , [ Postfix postfixFunArgParser
      ]
    , [ Postfix postfixDotAppParser
      ]
    ]

postfixDotAppParser :: Parser (ProgExpr () -> ProgExpr ())
postfixDotAppParser = do
    fun <- symbol "." *> annExprParser
    pure (\expr -> appExpr () [fun, expr])

postfixFunArgParser :: Parser (ProgExpr () -> ProgExpr ())
postfixFunArgParser = do
    args <- argParser annExprParser
    pure (\fun -> appExpr () (fun:args))

annExprParser :: Parser (ProgExpr ())
annExprParser = makeExprParser (try lambdaParser <|> try (parens annExprParser) <|> exprParser)
    [[ Postfix (symbol ":" *> (annExpr <$> typeParser)) ]]

exprParser :: Parser (ProgExpr ())
exprParser = makeExprParser (try lambdaParser <|> try (parens exprParser) <|> parser) operator
  where
    parser = parseIf
      <|> parseFun
--      <|> parseFix
      <|> parseLet
      <|> parseMatch
      <|> parseVar
      <|> parseLit
      <|> parseCon
      <|> parseList
      <|> parseTuple
      <|> parseRecord

    parseApp = do
        fun  <- nameParser
        args <- argParser annExprParser
        pure (appExpr () (varExpr () fun:args))

    parseIf = ifExpr () 
        <$> (keyword "if"   *> annExprParser)
        <*> (keyword "then" *> annExprParser)
        <*> (keyword "else" *> annExprParser)

    parseLet = do
        keyword "let"
        bind <- try parseFunLet <|> parseNormalLet
        expr <- parseLetRhs <* symbol "in"
        letExpr () bind expr <$> annExprParser

    parseLetRhs = try (funExpr () <$> some parseClause) 
        <|> (symbol "=" *> annExprParser)

    parseMatch = patExpr () 
        <$> (keyword "match" *> annExprParser)
        <*> (keyword "with" *> some parseClause)

    parseClause = 
        symbol "|" >> Clause ()
            <$> patternParser
            <*> (try guarded <|> nonGuarded)

    guarded = do
        iffs <- some iffClause
        last <- optional (keyword "otherwise" *> symbol "=>" *> annExprParser)
        pure (iffs <> maybe [] (pure . Guard []) last)

    iffClause = Guard 
        <$> (keyword "iff" *> (pure <$> exprParser) <* symbol "=>") 
        <*> annExprParser

    nonGuarded = do
        expr <- symbol "=>" *> annExprParser
        pure [Guard [] expr]

    parseFunLet    = BFun () <$> nameParser <*> argParser annPatternParser
    parseNormalLet = BLet () <$> annPatternParser
--    parseFix       = undefined
    parseFun       = keyword "fun" *> (funExpr () <$> some parseClause)
    parseVar       = varExpr () <$> nameParser
    parseLit       = litExpr () <$> primParser
    parseList      = listExpr () <$> elements annExprParser
    parseTuple     = tupleExpr () <$> components exprParser
    parseCon       = conExpr () <$> constructorParser 
                                <*> (fromMaybe [] <$> optional (components annExprParser))
    parseRecord    = recordExpr () <$> rowParser annExprParser rowExpr varExpr emptyRowExpr

lambdaParser :: Parser (ProgExpr ())
lambdaParser = lamExpr () <$> argParser patternParser <*> (symbol "=>" *> annExprParser)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- TODO
typeParser :: Parser Type
typeParser = makeExprParser (try (parens typeParser) <|> parser) 
    [[ InfixR (tArr <$ symbol "->") ]]
  where
    parser = do
        ts <- some typeFragmentParser
        --let kind = foldr1 kArr (fromJust . kindOf <$> ts)
        -- TODO
        pure (foldl1 foo ts)

foo = undefined

typeFragmentParser :: Parser Type
typeFragmentParser = tVar undefined <$> nameParser
    <|> tCon undefined <$> constructorParser
    -- tuple
    -- record

--setKind :: Kind -> TypeT a -> TypeT a
--setKind k = project >>> \case
--    TVar _ var   -> tVar k var
----    TCon _ con   -> tCon con
----    TRow _ a b   -> tRow kRow a b
----    TApp _ t1 t2 -> tApp k t1 t2
----    TArr   t1 t2 -> tArr t1 t2
