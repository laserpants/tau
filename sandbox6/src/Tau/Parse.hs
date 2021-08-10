{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Parse where

import Control.Arrow ((<<<), (>>>))
import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Supply
import Control.Monad.Trans (lift)
import Data.Foldable (foldlM)
import Data.Function ((&))
import Data.Functor (($>))
import Data.Functor.Foldable
import Data.Maybe (fromMaybe, fromJust)
import Data.Text (Text, pack, unpack, strip)
import Data.Void
import Tau.Misc
import Tau.Util hiding (parens, brackets, braces, commaSep)
import Text.Megaparsec
import Text.Megaparsec.Char
import TextShow
import qualified Text.Megaparsec.Char as Megaparsec
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = ParsecT Void Text (Supply Int)

runParserStack
  :: ParsecT Void Text (Supply Int) a
  -> String
  -> Text
  -> Either (ParseErrorBundle Text Void) a
runParserStack p s t = runSupplyNats (runParserT p s (strip t))

-------------------------------------------------------------------------------

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
keyword tok = Megaparsec.string tok
    *> notFollowedBy alphaNumChar
    *> spaces

reserved :: [Text]
reserved =
    [ "and"
    , "as"
    , "else"
    , "fun"
    , "if"
    , "in"
    , "let"
    , "match"
    , "or"
    , "otherwise"
    , "then"
    , "where"
    , "when"
    , "with"
    ]

word :: Parser Text -> Parser Text
word parser = lexeme $ try $ do
    var <- parser
    if var `elem` reserved
        then fail ("Reserved word " <> unpack var)
        else pure var

-------------------------------------------------------------------------------

nameParser :: Parser Text
nameParser = word (withInitial (lowerChar <|> char '_'))

constructorParser :: Parser Name
constructorParser = word (withInitial upperChar)

commaSep :: Parser a -> Parser [a]
commaSep parser = parser `sepBy1` symbol ","

elements :: Parser a -> Parser [a]
elements = brackets . commaSep

components :: Parser a -> Parser [a]
components = parens . commaSep

fields :: Name -> Parser a -> Parser [(Name, a)]
fields stor parser = commaSep $ (,) <$> nameParser <*> (symbol stor *> parser)

rowParser
  :: Text
  -> Parser a
  -> (Name -> a -> a -> a)
  -> (Name -> a)
  -> a
  -> Parser a
rowParser stor parser rowCon varCon empty = braces $ do
    pairs <- fields stor parser
    rest <- optional (symbol "|" *> nameParser)
    pure $ case pairs of
        [] -> empty
        (label, value):row -> do
            let next = maybe empty varCon rest
            foldr (uncurry rowCon) (rowCon label value next) row

argParser :: Parser p -> Parser [p]
argParser parser = components parser >>= \case
    [] -> fail "Expected one or more function arguments"
    ps -> pure ps

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------

kindVar :: Parser Kind
kindVar = lift (kVar . ("k" <>) . showt <$> supply)

typeParser :: Parser Type
typeParser = makeExprParser (try (parens typeParser) <|> parser)
    [[ InfixR (tArr <$ symbol "->") ]]
  where
    parser = do
        (t:ts) <- some typeFragmentParser
        foldlM (\s t -> kindVar >>= \k -> pure (tApp k s t)) t ts

typeFragmentParser :: Parser Type
typeFragmentParser = tVar <$> kindVar <*> nameParser
    <|> builtIn
    <|> tCon <$> kindVar <*> constructorParser
    <|> tTuple <$> components typeParser
    <|> recordTypeParser
  where
    recordTypeParser :: Parser Type
    recordTypeParser =
        symbol "{}" $> tRecord tRowNil
            <|> tRecord <$> rowParser ":" typeParser tRow (tVar kRow) tRowNil

    builtIn :: Parser Type
    builtIn = builtInType "Integer" kTyp
          <|> builtInType "Int"     kTyp
          <|> builtInType "Unit"    kTyp
          <|> builtInType "Bool"    kTyp
          <|> builtInType "Float"   kTyp
          <|> builtInType "Double"  kTyp
          <|> builtInType "Char"    kTyp
          <|> builtInType "String"  kTyp
          <|> builtInType "Nat"     kTyp
          <|> builtInType "List"    kFun
          <|> builtInType "Option"  kFun

    builtInType :: Name -> Kind -> Parser Type
    builtInType name kind = keyword name $> tCon kind name

-------------------------------------------------------------------------------

datatypeParser :: Parser Datatype
datatypeParser = do
    keyword "type"
    Sum <$> constructorParser
        <*> many nameParser <* symbol "="
        <*> productParser `sepBy` symbol "|"

productParser :: Parser Product
productParser =
    Mul <$> constructorParser
        <*> many (insertKinds <$> (try (parens typeParser) <|> typeFragmentParser))

insertKinds :: Type -> Type
insertKinds = go kTyp
  where
    go :: Kind -> Type -> Type
    go k = project >>> \case
        TVar _ var   -> tVar k var
        TCon _ con   -> tCon k con
        TRow lab a b -> tRow lab (insertKinds a) (setKind kRow b)
        TArr a b     -> tArr (insertKinds a) (insertKinds b)
        TApp _ a b   -> tApp k (go (kArr k1 k) a) rhs
          where
            k1 = case project a of
                TCon _ "#"  -> kRow
                _           -> kTyp
            rhs = case project (insertKinds b) of
                TCon _ "{}" -> tCon kRow "{}"
                t           -> setKind kTyp (embed t)

    setKind :: Kind -> Type -> Type
    setKind k = project >>> \case
        TVar _ var   -> tVar k var
        TCon _ con   -> tCon k con
        TApp _ a b   -> tApp k a b
        t            -> embed t

-------------------------------------------------------------------------------

annPatternParser :: Parser (ProgPattern () Type)
annPatternParser = makeExprParser (try (parens annPatternParser) <|> patternParser)
    [[ Postfix (symbol ":" *> (annPat <$> typeParser)) ]]

patternParser :: Parser (ProgPattern () Type)
patternParser = makeExprParser (try (parens patternParser) <|> parser)
    [ [ InfixR (orPat () <$ symbol "or") ]
    , [ Postfix parseAsPattern ]
    , [ InfixR (listPatCons () <$ symbol "::") ] ]
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
    parseVar       = varPat   () <$> nameParser
    parseLit       = litPat   () <$> primParser
    parseTuple     = tuplePat () <$> components annPatternParser
    parseCon       = conPat   () <$> constructorParser
                                 <*> (fromMaybe [] <$> optional (components annPatternParser))

    parseList =
        try (brackets spaces $> conPat () "[]" [])
            <|> listPat () <$> elements annPatternParser

    parseRecord =
        try (braces spaces $> recordPat () (conPat () "{}" []))
            <|> recordPat () <$> rowParser "=" annPatternParser (rowPat ()) (varPat ()) (conPat () "{}" [])

-------------------------------------------------------------------------------

operator :: [[Operator Parser (ProgExpr () Type)]]
operator =
    [
      [ Postfix postfixFunArgParser ]
      -- 10
    , [ InfixL (symbol "." $> flip (op2Expr () (ODot ())))
      ]
      -- 9
    , [ InfixR (op2Expr () (OLarr ()) <$ symbol "<<")
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
      , InfixR (op2Expr () (OStr ()) <$ symbol "++")
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
    , [ InfixL (op2Expr () (OFpip ()) <$ symbol "|>")
      , InfixR (op2Expr () (OBpip ()) <$ symbol "<|")
      ]
    ]

postfixFunArgParser :: Parser (ProgExpr () Type -> ProgExpr () Type)
postfixFunArgParser = do
    args <- try (parens spaces $> [litExpr () TUnit]) <|> argParser annExprParser
    pure (\fun -> appExpr () (fun:args))

annExprParser :: Parser (ProgExpr () Type)
annExprParser = makeExprParser (try lambdaParser <|> try (parens annExprParser) <|> exprParser)
    [ [ Postfix postfixFunArgParser ]
    , [ Postfix (symbol ":" *> (annExpr <$> typeParser)) ] ]

lambdaParser :: Parser (ProgExpr () Type)
lambdaParser =
    lamExpr () <$> (try (argParser annPatternParser) <|> pure <$> annPatternParser)
               <*> (symbol "=>" *> annExprParser)

exprParser :: Parser (ProgExpr () Type)
exprParser = makeExprParser parseItem operator
  where
    parseItem = try lambdaParser
        <|> try (parens exprParser)
        <|> parser

    parser = parseIf
--        <|> parseFun
--        <|> parseLet
--        <|> parseMatch
        <|> symbol "_" $> holeExpr ()
        <|> parseVar
        <|> parseLit
        <|> parseCon
        <|> parseList
        <|> parseTuple
        <|> parseRecord

    parseIf = ifExpr ()
        <$> (keyword "if"   *> annExprParser)
        <*> (keyword "then" *> annExprParser)
        <*> (keyword "else" *> annExprParser)

    parseVar       = varExpr   () <$> nameParser
    parseLit       = litExpr   () <$> primParser
    parseTuple     = tupleExpr () <$> components exprParser
    parseCon       = conExpr   () <$> constructorParser
                                  <*> (fromMaybe [] <$> optional (components annExprParser))

    parseList =
        try (brackets spaces $> conExpr () "[]" [])
            <|> listExpr () <$> elements annExprParser

    parseRecord =
        try (braces spaces $> recordExpr () (conExpr () "{}" []))
            <|> recordExpr () <$> rowParser "=" annExprParser (rowExpr ()) (varExpr ()) (conExpr () "{}" [])

