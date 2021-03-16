module Tau.Lang.Parser2 where

import Data.Text (Text, pack, unpack)
import Data.Void
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.Util
import Text.Megaparsec 

data Keyword
    = KLet
    | KIf
    deriving (Show, Eq, Ord)

data Symbol
    = SDot
    | SPipe
    | SLambda
    | SColon
    | SDoubleColon
    | SUnderscore
    | SComment
    deriving (Show, Eq, Ord)

data Tok
    = TKeyword Keyword
    | TLiteral Literal
    | TName Name
    | TConstructor Name
    | TSymbol Symbol
    | TNewline
    | TIndNewline
    | TSpace
    | TLeftParen
    | TRightParen
    | TLeftBracket
    | TRightBracket
    | TLeftBrace
    | TRightBrace
    | TCommentStart
    | TCommentEnd
    deriving (Show, Eq, Ord)

--

--expr2 :: Parser2 ProgExpr
--expr2 = ifClause2
--    <|> fixBinding2
--    <|> letBinding2
--
--ifClause2 = do
--    token TSpace
--    --Keyword KIf
--    undefined
--
--fixBinding2 = undefined
--
--letBinding2 = undefined
