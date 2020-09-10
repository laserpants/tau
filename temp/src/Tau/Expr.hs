{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Expr where

import Data.Eq.Deriving
import Data.Text (Text)
import Tau.Type
import Tau.Util
import Text.Show.Deriving

-- | Language primitives
data Prim
    = Unit                   -- ^ Unit value
    | Bool Bool              -- ^ Booleans
    | Int Int                -- ^ Machine-level integers (32 or 64 bit)
    | Integer Integer        -- ^ Arbitrary precision integers
    | Float Double           -- ^ Floating point numbers
    | Char Char              -- ^ Chars
    | String Text            -- ^ Strings
    deriving (Show, Eq)

data PatternF a
    = VarP Name              -- ^ Variable pattern
    | ConP Name [a]          -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Pattern = Fix PatternF

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)

-- | Source language expression tree
data ExprF a
    = VarS Name
    | LamS Name a
    | AppS [a]
    | LitS Prim
    | LetS Name a a
    | RecS Name a a
    | IfS a ~a ~a
    | MatchS a [MatchClause a]
    | LamMatchS [MatchClause a]
    | OpS (OpF a)
    | AnnS a Scheme
    | ErrS
    deriving (Show, Eq, Functor, Foldable, Traversable)

type MatchClause a = (Pattern, a)

type Expr = Fix ExprF

-- | Operators
data OpF a
    = AddS a a
    | SubS a a
    | MulS a a
    | DivS a a
    | EqS a a
    | LtS a a
    | GtS a a
    | NegS a
    | NotS a
    | OrS a ~a
    | AndS a ~a
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Op = OpF (Fix ExprF)

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)

$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)

-- ============================================================================
-- == Constructors
-- ============================================================================

varS :: Name -> Expr
varS = Fix . VarS

lamS :: Name -> Expr -> Expr
lamS a = Fix . LamS a

appS :: [Expr] -> Expr
appS = Fix . AppS

litS :: Prim -> Expr
litS = Fix . LitS

letS :: Name -> Expr -> Expr -> Expr
letS a1 a2 = Fix . LetS a1 a2

recS :: Name -> Expr -> Expr -> Expr
recS a1 a2 = Fix . RecS a1 a2

ifS :: Expr -> Expr -> Expr -> Expr
ifS a1 a2 a3 = Fix (IfS a1 a2 a3)

matchS :: Expr -> [MatchClause Expr] -> Expr
matchS a = Fix . MatchS a

lamMatchS :: [MatchClause Expr] -> Expr
lamMatchS = Fix . LamMatchS

opS :: OpF Expr -> Expr
opS = Fix . OpS

annS :: Expr -> Scheme -> Expr
annS a = Fix . AnnS a

errS :: Expr
errS = Fix ErrS

addS :: Expr -> Expr -> Expr
addS a1 a2 = opS (AddS a1 a2)

subS :: Expr -> Expr -> Expr
subS a1 a2 = opS (SubS a1 a2)

mulS :: Expr -> Expr -> Expr
mulS a1 a2 = opS (MulS a1 a2)

divS :: Expr -> Expr -> Expr
divS a1 a2 = opS (DivS a1 a2)

eqS :: Expr -> Expr -> Expr
eqS a1 a2 = opS (EqS a1 a2)

ltS :: Expr -> Expr -> Expr
ltS a1 a2 = opS (LtS a1 a2)

gtS :: Expr -> Expr -> Expr
gtS a1 a2 = opS (GtS a1 a2)

negS :: Expr -> Expr
negS = opS . NegS

notS :: Expr -> Expr
notS = opS . NotS

orS :: Expr -> Expr -> Expr
orS a1 a2 = opS (OrS a1 a2)

andS :: Expr -> Expr -> Expr
andS a1 a2 = opS (AndS a1 a2)

litUnit :: Expr
litUnit = litS Unit

litBool :: Bool -> Expr
litBool = litS . Bool

litInt :: Int -> Expr
litInt = litS . Int

litInteger :: Integer -> Expr
litInteger = litS . Integer

litFloat :: Double -> Expr
litFloat = litS . Float

litChar :: Char -> Expr
litChar = litS . Char

litString :: Text -> Expr
litString = litS . String

varP :: Name -> Pattern
varP = Fix . VarP

conP :: Name -> [Pattern] -> Pattern
conP a = Fix . ConP a

litP :: Prim -> Pattern
litP = Fix . LitP

anyP :: Pattern
anyP = Fix AnyP
