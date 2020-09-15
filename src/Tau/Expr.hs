{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
module Tau.Expr where

import Control.Arrow ((>>>))
import Data.Eq.Deriving
import Data.Functor.Const
import Data.List (intersperse)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
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
    | NeqS a a
    | LtS a a
    | GtS a a
    | NegS a
    | NotS a
    | OrS a ~a
    | AndS a ~a
    | DotS a a
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Op = OpF (Fix ExprF)

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)

$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)

patternVars :: Pattern -> [Name]
patternVars = cata alg where
    alg :: Algebra PatternF [Name]
    alg (VarP v)    = [v]
    alg (ConP _ ps) = concat ps
    alg _           = []

-- ============================================================================
-- == Patterns
-- ============================================================================

-- | Predicate to check whether a pattern is /simple/. A simple pattern is
--     - a variable,
--     - a wildcard, or
--     - a constructor where all subpatterns are simple.
--
isSimple :: Pattern -> Bool
isSimple = cata alg where
    alg :: Algebra PatternF Bool
    alg AnyP        = True
    alg VarP{}      = True
    alg (ConP _ ps) = and ps
    alg _           = False

-- ============================================================================
-- == Annotated AST
-- ============================================================================

type AnnotatedAstF a = Const a :*: ExprF

-- | Annotated syntax tree
newtype AnnotatedAst a = AnnotatedAst
    { getAnnotatedAst :: Fix (AnnotatedAstF a)
    } deriving (Eq, Show)

instance (Substitutable a a) => Substitutable a (AnnotatedAst a) where
    apply sub = getAnnotatedAst >>> cata alg >>> AnnotatedAst where
        alg (Const ann :*: expr) = Fix (Const (apply sub ann) :*: expr)

toExpr :: AnnotatedAst a -> Expr
toExpr = cata (Fix . right) . getAnnotatedAst

getAnnotation :: AnnotatedAst a -> a
getAnnotation = getConst . left . unfix . getAnnotatedAst

updateAnnotation :: a -> AnnotatedAst a -> AnnotatedAst a
updateAnnotation ann tree = AnnotatedAst $ Fix (Const ann :*: expr) where
    expr = right $ unfix $ getAnnotatedAst tree

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

neqS :: Expr -> Expr -> Expr
neqS a1 a2 = opS (NeqS a1 a2)

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

dotS :: Expr -> Expr -> Expr
dotS a1 a2 = opS (DotS a1 a2)

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

-- ============================================================================
-- == Substitutable
-- ============================================================================

instance Substitutable Expr Expr where
    apply sub = para $ \case
        VarS var ->
            substituteWithDefault (varS var) var sub

        LamS var (expr, _) ->
            lamS var (apply (deleteFromSub var sub) expr)

        AppS exprs ->
            appS (snd <$> exprs)

        LitS prim ->
            litS prim

        LetS var (_, body) (expr, _) ->
            letS var body (apply (deleteFromSub var sub) expr)

        RecS var (body, _) (expr, _) ->
            let deleteVarIn = apply (deleteFromSub var sub)
             in recS var (deleteVarIn body) (deleteVarIn expr)

        IfS cond true false ->
            ifS (snd cond) (snd true) (snd false)

        MatchS (_, expr) clss ->
            matchS expr (uncurry substituteClause <$> clss)

        LamMatchS clss ->
            lamMatchS (uncurry substituteClause <$> clss)

        OpS op ->
            opS (snd <$> op)

        AnnS (_, expr) ty ->
            annS expr ty

        ErrS ->
            errS

      where
        substituteClause pat (expr, _) =
            ( pat
            , apply (deleteManyFromSub (patternVars pat) sub) expr )

-- ============================================================================
-- == Pretty Printing
-- ============================================================================

instance Pretty Expr where
    pretty = prettyExpr 0

prettyExpr :: Int -> Expr -> Doc a
prettyExpr n = unfix >>> \case
    VarS name ->
        pretty name

    LamS name body ->
        wrap n $ backslash <> pretty name <+> "=>" <+> pretty body

    AppS [expr] ->
        prettyExpr n expr

    AppS exprs ->
        wrap n $ hsep (prettyExpr (succ n) <$> exprs)

    LitS prim ->
        pretty prim

    LetS name expr body ->
        wrap n $ "let"
        <+> pretty name <+> equals
        <+> pretty expr <+> "in"
        <+> pretty body

    RecS name expr body ->
        wrap n $ "let rec"
        <+> pretty name <+> equals
        <+> pretty expr <+> "in"
        <+> pretty body

    IfS cond true false ->
        wrap n $ "if"
        <+> pretty cond <+> "then"
        <+> pretty true <+> "else"
        <+> pretty false

    MatchS expr (cls:clss) ->
        wrap n $ "match" <+> pretty expr <+> "with" <+> prettyMatch cls clss

    LamMatchS (cls:clss) ->
        wrap n $ backslash <> "match" <+> prettyMatch cls clss

    OpS ops ->
        wrap n $ prettyOp 0 ops

    AnnS expr ty ->
        wrap n $ pretty expr <+> colon <+> pretty ty

    ErrS ->
        "<<error>>"

    MatchS expr [] ->
        wrap n $ "match" <+> pretty expr <+> equals <+> "{}"

    LamMatchS [] ->
        wrap n $ backslash <> "match" <+> equals <+> "{}"

wrap :: Int -> Doc a -> Doc a
wrap 0 doc = doc
wrap _ doc = parens doc

prettyMatch :: MatchClause Expr -> [MatchClause Expr] -> Doc a
prettyMatch cls clss =
    clause cls
        <> (if not (null clss) then space else mempty)
        <> hsep (clause <$> clss)
  where
    clause (pat, expr) = pipe <+> pretty pat <+> "=>" <+> pretty expr

prettyOp :: Int -> Op -> Doc a
prettyOp n = \case
    EqS a b  -> pretty a <+> "==" <+> pretty b
    NeqS a b -> pretty a <+> "/=" <+> pretty b
    AddS a b -> hsep (intersperse "+" (next <$> flattenOp AddOp [a, b]))
    MulS a b -> hsep (intersperse "*" (next <$> flattenOp MulOp [a, b]))
    AndS a b -> hsep (intersperse "&&" (next <$> flattenOp AndOp [a, b]))
    OrS a b  -> hsep (intersperse "||" (next <$> flattenOp OrOp [a, b]))
    DivS a b -> next a <+> "/" <+> next b
    SubS a b -> next a <+> "-" <+> next b
    LtS a b  -> next a <+> "<" <+> next b
    GtS a b  -> next a <+> ">" <+> next b
    DotS a b -> next a <> "." <> next b
    NegS a   -> "-" <> next a
    NotS a   -> "not" <+> next a
  where
    next = prettyExpr (succ n)

data OpType = AddOp | MulOp | AndOp | OrOp deriving (Eq, Show)

flattenOp :: OpType -> [Fix ExprF] -> [Expr]
flattenOp _ [] = []
flattenOp op (x:xs) =
    case unfix x of
        OpS (AddS a b) | AddOp == op -> flattenOp op [a, b] <> rest
        OpS (MulS a b) | MulOp == op -> flattenOp op [a, b] <> rest
        OpS (AndS a b) | AndOp == op -> flattenOp op [a, b] <> rest
        OpS (OrS a b)  | OrOp  == op -> flattenOp op [a, b] <> rest
        _ -> x:rest
  where
    rest = flattenOp op xs

instance Pretty Prim where
    pretty = \case
        Unit      -> "()"
        Bool b    -> pretty b
        Int n     -> pretty n
        Integer n -> pretty n
        Float f   -> pretty f
        Char c    -> squotes (pretty c)
        String s  -> dquotes (pretty s)

instance Pretty Pattern where
    pretty = unfix >>> \case
        ConP name ps@(_:_) -> pretty name <+> hsep (prettyPattern . unfix <$> ps)
        pat                -> prettyPattern pat

prettyPattern :: PatternF (Fix PatternF) -> Doc a
prettyPattern = \case
    VarP name    -> pretty name
    LitP prim    -> pretty prim
    ConP name [] -> pretty name
    con@ConP{}   -> parens $ pretty (Fix con)
    AnyP         -> "_"
