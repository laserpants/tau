{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE EmptyDataDeriving     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Tau.Lang.Expr where

import Control.Arrow ((>>>))
import Control.Monad.Identity
import Data.List (sortOn)
import Data.Text (Text)
import Data.Types.Injective
import Tau.Util

-- | Language primitives
data Prim
    = TVoid
    | TUnit                   -- ^ Unit value
    | TBool Bool              -- ^ Booleans
    | TInt Int                -- ^ Bounded machine integers (32 or 64 bit)
    | TInteger Integer        -- ^ Arbitrary precision integers (bigint)
--    | TNat Integer            -- ^ Peano arithmetic natural numbers 
    | TFloat Float            -- ^ Single precision Floating point numbers 
    | TDouble Double          -- ^ Double precision Floating point numbers
    | TChar Char              -- ^ Chars
    | TString Text            -- ^ Strings
    deriving (Show, Eq, Ord)

-- | Record fields
data Field t a = Field
    { fieldTag   :: t
    , fieldName  :: Name
    , fieldValue :: a
    } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''Field
deriveEq1   ''Field

instance Injective (Field t a) (t, Name, a) where
    to (Field tag name value) = (tag, name, value)

instance Injective (t, Name, a) (Field t a) where
    to (tag, name, value) = Field tag name value

newtype FieldSet t a = FieldSet [Field t a]
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''FieldSet
deriveEq1   ''FieldSet

-- | Base functor for Pattern
data PatternF t f g a 
    = PVar t Name             -- ^ Variable pattern
    | PCon t Name [a]         -- ^ Constuctor pattern
    | PLit t Prim             -- ^ Literal pattern
    | PRec t (FieldSet t a)   -- ^ Record pattern
    | PTup t [a]              -- ^ Tuple pattern
    | PLst t [a]              -- ^ List pattern
    | PAs  t Name a           -- ^ As pattern
    | POr  t a a              -- ^ Or pattern
    | PAny t                  -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''PatternF
deriveEq1   ''PatternF

-- | Patterns
type Pattern t f g = Fix (PatternF t f g)

-- | Simple patterns
data Prep t
    = RCon t Name [Name]      -- ^ Simple constuctor pattern
    deriving (Show, Eq)

-- | Pattern match expression clause
data Clause p a = Clause [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Clause
deriveEq1   ''Clause

-- | Unary operators
data Op1 t
    = ONeg t                  -- ^ Unary negation
    | ONot t                  -- ^ Logical NOT

    -- TODO:
    -- xor

    deriving (Show, Eq)

-- | Binary operators
data Op2 t
    = OEq  t                  -- ^ Equal-to operator
    | ONEq t                  -- ^ Not-equal-to operator
    | OAnd t                  -- ^ Logical AND
    | OOr  t                  -- ^ Logical OR
    | OAdd t                  -- ^ Addition operator
    | OSub t                  -- ^ Subtraction operator
    | OMul t                  -- ^ Multiplication operator
    | ODiv t                  -- ^ Division operator
    | OPow t                  -- ^ Exponentiation operator
    | OLt  t                  -- ^ Strictly less-than operator
    | OGt  t                  -- ^ Strictly greater-than operator
    | OLtE t                  -- ^ Less-than-or-equal-to operator
    | OGtE t                  -- ^ Greater-than-or-equal-to operator
    | OLArr t                 -- ^ Function composition operator
    | ORArr t                 -- ^ Reverse function composition
    | OFPipe t                -- ^ Forward pipe operator
    | OBPipe t                -- ^ Reverse pipe operator

    -- TODO:
    -- integer division (//)
    -- modulo (%)
    -- string concatenation (++)

    deriving (Show, Eq)

-- | Let name-bindings
data Binding p
    = BLet p                  -- ^ Plain let
    | BFun Name [p]           -- ^ Let f x = e type-of binding
    deriving (Show, Eq)

deriveShow1 ''Binding
deriveEq1   ''Binding

-- TODO
-- data NoListSugar
-- data NoFunPats

-- | Base functor for Expr
data ExprF t p q r n o a
    = EVar t Name             -- ^ Variable
    | ECon t Name [a]         -- ^ Data constructor
    | ELit t Prim             -- ^ Literal value
    | EApp t [a]              -- ^ Function application
    | ELet t q a a            -- ^ Let expression
    | EFix t Name a a         -- ^ Recursive let
    | ELam t r a              -- ^ Lambda abstraction
    | EIf  t a a a            -- ^ If-clause
    | EPat t [a] [Clause p a] -- ^ Match and fun expressions
    | EOp1 t n a              -- ^ Unary operator
    | EOp2 t o a a            -- ^ Unary operator
    | EDot t a a              -- ^ Dot operator
    | ERec t (FieldSet t a)   -- ^ Records
    | ETup t [a]              -- ^ Tuples
    | ELst t [a]              -- ^ List literal
--  | EAnn Scheme a           -- ^ Type-annotated expression
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

-- | Expression language tagged term tree
type Expr t p q r n o = Fix (ExprF t p q r n o)

literalName :: Prim -> Name
literalName = \case
    TVoid        -> "Void"
    TUnit        -> "Unit"
    (TBool    _) -> "Bool"
    (TInt     _) -> "Int"
    (TInteger _) -> "Integer"
--    (TNat     _) -> "Nat"
    (TFloat   _) -> "Float"
    (TDouble  _) -> "Double"
    (TChar    _) -> "Char"
    (TString  _) -> "String"

-- | Return the precedence of a binary operator
opPrecedence :: Op2 t -> Int
opPrecedence = \case
    OEq    _ -> 4
    ONEq   _ -> 4
    OAnd   _ -> 3
    OOr    _ -> 2
    OAdd   _ -> 6
    OSub   _ -> 6
    OMul   _ -> 7
    ODiv   _ -> 7
    OPow   _ -> 8
    OLt    _ -> 4
    OGt    _ -> 4
    OLtE   _ -> 4
    OGtE   _ -> 4
    OLArr  _ -> 9
    ORArr  _ -> 9
    OFPipe _ -> 0
    OBPipe _ -> 0

-- | Operator associativity
data Assoc
    = AssocL                  -- ^ Operator is left-associative
    | AssocR                  -- ^ Operator is right-associative
    | AssocN                  -- ^ Operator is non-associative
    deriving (Show, Eq)

-- | Return the associativity of a binary operator
opAssoc :: Op2 t -> Assoc
opAssoc = \case
    OEq    _ -> AssocN
    ONEq   _ -> AssocN
    OAnd   _ -> AssocR
    OOr    _ -> AssocR
    OAdd   _ -> AssocL
    OSub   _ -> AssocL
    OMul   _ -> AssocL
    ODiv   _ -> AssocL
    OPow   _ -> AssocR
    OLt    _ -> AssocN
    OGt    _ -> AssocN
    OLtE   _ -> AssocN
    OGtE   _ -> AssocN
    ORArr  _ -> AssocL
    OLArr  _ -> AssocR
    OFPipe _ -> AssocL
    OBPipe _ -> AssocR

-- | Return the symbolic representation of a binary operator
op2Symbol :: Op2 t -> Name
op2Symbol = \case
    OEq    _ -> "=="
    ONEq   _ -> "/="
    OAnd   _ -> "&&"
    OOr    _ -> "||"
    OAdd   _ -> "+"
    OSub   _ -> "-"
    OMul   _ -> "*"
    ODiv   _ -> "/"
    OPow   _ -> "^"
    OLt    _ -> "<"
    OGt    _ -> ">"
    OLtE   _ -> "<="
    OGtE   _ -> ">="
    OLArr  _ -> "<<"
    ORArr  _ -> ">>"
    OFPipe _ -> "|>"
    OBPipe _ -> "<|"

fieldSet :: [Field t a] -> FieldSet t a
fieldSet fields = FieldSet (to <$> sortOn fieldName fields)

fieldList :: FieldSet t a -> [(t, Name, a)]
fieldList (FieldSet fields) = to <$> fields

lookupField :: Name -> FieldSet t a -> Maybe (t, a)
lookupField name (FieldSet fields) = lookup name fields 
  where
    lookup _ [] = Nothing
    lookup name ((Field t n val):fs) 
        | n == name = Just (t, val)
        | otherwise = lookup name fs 

exprTag :: Expr t p q r n o -> t
exprTag = project >>> \case
    EVar t _       -> t
    ECon t _ _     -> t
    ELit t _       -> t
    EApp t _       -> t
    ELet t _ _ _   -> t
    EFix t _ _ _   -> t
    ELam t _ _     -> t
    EIf  t _ _ _   -> t
    EPat t _ _     -> t
    EOp1 t _ _     -> t
    EOp2 t _ _ _   -> t
    EDot t _ _     -> t
    ERec t _       -> t
    ETup t _       -> t
    ELst t _       -> t

setExprTag :: t -> Expr t p q r n o -> Expr t p q r n o
setExprTag t = project >>> \case
    EVar _ a       -> varExpr t a
    ECon _ a b     -> conExpr t a b
    ELit _ a       -> litExpr t a
    EApp _ a       -> appExpr t a
    ELet _ p a b   -> letExpr t p a b
    EFix _ n a b   -> fixExpr t n a b
    ELam _ p a     -> lamExpr t p a
    EIf  _ a b c   -> ifExpr  t a b c
    EPat _ o a     -> patExpr t o a
    EOp1 _ o a     -> op1Expr t o a
    EOp2 _ a b c   -> op2Expr t a b c
    EDot _ a b     -> dotExpr t a b
    ERec _ a       -> recExpr t a
    ETup _ a       -> tupExpr t a
    ELst _ a       -> lstExpr t a

patternTag :: Pattern t f g -> t
patternTag = project >>> \case
    PVar t _       -> t
    PCon t _ _     -> t
    PLit t _       -> t
    PRec t _       -> t
    PTup t _       -> t
    PLst t _       -> t
    PAny t         -> t
    PAs  t _ _     -> t
    POr  t _ _     -> t

setPatternTag :: t -> Pattern t f g -> Pattern t f g
setPatternTag t = project >>> \case
    PVar _ a       -> varPat t a
    PCon _ a b     -> conPat t a b
    PLit _ a       -> litPat t a
    PRec _ s       -> recPat t s
    PTup _ a       -> tupPat t a
    PLst _ a       -> lstPat t a
    PAny _         -> anyPat t
    PAs  _ a b     -> asPat t a b
    POr  _ a b     -> orPat t a b

data PatternsExpanded 
    deriving (Show, Eq)

data PatternsDesugared 
    deriving (Show, Eq)

patternsExpanded :: Pattern t f g -> Pattern t PatternsExpanded g
patternsExpanded = cata $ \case
    PVar t a       -> varPat t a
    PCon t a b     -> conPat t a b
    PRec t s       -> recPat t s
    PTup t a       -> tupPat t a
    PLst t a       -> lstPat t a
    PAny t         -> anyPat t
    PAs  t a b     -> asPat t a b
    _              -> error "Implementation error"

patternsDesugared :: Pattern t f g -> Pattern t f PatternsDesugared
patternsDesugared = cata $ \case
    PVar t a       -> varPat t a
    PCon t a b     -> conPat t a b
    PAny t         -> anyPat t
    PAs  t a b     -> asPat t a b
    _              -> error "Implementation error"

clauseDesugared :: Clause (Pattern t f g) a -> Clause (Pattern t f PatternsDesugared) a
clauseDesugared (Clause ps ex e) = Clause (patternsDesugared <$> ps) ex e

op1Tag :: Op1 t -> t
op1Tag = \case
    ONeg   t -> t
    ONot   t -> t

op2Tag :: Op2 t -> t
op2Tag = \case
    OEq    t -> t 
    ONEq   t -> t
    OAnd   t -> t
    OOr    t -> t
    OAdd   t -> t
    OSub   t -> t
    OMul   t -> t
    ODiv   t -> t
    OPow   t -> t
    OLt    t -> t
    OGt    t -> t
    OLtE   t -> t
    OGtE   t -> t
    OLArr  t -> t
    ORArr  t -> t
    OFPipe t -> t
    OBPipe t -> t

patternVars :: Pattern t f g -> [(Name, t)]
patternVars = cata $ \case
    PVar t var           -> [(var, t)]
    PCon _ _ rs          -> concat rs
    PRec _ (FieldSet fs) -> fieldValue =<< fs
    PTup _ elems         -> concat elems
    PLst _ elems         -> concat elems
    POr  _ a b           -> a <> b
    PAs  _ _ a           -> a
    PLit _ _             -> []
    PAny _               -> []

type Ast t n o f g = Expr t (Pattern t f g) (Binding (Pattern t f g)) [Pattern t f g] n o

class MapT s t a b where
    mapTagsM :: (Monad m) => (s -> m t) -> a -> m b

instance (MapT s t a b) => MapT s t [a] [b] where
    mapTagsM = traverse . mapTagsM 

instance 
    ( MapT s t a b
    , MapT s t c d
    , MapT s t e f
    , MapT s t g h
    , MapT s t i j
    ) => MapT s t (Expr s a c e g i) (Expr t b d f h j) 
  where
    mapTagsM f = cata $ \case
        EVar t a -> 
            varExpr <$> f t <*> pure a
        ECon t a b -> 
            conExpr <$> f t <*> pure a <*> sequence b
        ELit t a -> 
            litExpr <$> f t <*> pure a
        EApp t a -> 
            appExpr <$> f t <*> sequence a
        ELet t c a b -> 
            letExpr <$> f t <*> mapTagsM f c <*> a <*> b
        EFix t n a b -> 
            fixExpr <$> f t <*> pure n <*> a <*> b
        ELam t p a -> 
            lamExpr <$> f t <*> mapTagsM f p <*> a
        EIf t a b c -> 
            ifExpr  <$> f t <*> a <*> b <*> c
        EOp1 t o a -> 
            op1Expr <$> f t <*> mapTagsM f o <*> a
        EOp2 t o a b -> 
            op2Expr <$> f t <*> mapTagsM f o <*> a <*> b
        EDot t a b -> 
            dotExpr <$> f t <*> a <*> b
        ETup t a -> 
            tupExpr <$> f t <*> sequence a 
        EPat t a cs -> do
            clauses <- traverse sequence cs 
            patExpr <$> f t <*> sequence a <*> traverse (mapTagsM f) clauses
        ERec t (FieldSet fs) -> do
            fields <- traverse sequence fs
            recExpr <$> f t <*> (FieldSet <$> traverse (mapTagsM f) fields)
        ELst t a ->
            lstExpr <$> f t <*> sequence a 

instance MapT s t (Pattern s f g) (Pattern t f g) where
    mapTagsM f = cata $ \case
        PVar t a -> 
            varPat <$> f t <*> pure a
        PCon t a b -> 
            conPat <$> f t <*> pure a <*> sequence b
        PLit t a -> 
            litPat <$> f t <*> pure a
        PAny t -> 
            anyPat <$> f t 
        PAs t a b -> 
            asPat  <$> f t <*> pure a <*> b
        POr t a b -> 
            orPat  <$> f t <*> a <*> b
        PRec t (FieldSet fs) -> do
            fields <- traverse sequence fs
            recPat <$> f t <*> (FieldSet <$> traverse (mapTagsM f) fields)
        PTup t elems ->
            tupPat <$> f t <*> sequence elems
        PLst t elems ->
            lstPat <$> f t <*> sequence elems

instance MapT s t (Prep s) (Prep t) where
    mapTagsM f = \case
        RCon t con ps -> RCon <$> f t <*> pure con <*> pure ps

instance MapT s t (Binding (Pattern s f g)) (Binding (Pattern t f g)) where
    mapTagsM f = \case
        BLet p      -> BLet <$> mapTagsM f p
        BFun fun ps -> BFun fun <$> traverse (mapTagsM f) ps

instance (MapT s t p q) => MapT s t (Clause p a) (Clause q a) where
    mapTagsM f (Clause p a b) = 
        Clause <$> mapTagsM f p <*> pure a <*> pure b

instance MapT s t (Op1 s) (Op1 t) where
    mapTagsM f = \case
        ONeg   t -> ONeg   <$> f t
        ONot   t -> ONot   <$> f t

instance MapT s t (Op2 s) (Op2 t) where
    mapTagsM f = \case
        OEq    t -> OEq    <$> f t 
        ONEq   t -> ONEq   <$> f t
        OAnd   t -> OAnd   <$> f t
        OOr    t -> OOr    <$> f t
        OAdd   t -> OAdd   <$> f t
        OSub   t -> OSub   <$> f t
        OMul   t -> OMul   <$> f t
        ODiv   t -> ODiv   <$> f t
        OPow   t -> OPow   <$> f t
        OLt    t -> OLt    <$> f t
        OGt    t -> OGt    <$> f t
        OLtE   t -> OLtE   <$> f t
        OGtE   t -> OGtE   <$> f t
        OLArr  t -> OLArr  <$> f t
        ORArr  t -> ORArr  <$> f t
        OFPipe t -> OFPipe <$> f t
        OBPipe t -> OBPipe <$> f t

instance MapT s t (Field s a) (Field t a) where
    mapTagsM f (Field t a b) = 
        Field <$> f t <*> pure a <*> pure b

mapTags :: (MapT s t a b) => (s -> t) -> a -> b
mapTags f = runIdentity . mapTagsM (pure . f)

varPat :: t -> Name -> Pattern t f g
varPat = embed2 PVar

conPat :: t -> Name -> [Pattern t f g] -> Pattern t f g
conPat = embed3 PCon

asPat :: t -> Name -> Pattern t f g -> Pattern t f g
asPat = embed3 PAs

orPat :: t -> Pattern t f g -> Pattern t f g -> Pattern t f g
orPat = embed3 POr

litPat :: t -> Prim -> Pattern t f g
litPat = embed2 PLit

recPat :: t -> FieldSet t (Pattern t f g) -> Pattern t f g
recPat = embed2 PRec

tupPat :: t -> [Pattern t f g] -> Pattern t f g
tupPat = embed2 PTup

lstPat :: t -> [Pattern t f g] -> Pattern t f g
lstPat = embed2 PLst

anyPat :: t -> Pattern t f g
anyPat = embed1 PAny

varExpr :: t -> Name -> Expr t p q r n o
varExpr = embed2 EVar

conExpr :: t -> Name -> [Expr t p q r n o] -> Expr t p q r n o
conExpr = embed3 ECon

litExpr :: t -> Prim -> Expr t p q r n o
litExpr = embed2 ELit

appExpr :: t -> [Expr t p q r n o] -> Expr t p q r n o
appExpr = embed2 EApp

letExpr :: t -> q -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
letExpr = embed4 ELet

fixExpr :: t -> Name -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
fixExpr = embed4 EFix

lamExpr :: t -> r -> Expr t p q r n o -> Expr t p q r n o
lamExpr = embed3 ELam

ifExpr :: t -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
ifExpr = embed4 EIf

patExpr :: t -> [Expr t p q r n o] -> [Clause p (Expr t p q r n o)] -> Expr t p q r n o
patExpr = embed3 EPat

op1Expr :: t -> n -> Expr t p q r n o -> Expr t p q r n o
op1Expr = embed3 EOp1

op2Expr :: t -> o -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
op2Expr = embed4 EOp2

dotExpr :: t -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
dotExpr = embed3 EDot

recExpr :: t -> FieldSet t (Expr t p q r n o) -> Expr t p q r n o
recExpr = embed2 ERec

tupExpr :: t -> [Expr t p q r n o] -> Expr t p q r n o
tupExpr = embed2 ETup

lstExpr :: t -> [Expr t p q r n o] -> Expr t p q r n o
lstExpr = embed2 ELst

-- List cons constructors

listConsExpr :: t -> Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
listConsExpr t hd tl = conExpr t "(::)" [hd, tl]

listConsPat :: t -> Pattern t f g -> Pattern t f g -> Pattern t f g
listConsPat t hd tl = conPat t "(::)" [hd, tl]
