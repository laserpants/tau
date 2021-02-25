{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Tau.Lang.Expr where

import Control.Arrow ((>>>))
import Data.List (sortOn)
import Data.Text (Text)
import Data.Types.Injective
import Tau.Util

-- | Language primitives
data Literal
    = LUnit                   -- ^ Unit value
    | LBool Bool              -- ^ Booleans
    | LInt Int                -- ^ Bounded machine integers (32 or 64 bit)
    | LInteger Integer        -- ^ Arbitrary precision integers (bigint)
    | LFloat Double           -- ^ Floating point numbers
    | LChar Char              -- ^ Chars
    | LString Text            -- ^ Strings
    deriving (Show, Eq)

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
data PatternF t a
    = PVar t Name             -- ^ Variable pattern
    | PCon t Name [a]         -- ^ Constuctor pattern
    | PLit t Literal          -- ^ Literal pattern
    | PRec t (FieldSet t a)   -- ^ Record pattern
    | PTup t [a]              -- ^ Tuple pattern
    | PAs  t Name a           -- ^ As pattern
    | POr  t a a              -- ^ Or pattern
    | PAny t                  -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''PatternF
deriveEq1   ''PatternF

-- | Patterns
type Pattern t = Fix (PatternF t)

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
data Op1 
    = ONeg                    -- ^ Unary negation
    | ONot                    -- ^ Logical NOT
    deriving (Show, Eq)

-- | Binary operators
data Op2 
    = OEq                     -- ^ Equal-to operator
    | ONEq                    -- ^ Not-equal-to operator
    | OAnd                    -- ^ Logical AND
    | OOr                     -- ^ Logical OR
    | OAdd                    -- ^ Addition operator 
    | OSub                    -- ^ Subtraction operator 
    | OMul                    -- ^ Multiplication operator 
    | ODiv                    -- ^ Division operator 
    | OPow                    -- ^ Exponentiation operator 
    | OLt                     -- ^ Strictly less-than operator 
    | OGt                     -- ^ Strictly greater-than operator 
    | OLtE                    -- ^ Less-than-or-equal-to operator 
    | OGtE                    -- ^ Greater-than-or-equal-to operator 
    | OLArr                   -- ^ Function composition operator 
    | ORArr                   -- ^ Reverse function composition 
    | OFPipe                  -- ^ Forward pipe operator 
    | OBPipe                  -- ^ Reverse pipe operator 
    deriving (Show, Eq)

-- | Let name-bindings
data Binding p 
    = BLet p                  -- ^ Plain let
    | BFun Name [p]           -- ^ Let f x = e type-of binding
    deriving (Show, Eq)

deriveShow1 ''Binding
deriveEq1   ''Binding

-- | Base functor for Expr  
data ExprF t p q r a
    = EVar t Name             -- ^ Variable
    | ECon t Name [a]         -- ^ Data constructor
    | ELit t Literal          -- ^ Literal value
    | EApp t [a]              -- ^ Function application
    | ELet t q a a            -- ^ Let expression
    | EFix t Name a a         -- ^ Recursive let
    | ELam t r a              -- ^ Lambda abstraction
    | EIf  t a a a            -- ^ If-clause
    | EPat t [a] [Clause p a] -- ^ Match and fun expressions
    | EOp1 t Op1 a            -- ^ Unary operator
    | EOp2 t Op2 a a          -- ^ Unary operator
    | EDot t Name a           -- ^ Dot operator
    | ERec t (FieldSet t a)   -- ^ Records
    | ETup t [a]              -- ^ Tuples
--  | EAnn Scheme a           -- ^ Type-annotated expression
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

-- | Expression language tagged term tree
type Expr t p q r = Fix (ExprF t p q r)

-- | Return the precedence of a binary operator
opPrecedence :: Op2 -> Int
opPrecedence = \case
    OEq    -> 4
    ONEq   -> 4    
    OAnd   -> 3   
    OOr    -> 2   
    OAdd   -> 6    
    OSub   -> 6
    OMul   -> 7
    ODiv   -> 7
    OPow   -> 8
    OLt    -> 4
    OGt    -> 4
    OLtE   -> 4    
    OGtE   -> 4
    OLArr  -> 1   
    ORArr  -> 1   
    OFPipe -> 1 
    OBPipe -> 1

-- | Operator associativity
data Assoc 
    = AssocL                  -- ^ Operator is left-associative 
    | AssocR                  -- ^ Operator is right-associative 
    | AssocN                  -- ^ Operator is non-associative 
    deriving (Show, Eq)

-- | Return the associativity of a binary operator
opAssoc :: Op2 -> Assoc
opAssoc = \case
    OEq    -> AssocN
    ONEq   -> AssocN    
    OAnd   -> AssocR
    OOr    -> AssocR   
    OAdd   -> AssocL    
    OSub   -> AssocL
    OMul   -> AssocL
    ODiv   -> AssocL
    OPow   -> AssocR
    OLt    -> AssocN
    OGt    -> AssocN
    OLtE   -> AssocN    
    OGtE   -> AssocN
    OLArr  -> AssocR   
    ORArr  -> AssocR   
    OFPipe -> AssocL 
    OBPipe -> AssocR

opSymbol :: Op2 -> Name
opSymbol = \case
    OEq    -> "=="
    ONEq   -> "/="    
    OAnd   -> "&&"
    OOr    -> "||"   
    OAdd   -> "+"    
    OSub   -> "-"
    OMul   -> "*"
    ODiv   -> "/"
    OPow   -> "^"
    OLt    -> "<"
    OGt    -> ">"
    OLtE   -> "<="    
    OGtE   -> ">="
    OLArr  -> "<<"   
    ORArr  -> ">>"   
    OFPipe -> "<|" 
    OBPipe -> "|>"

fieldSet :: [Field t a] -> FieldSet t a
fieldSet fields = FieldSet (to <$> sortOn fieldName fields)

exprTag :: Expr t p q r -> t
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

patternTag :: Pattern t -> t
patternTag = project >>> \case
    PVar t _       -> t
    PCon t _ _     -> t
    PLit t _       -> t
    PRec t _       -> t
    PTup t _       -> t
    PAny t         -> t
    PAs  t _ _     -> t
    POr  t _ _     -> t

patternVars :: Pattern t -> [(Name, t)]
patternVars = cata $ \case
    PVar t var           -> [(var, t)]
    PCon _ _ rs          -> concat rs
    PRec _ (FieldSet fs) -> fieldValue =<< fs
    PTup _ elems         -> concat elems
    POr  _ a b           -> a <> b
    PAs  _ _ a           -> a
    PLit _ _             -> []
    PAny _               -> []

varPat :: t -> Name -> Pattern t
varPat = embed2 PVar

conPat :: t -> Name -> [Pattern t] -> Pattern t
conPat = embed3 PCon

asPat :: t -> Name -> Pattern t -> Pattern t
asPat = embed3 PAs

orPat :: t -> Pattern t -> Pattern t -> Pattern t
orPat = embed3 POr

litPat :: t -> Literal -> Pattern t
litPat = embed2 PLit

recPat :: t -> FieldSet t (Pattern t) -> Pattern t
recPat = embed2 PRec

tupPat :: t -> [Pattern t] -> Pattern t
tupPat = embed2 PTup

anyPat :: t -> Pattern t
anyPat = embed1 PAny 

varExpr :: t -> Name -> Expr t p q r
varExpr = embed2 EVar

conExpr :: t -> Name -> [Expr t p q r] -> Expr t p q r
conExpr = embed3 ECon 

litExpr :: t -> Literal -> Expr t p q r
litExpr = embed2 ELit 

appExpr :: t -> [Expr t p q r] -> Expr t p q r
appExpr = embed2 EApp 

letExpr :: t -> q -> Expr t p q r -> Expr t p q r -> Expr t p q r
letExpr = embed4 ELet 

fixExpr :: t -> Name -> Expr t p q r -> Expr t p q r -> Expr t p q r
fixExpr = embed4 EFix

lamExpr :: t -> r -> Expr t p q r -> Expr t p q r
lamExpr = embed3 ELam

ifExpr :: t -> Expr t p q r -> Expr t p q r -> Expr t p q r -> Expr t p q r
ifExpr = embed4 EIf

patExpr :: t -> [Expr t p q r] -> [Clause p (Expr t p q r)] -> Expr t p q r
patExpr = embed3 EPat

op1Expr :: t -> Op1 -> Expr t p q r -> Expr t p q r
op1Expr = embed3 EOp1

op2Expr :: t -> Op2 -> Expr t p q r -> Expr t p q r -> Expr t p q r
op2Expr = embed4 EOp2

dotExpr :: t -> Name -> Expr t p q r -> Expr t p q r
dotExpr = embed3 EDot

recExpr :: t -> FieldSet t (Expr t p q r) -> Expr t p q r
recExpr = embed2 ERec

tupExpr :: t -> [Expr t p q r] -> Expr t p q r
tupExpr = embed2 ETup
