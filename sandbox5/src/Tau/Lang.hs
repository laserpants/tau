{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Lang where

import Tau.Row
import Tau.Tool

-- | Built-in language primitives
data Prim
    = TUnit                            -- ^ Unit value
    | TBool Bool                       -- ^ Booleans
    | TInt Int                         -- ^ Bounded machine integers (32 or 64 bit)
    | TInteger Integer                 -- ^ Arbitrary precision integers (BigInt)
    | TFloat Float                     -- ^ Single precision floating point numbers 
    | TDouble Double                   -- ^ Double precision floating point numbers
    | TChar Char                       -- ^ Chars
    | TString Text                     -- ^ Strings

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 a
    = PVar    t1 Name                  -- ^ Variable pattern
    | PCon    t2 Name [a]              -- ^ Constuctor pattern
    | PLit    t3 Prim                  -- ^ Literal pattern
    | PAs     t4 Name a                -- ^ As-pattern
    | POr     t5 a a                   -- ^ Or-pattern
    | PAny    t6                       -- ^ Wildcard pattern
    | PTuple  t7 [a]                   -- ^ Tuple pattern
    | PList   t8 [a]                   -- ^ List pattern
    | PRecord t9 (Row a)               -- ^ Record pattern

-- | Pattern
type Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 = Fix (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9)

type ProgPattern t = Pattern t t t t t t t t t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Unary operators
data Op1 t
    = ONeg t                           -- ^ Unary negation
    | ONot t                           -- ^ Logical NOT

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Binary operators
data Op2 t
    = OEq  t                           -- ^ Equal-to operator
    | ONeq t                           -- ^ Not-equal-to operator
    | OAnd t                           -- ^ Logical AND
    | OOr  t                           -- ^ Logical OR
    | OAdd t                           -- ^ Addition operator
    | OSub t                           -- ^ Subtraction operator
    | OMul t                           -- ^ Multiplication operator
    | ODiv t                           -- ^ Division operator
    | OPow t                           -- ^ Exponentiation operator
    | OMod t                           -- ^ Modulo operator
    | OLt  t                           -- ^ Strictly less-than operator
    | OGt  t                           -- ^ Strictly greater-than operator
    | OLte t                           -- ^ Less-than-or-equal-to operator
    | OGte t                           -- ^ Greater-than-or-equal-to operator
    | OLarr t                          -- ^ Function composition operator
    | ORarr t                          -- ^ Reverse function composition
    | OFpipe t                         -- ^ Forward pipe operator
    | OBpipe t                         -- ^ Reverse pipe operator
    | OOpt t                           -- ^ Option default operator
    | OStrc t                          -- ^ String concatenation operator
    | ONdiv t                          -- ^ Integral division

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Pattern guard
data Guard a = Guard [a] a

-- | Pattern matching clause
data Clause p a = Clause [p] [Guard a] 

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Name binding-part of let expressions
data Binding p
    = BLet p                           -- ^ Simple let-binding
    | BFun Name [p]                    -- ^ Function binding

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat a
    = EVar    t1  Name                 -- ^ Variable
    | ECon    t2  Name [a]             -- ^ Data constructor
    | ELit    t3  Prim                 -- ^ Literal value
    | EApp    t4  [a]                  -- ^ Function application
    | ELet    t5  bind a a             -- ^ Let expression
    | EFix    t6  Name a a             -- ^ Recursive let
    | ELam    t7  lam a                -- ^ Lambda abstraction
    | EIf     t8  a a a                -- ^ If-clause
    | EPat    t9  [a] [Clause pat a]   -- ^ Match expressions
    | EFun    t10 [Clause pat a]       -- ^ Fun expression
    | EOp1    t11 (Op1 t11) a          -- ^ Unary operator
    | EOp2    t12 (Op2 t12) a a        -- ^ Binary operator
    | ETuple  t13 [a]                  -- ^ Tuple
    | EList   t14 [a]                  -- ^ List literal
    | ERecord t15 (Row a)              -- ^ Record

-- | Language expression
type Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat = 
    Fix (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)

type ProgExpr t = Expr t t t t t t t t t t t t t t t (Binding (ProgPattern t)) [ProgPattern t] (ProgPattern t)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

newtype Ast t = Ast { getAst :: ProgExpr t }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances for Prim

deriving instance Show Prim
deriving instance Eq   Prim
deriving instance Ord  Prim

-- Type class instances for Pattern

deriving instance (Show t1, Show t2, Show t3, Show t4, Show t5, Show t6, Show t7, Show t8, Show t9, Show a) => 
    Show (PatternF  t1 t2 t3 t4 t5 t6 t7 t8 t9 a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6, Eq t7, Eq t8, Eq t9, Eq a) => 
    Eq (PatternF  t1 t2 t3 t4 t5 t6 t7 t8 t9 a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6, Ord t7, Ord t8, Ord t9, Ord a) => 
    Ord (PatternF  t1 t2 t3 t4 t5 t6 t7 t8 t9 a)

deriveShow1 ''PatternF
deriveEq1   ''PatternF
deriveOrd1  ''PatternF

deriving instance Functor     (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9)
deriving instance Foldable    (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9)
deriving instance Traversable (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9)

-- Type class instances for Guard

deriving instance (Show a) => Show (Guard a)
deriving instance (Eq   a) => Eq   (Guard a)
deriving instance (Ord  a) => Ord  (Guard a)

deriveShow1 ''Guard
deriveEq1   ''Guard
deriveOrd1  ''Guard

deriving instance Functor     Guard
deriving instance Foldable    Guard
deriving instance Traversable Guard

-- Type class instances for Clause

deriving instance (Show p, Show a) => 
    Show (Clause p a)

deriving instance (Eq p, Eq a) => 
    Eq (Clause p a)

deriving instance (Ord p, Ord a) => 
    Ord (Clause p a)

deriveShow1 ''Clause
deriveEq1   ''Clause
deriveOrd1  ''Clause

deriving instance Functor     (Clause p)
deriving instance Foldable    (Clause p)
deriving instance Traversable (Clause p)

-- Type class instances for Op1

deriving instance (Show t) => Show (Op1 t)
deriving instance (Eq   t) => Eq   (Op1 t)
deriving instance (Ord  t) => Ord  (Op1 t)

-- Type class instances for Op2

deriving instance (Show t) => Show (Op2 t)
deriving instance (Eq   t) => Eq   (Op2 t)
deriving instance (Ord  t) => Ord  (Op2 t)

-- Type class instances for Binding

deriving instance (Show p) => Show (Binding p)
deriving instance (Eq   p) => Eq   (Binding p)
deriving instance (Ord  p) => Ord  (Binding p)

deriveShow1 ''Binding
deriveEq1   ''Binding
deriveOrd1  ''Binding

-- Type class instances for Expr

deriving instance (Show t1, Show t2, Show t3, Show t4, Show t5, Show t6, Show t7, Show t8, Show t9, Show t10, Show t11, Show t12, Show t13, Show t14, Show t15, Show bind, Show lam, Show pat, Show a) =>
    Show (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6, Eq t7, Eq t8, Eq t9, Eq t10, Eq t11, Eq t12, Eq t13, Eq t14, Eq t15, Eq bind, Eq lam, Eq pat, Eq a) =>
    Eq (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6, Ord t7, Ord t8, Ord t9, Ord t10, Ord t11, Ord t12, Ord t13, Ord t14, Ord t15, Ord bind, Ord lam, Ord pat, Ord a) =>
    Ord (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat a)

deriveShow1 ''ExprF
deriveEq1   ''ExprF
deriveOrd1  ''ExprF

deriving instance Functor     (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)
deriving instance Foldable    (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)
deriving instance Traversable (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

deriving instance (Show t) => Show (Ast t)
deriving instance (Eq   t) => Eq   (Ast t)
deriving instance (Ord  t) => Ord  (Ast t)

instance Functor Ast where
    fmap f (Ast ast) = Ast (mapExpr ast)
      where 
        mapExpr = cata $ \case
            EVar t var        -> varExpr    (f t) var
            ECon t con es     -> conExpr    (f t) con es
            ELit t prim       -> litExpr    (f t) prim
            EApp t es         -> appExpr    (f t) es
            ELet t bind e1 e2 -> letExpr    (f t) (mapBind bind) e1 e2
            EFix t name e1 e2 -> fixExpr    (f t) name e1 e2
            ELam t ps e       -> lamExpr    (f t) (mapPattern <$> ps) e
            EIf t e1 e2 e3    -> ifExpr     (f t) e1 e2 e3
            EPat t es cs      -> patExpr    (f t) es (mapClause <$> cs)
            EFun t cs         -> funExpr    (f t) (mapClause <$> cs)
            EOp1 t op a       -> op1Expr    (f t) (mapOp1 op) a
            EOp2 t op a b     -> op2Expr    (f t) (mapOp2 op) a b
            ETuple t es       -> tupleExpr  (f t) es
            EList t es        -> listExpr   (f t) es
            ERecord t row     -> recordExpr (f t) row

        mapBind = \case
            BLet p            -> BLet (mapPattern p)
            BFun name ps      -> BFun name (mapPattern <$> ps)

        mapClause = \case
            Clause ps gs      -> Clause (mapPattern <$> ps) gs

        mapPattern = cata $ \case
            PVar    t var     -> varPat    (f t) var
            PCon    t con ps  -> conPat    (f t) con ps
            PLit    t prim    -> litPat    (f t) prim
            PAs     t as p    -> asPat     (f t) as p
            POr     t p q     -> orPat     (f t) p q
            PAny    t         -> anyPat    (f t)
            PTuple  t ps      -> tuplePat  (f t) ps
            PList   t ps      -> listPat   (f t) ps
            PRecord t row     -> recordPat (f t) row

        mapOp1 = \case
            ONeg t            -> ONeg   (f t)
            ONot t            -> ONot   (f t)

        mapOp2 = \case
            OEq  t            -> OEq    (f t)
            ONeq t            -> ONeq   (f t)
            OAnd t            -> OAnd   (f t)
            OOr  t            -> OOr    (f t)
            OAdd t            -> OAdd   (f t)
            OSub t            -> OSub   (f t)
            OMul t            -> OMul   (f t)
            ODiv t            -> ODiv   (f t)
            OPow t            -> OPow   (f t)
            OMod t            -> OMod   (f t)
            OLt  t            -> OLt    (f t)
            OGt  t            -> OGt    (f t)
            OLte t            -> OLte   (f t)
            OGte t            -> OGte   (f t)
            OLarr t           -> OLarr  (f t)
            ORarr t           -> ORarr  (f t)
            OFpipe t          -> OFpipe (f t)
            OBpipe t          -> OBpipe (f t)
            OOpt t            -> OOpt   (f t)
            OStrc t           -> OStrc  (f t)
            ONdiv t           -> ONdiv  (f t)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Pattern

varPat :: t1 -> Name -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
varPat = embed2 PVar

conPat :: t2 -> Name -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9] -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
conPat = embed3 PCon

litPat :: t3 -> Prim -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
litPat = embed2 PLit

asPat :: t4 -> Name -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
asPat = embed3 PAs

orPat :: t5 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
orPat = embed3 POr

anyPat :: t6 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
anyPat = embed1 PAny

tuplePat :: t7 -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9] -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
tuplePat = embed2 PTuple

listPat :: t8 -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9] -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
listPat = embed2 PList

recordPat :: t9 -> Row (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9) -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
recordPat = embed2 PRecord

-- Expr

varExpr :: t1 -> Name -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
varExpr = embed2 EVar

conExpr :: t2 -> Name -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
conExpr = embed3 ECon

litExpr :: t3 -> Prim -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
litExpr = embed2 ELit

appExpr :: t4 -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
appExpr = embed2 EApp

letExpr :: t5 -> bind -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
letExpr = embed4 ELet

fixExpr :: t6 -> Name -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
fixExpr = embed4 EFix

lamExpr :: t7 -> lam -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
lamExpr = embed3 ELam

ifExpr :: t8 -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
ifExpr = embed4 EIf

patExpr :: t9 -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat] -> [Clause pat (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
patExpr = embed3 EPat

funExpr :: t10 -> [Clause pat (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat)] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
funExpr = embed2 EFun

op1Expr :: t11 -> Op1 t11 -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
op1Expr = embed3 EOp1

op2Expr :: t12 -> Op2 t12 -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat ->Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
op2Expr = embed4 EOp2

tupleExpr :: t13 -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
tupleExpr = embed2 ETuple

listExpr :: t14 -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat] -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
listExpr = embed2 EList

recordExpr :: t15 -> Row (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat) -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
recordExpr = embed2 ERecord

-- List cons constructors

listConsExpr :: t2 -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat
listConsExpr t hd tl = conExpr t "(::)" [hd, tl]

listConsPat :: t2 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
listConsPat t hd tl = conPat t "(::)" [hd, tl]

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

exprTag :: ProgExpr t -> t
exprTag = cata $ \case
    EVar    t _     -> t
    ECon    t _ _   -> t
    ELit    t _     -> t
    EApp    t _     -> t
    ELet    t _ _ _ -> t
    EFix    t _ _ _ -> t
    ELam    t _ _   -> t
    EIf     t _ _ _ -> t
    EPat    t _ _   -> t
    EFun    t _     -> t
    EOp1    t _ _   -> t
    EOp2    t _ _ _ -> t
    ETuple  t _     -> t
    EList   t _     -> t
    ERecord t _     -> t

patternTag :: ProgPattern t -> t
patternTag = cata $ \case
    PVar    t _     -> t
    PCon    t _ _   -> t
    PLit    t _     -> t 
    PAs     t _ _   -> t
    POr     t _ _   -> t
    PAny    t       -> t
    PTuple  t _     -> t
    PList   t _     -> t
    PRecord t _     -> t

op1Tag :: Op1 t -> t
op1Tag = \case
    ONeg    t       -> t
    ONot    t       -> t

op2Tag :: Op2 t -> t
op2Tag = \case
    OEq     t       -> t
    ONeq    t       -> t
    OAnd    t       -> t
    OOr     t       -> t
    OAdd    t       -> t
    OSub    t       -> t
    OMul    t       -> t
    ODiv    t       -> t
    OPow    t       -> t
    OMod    t       -> t
    OLt     t       -> t
    OGt     t       -> t
    OLte    t       -> t
    OGte    t       -> t
    OLarr   t       -> t
    ORarr   t       -> t
    OFpipe  t       -> t
    OBpipe  t       -> t
    OOpt    t       -> t
    OStrc   t       -> t
    ONdiv   t       -> t

astTag :: Ast t -> t
astTag = exprTag . getAst 
