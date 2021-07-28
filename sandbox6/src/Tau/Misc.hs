{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE StandaloneDeriving #-}
module Tau.Misc where

import Data.Eq.Deriving
import Data.Fix
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Text (Text)
import Data.Void
import Text.Show.Deriving

-------------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------------

type Name = Text

type Algebra f a = f a -> a

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

--

embed1 :: (Corecursive t) => (t1 -> Base t t) -> t1 -> t
embed1 t a = embed (t a)

embed2 :: (Corecursive t) => (t1 -> t2 -> Base t t) -> t1 -> t2 -> t
embed2 t a b = embed (t a b)

embed3 :: (Corecursive t) => (t1 -> t2 -> t3 -> Base t t) -> t1 -> t2 -> t3 -> t
embed3 t a b c = embed (t a b c)

embed4 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t
embed4 t a b c d = embed (t a b c d)

embed5 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> t5 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t5 -> t
embed5 t a b c d e = embed (t a b c d e)

-------------------------------------------------------------------------------
-- Type
-------------------------------------------------------------------------------

data KindF a
    = KVar Name                          -- ^ Kind variable
    | KCon Name                          -- ^ Kind constructor
    | KArr a a                           -- ^ Kind of (higher order) type constructors

-- | Kind
type Kind = Fix KindF

data TypeF k i a 
    = TVar k Name                        -- ^ Type variable
    | TCon k Name                        -- ^ Type constructor
    | TRow Name a a                      -- ^ Row type
    | TApp k a a                         -- ^ Type application
    | TArr a a                           -- ^ Function type
    | TGen i                             -- ^ Quantified type variable

-- | Type 
type TypeT i = Fix (TypeF Kind i)

-- | Standalone type (a type that is not part of a type scheme)
type Type = TypeT Void

-- | A type which appears in a type scheme and therefore may contain quantified 
-- variables
type Polytype = TypeT Int

-------------------------------------------------------------------------------
-- Lang
-------------------------------------------------------------------------------

-- | Built-in language primitives
data Prim
    = TUnit                              -- ^ Unit value
    | TBool    Bool                      -- ^ Booleans
    | TInt     Int                       -- ^ Bounded machine integers (32 or 64 bit)
    | TInteger Integer                   -- ^ Arbitrary precision (big) integers
    | TFloat   Float                     -- ^ Single precision floating point numbers 
    | TDouble  Double                    -- ^ Double precision floating point numbers
    | TChar    Char                      -- ^ Chars
    | TString  Text                      -- ^ Strings
    | TSymbol  Name                      -- ^ Symbolic constant (language internal)

data PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 a
    = PVar    t1  Name                   -- ^ Variable pattern
    | PCon    t2  Name [a]               -- ^ Constuctor pattern
    | PAs     t3  Name a                 -- ^ As-pattern
    | PLit    t4  Prim                   -- ^ Literal pattern
    | PAny    t5                         -- ^ Wildcard pattern
    | POr     t6  a a                    -- ^ Or-pattern
    | PTuple  t7  [a]                    -- ^ Tuple pattern
    | PList   t8  [a]                    -- ^ List pattern
    | PRow    t9  Name a a               -- ^ Row pattern
    | PAnn    t10 a                      -- ^ Explicit type annotation

-- | Pattern
type Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 = Fix (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)

-- | Unary operators
data Op1 t
    = ONeg   t                           -- ^ Unary negation
    | ONot   t                           -- ^ Logical NOT

-- | Binary operators
data Op2 t
    = OEq    t                           -- ^ Equal-to operator
    | ONeq   t                           -- ^ Not-equal-to operator
    | OAnd   t                           -- ^ Logical AND
    | OOr    t                           -- ^ Logical OR
    | OAdd   t                           -- ^ Addition operator
    | OSub   t                           -- ^ Subtraction operator
    | OMul   t                           -- ^ Multiplication operator
    | ODiv   t                           -- ^ Division operator
    | OPow   t                           -- ^ Exponentiation operator
    | OMod   t                           -- ^ Modulo operator
    | OLt    t                           -- ^ Strictly less-than operator
    | OGt    t                           -- ^ Strictly greater-than operator
    | OLte   t                           -- ^ Less-than-or-equal-to operator
    | OGte   t                           -- ^ Greater-than-or-equal-to operator
    | OLarr  t                           -- ^ Function composition operator
    | ORarr  t                           -- ^ Reverse function composition
    | OFpp   t                           -- ^ Forward pipe operator
    | OBpp   t                           -- ^ Reverse pipe operator
    | OOpt   t                           -- ^ Option default operator
    | OStr   t                           -- ^ String concatenation operator
    | ODot   t                           -- ^ Dot operator
    | OField t                           -- ^ Field access operator

data ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4 a
    = EVar    t1  Name                   -- ^ Variable
    | ECon    t2  Name [a]               -- ^ Data constructor
    | ELit    t3  Prim                   -- ^ Literal value
    | EApp    t4  [a]                    -- ^ Function application
    | EFix    t5  Name a a               -- ^ Recursive let
    | ELam    t6  e1 a                   -- ^ Lambda abstraction
    | EIf     t7  a a a                  -- ^ If-clause
    | EPat    t8  a [e2 a]               -- ^ Match expressions
    | ELet    t9  e3 a a                 -- ^ Let expression
    | EFun    t10 [e4 a]                 -- ^ Fun expression
    | EOp1    t11 (Op1 t11) a            -- ^ Unary operator
    | EOp2    t12 (Op2 t12) a a          -- ^ Binary operator
    | ETuple  t13 [a]                    -- ^ Tuple
    | EList   t14 [a]                    -- ^ List literal
    | ERow    t15 Name a a               -- ^ Row expression
    | EHole   t16                        -- ^ Blank argument in partial function application
    | EAnn    t17 a                      -- ^ Explicit type annotation

-- | Language expression
type Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4 = 
    Fix (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)

-- | Name binding-part of let expressions
data Binding t p
    = BPat t p                           -- ^ Pattern binding
    | BFun t Name [p]                    -- ^ Function binding

-- | Pattern guard
data Guard a = Guard [a] a

-- | Pattern match clause
data Clause t p a = Clause
    { clauseTag      :: t
    , clausePatterns :: p
    , clauseGuards   :: [Guard a] }

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Type class instances for Kind

deriving instance (Show a) => 
    Show (KindF a)

deriving instance (Eq a) => 
    Eq (KindF a)

deriving instance (Ord a) => 
    Ord (KindF a)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

deriving instance Functor     KindF
deriving instance Foldable    KindF
deriving instance Traversable KindF

-- Type class instances for Type

deriving instance (Show k, Show i, Show a) => 
    Show (TypeF k i a)

deriving instance (Eq k, Eq i, Eq a) => 
    Eq (TypeF k i a)

deriving instance (Ord k, Ord i, Ord a) => 
    Ord (TypeF k i a)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

deriving instance Functor     (TypeF k i)
deriving instance Foldable    (TypeF k i)
deriving instance Traversable (TypeF k i)

-------------------------------------------------------------------------------

-- Type class instances for Prim

deriving instance Show Prim
deriving instance Eq   Prim
deriving instance Ord  Prim

-- Type class instances for Op1

deriving instance (Show t) => Show (Op1 t)
deriving instance (Eq   t) => Eq   (Op1 t)
deriving instance (Ord  t) => Ord  (Op1 t)

-- Type class instances for Op2

deriving instance (Show t) => Show (Op2 t)
deriving instance (Eq   t) => Eq   (Op2 t)
deriving instance (Ord  t) => Ord  (Op2 t)

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

deriving instance (Show t, Show p, Show a) => 
    Show (Clause t p a)

deriving instance (Eq t, Eq p, Eq a) => 
    Eq (Clause t p a)

deriving instance (Ord t, Ord p, Ord a) => 
    Ord (Clause t p a)

deriveShow1 ''Clause
deriveEq1   ''Clause
deriveOrd1  ''Clause

deriving instance Functor     (Clause t p)
deriving instance Foldable    (Clause t p)
deriving instance Traversable (Clause t p)

-- Type class instances for Expr

deriving instance (Show t1, Show t2, Show t3, Show t4, Show t5, Show t6, Show t7, Show t8, Show t9, Show t10, Show t11, Show t12, Show t13, Show t14, Show t15, Show t16, Show t17, Show e1, Show (e2 a), Show e3, Show (e4 a), Show a) =>
    Show (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4 a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6, Eq t7, Eq t8, Eq t9, Eq t10, Eq t11, Eq t12, Eq t13, Eq t14, Eq t15, Eq t16, Eq t17, Eq e1, Eq (e2 a), Eq e3, Eq (e4 a), Eq a) =>
    Eq (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4 a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6, Ord t7, Ord t8, Ord t9, Ord t10, Ord t11, Ord t12, Ord t13, Ord t14, Ord t15, Ord t16, Ord t17, Ord e1, Ord (e2 a), Ord e3, Ord (e4 a), Ord a) =>
    Ord (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4 a)

deriveShow1 ''ExprF
deriveEq1   ''ExprF
deriveOrd1  ''ExprF

deriving instance (Functor e2, Functor e4) =>
    Functor (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)

deriving instance (Foldable e2, Foldable e4) =>
    Foldable (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)

deriving instance (Traversable e2, Traversable e4) =>
    Traversable (ExprF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)

-------------------------------------------------------------------------------
-- Prog
-------------------------------------------------------------------------------

type ProgPattern t u = Pattern t t t t t t t t t u

type ProgBinding t u = Binding t (ProgPattern t u) 

type ProgExpr t u = Expr t t t t t t t t t t t t t t t t u 
    [ProgPattern t u] (Clause t (ProgPattern t u)) (ProgBinding t u) (Clause t [ProgPattern t u])

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

varExpr 
  :: (Functor e2, Functor e4) 
  => t1 
  -> Name 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
varExpr = embed2 EVar

annExpr
  :: (Functor e2, Functor e4)
  => t17
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
annExpr = embed2 EAnn

