{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
module Tau.Misc where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Control.Monad.Supply
import Data.Eq.Deriving
import Data.Fix (Fix)
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.List (nub, intersect)
import Data.Map.Strict (Map)
import Data.Ord.Deriving
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Void
import Tau.Env (Env)
import Tau.Util
import Text.Show.Deriving
import TextShow
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Env as Env

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

-- | Type class constraint
data PredicateT a = InClass Name a

-- | A standalone type class constraint
type Predicate = PredicateT Type

-- | Polymorphic type scheme
data Scheme = Forall [Kind] [PredicateT Int] Polytype

-- | Class of data types that carry type information
class Typed a where
    typeOf :: a -> Type

-- | Class of data types that contain free type variables
class FreeIn t where
    free :: t -> [(Name, Kind)]

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
    = PVar    t1 Name                    -- ^ Variable pattern
    | PCon    t2 Name [a]                -- ^ Constuctor pattern
    | PAs     t3 Name a                  -- ^ As-pattern
    | PLit    t4 Prim                    -- ^ Literal pattern
    | PAny    t5                         -- ^ Wildcard pattern
    | POr     t6 a a                     -- ^ Or-pattern
    | PTuple  t7 [a]                     -- ^ Tuple pattern
    | PList   t8 [a]                     -- ^ List pattern
    | PRow    t9 Name a a                -- ^ Row pattern
    | PAnn    t10 a                      -- ^ Explicit type annotation

-- | Pattern
type Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 = Fix (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)

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

-- | Pattern clause choice
data Choice a = Choice [a] a

-- | Pattern match clause
data Clause t p a = Clause
    { clauseTag      :: t
    , clausePatterns :: p
    , clauseChoices  :: [Choice a] }

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
    | OFpip  t                           -- ^ Forward pipe operator
    | OBpip  t                           -- ^ Reverse pipe operator
    | OOpt   t                           -- ^ Option default operator
    | OStr   t                           -- ^ String concatenation operator
    | ODot   t                           -- ^ Dot operator
    | OField t                           -- ^ Field access operator

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

-- Type class instances for Pattern

deriving instance (Show t1, Show t2, Show t3, Show t4, Show t5, Show t6, Show t7, Show t8, Show t9, Show t10, Show a) =>
    Show (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq t5, Eq t6, Eq t7, Eq t8, Eq t9, Eq t10, Eq a) =>
    Eq (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord t5, Ord t6, Ord t7, Ord t8, Ord t9, Ord t10, Ord a) =>
    Ord (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 a)

deriveShow1 ''PatternF
deriveEq1   ''PatternF
deriveOrd1  ''PatternF

deriving instance Functor     (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)
deriving instance Foldable    (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)
deriving instance Traversable (PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)

-- Type class instances for Op1

deriving instance (Show t) => Show (Op1 t)
deriving instance (Eq   t) => Eq   (Op1 t)
deriving instance (Ord  t) => Ord  (Op1 t)

-- Type class instances for Op2

deriving instance (Show t) => Show (Op2 t)
deriving instance (Eq   t) => Eq   (Op2 t)
deriving instance (Ord  t) => Ord  (Op2 t)

-- Type class instances for Binding

deriving instance (Show t, Show p) => Show (Binding t p)
deriving instance (Eq   t, Eq   p) => Eq   (Binding t p)
deriving instance (Ord  t, Ord  p) => Ord  (Binding t p)

deriveShow1 ''Binding
deriveEq1   ''Binding
deriveOrd1  ''Binding

-- Type class instances for Choice

deriving instance (Show a) => Show (Choice a)
deriving instance (Eq   a) => Eq   (Choice a)
deriving instance (Ord  a) => Ord  (Choice a)

deriveShow1 ''Choice
deriveEq1   ''Choice
deriveOrd1  ''Choice

deriving instance Functor     Choice
deriving instance Foldable    Choice
deriving instance Traversable Choice

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

newtype Ast t = Ast { astExpr :: ProgExpr t Void }

data TypeInfoT e t = TypeInfo
    { nodeErrors     :: e
    , nodeType       :: t
    , nodePredicates :: [Predicate] }

type TypeInfo e = TypeInfoT e Type

data ClassInfo p e = ClassInfo
    { classSignature  :: PredicateT p
    , classPredicates :: [PredicateT p]
    , classMethods    :: [(Name, e)] }

-- Environments

type Context = Env (Set Name)

type TypeEnv = Env Scheme

type KindEnv = Env Kind

type ClassEnv = Env
    ( ClassInfo Name Type                        -- Abstract interface
    , [ClassInfo Type (Ast (TypeInfo Void))] )   -- Instances

type ConstructorEnv = Env (Set Name, Int)

-------------------------------------------------------------------------------

-- Type class instances for Predicate

deriving instance (Show a) =>
    Show (PredicateT a)

deriving instance (Eq a) =>
    Eq (PredicateT a)

deriving instance (Ord a) =>
    Ord (PredicateT a)

deriveShow1 ''PredicateT
deriveEq1   ''PredicateT
deriveOrd1  ''PredicateT

deriving instance Functor     PredicateT
deriving instance Foldable    PredicateT
deriving instance Traversable PredicateT

-- Type class instances for Scheme

deriving instance Show Scheme
deriving instance Eq   Scheme
deriving instance Ord  Scheme

-- Type class instances for ClassInfo

deriving instance (Show p, Show e) => Show (ClassInfo p e)
deriving instance (Eq   p, Eq   e) => Eq   (ClassInfo p e)

-- Typed instances

instance Typed Type where
    typeOf = id

-- FreeIn instances

instance (FreeIn t) => FreeIn [t] where
    free = concatMap free

instance FreeIn (TypeT a) where
    free = nub . typeVars

instance FreeIn Scheme where
    free (Forall _ _ t) = free t

-------------------------------------------------------------------------------

-- Type class instances

instance (Typed t) => Typed (ProgExpr t u) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (ProgPattern t u) where
    typeOf = typeOf . patternTag

instance (Typed t) => Typed (Op1 t) where
    typeOf = typeOf . op1Tag

instance (Typed t) => Typed (Op2 t) where
    typeOf = typeOf . op2Tag

instance (Typed t) => Typed (Ast t) where
    typeOf = typeOf . astTag

deriving instance (Show e, Show t) =>
    Show (TypeInfoT e t)

deriving instance (Eq e, Eq t) =>
    Eq (TypeInfoT e t)

deriving instance Functor (TypeInfoT e)

instance (Typed t) => Typed (TypeInfoT e t) where
    typeOf = typeOf . nodeType

instance (Typed t) => Typed (Binding t p) where
    typeOf = typeOf . bindingTag

instance Typed Void where
    typeOf _ = tVar kTyp "a"

instance Typed () where
    typeOf _ = tVar kTyp "a"

instance FreeIn TypeEnv where
    free = free . Env.elems

instance FreeIn (TypeInfo e) where
    free = free . nodeType

instance (Substitutable Type a) => Substitutable (TypeInfo e) a where
    apply sub = \case
        TypeInfo e ty ps -> TypeInfo e (apply sub ty) (apply sub ps)

instance (Substitutable Scheme t) => Substitutable TypeEnv t where
    apply = Env.map . apply

instance (Substitutable Type t) => Substitutable (ClassInfo Type (Ast (TypeInfo e))) t where
    apply sub ClassInfo{..} =
        ClassInfo{ classPredicates = apply sub classPredicates
                 , classSignature  = apply sub classSignature
                 , .. }

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Kind

kVar :: Name -> Kind
kVar = embed1 KVar

kCon :: Name -> Kind
kCon = embed1 KCon

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr

infixr 1 `kArr`

kTyp :: Kind
kTyp = kCon "*"

kClass :: Kind
kClass = kCon "Constraint"

kRow :: Kind
kRow = kCon "Row"

kFun :: Kind
kFun = kTyp `kArr` kTyp

kFun2 :: Kind
kFun2 = kTyp `kArr` kTyp `kArr` kTyp

-- Type

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon

tRow :: Name -> TypeT a -> TypeT a -> TypeT a
tRow = embed3 TRow

tApp :: Kind -> TypeT a -> TypeT a -> TypeT a
tApp = embed3 TApp

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr

infixr 1 `tArr`

tGen :: a -> TypeT a
tGen = embed1 TGen

typ :: Name -> TypeT a
typ = tCon kTyp

-- Built-in types

tVoid :: TypeT a
tVoid = typ "Void"

tUnit :: TypeT a
tUnit = typ "Unit"

tBool :: TypeT a
tBool = typ "Bool"

tNat :: TypeT a
tNat = typ "Nat"

tInt :: TypeT a
tInt = typ "Int"

tInteger :: TypeT a
tInteger = typ "Integer"

tFloat :: TypeT a
tFloat = typ "Float"

tDouble :: TypeT a
tDouble = typ "Double"

tChar :: TypeT a
tChar = typ "Char"

tString :: TypeT a
tString = typ "String"

tSymbol :: TypeT a
tSymbol = typ "Symbol"

-- Lists

tListCon :: TypeT a
tListCon = tCon kFun "List"

tList :: TypeT a -> TypeT a
tList = tApp kTyp tListCon

-- Tuples

tTupleCon :: Int -> TypeT a
tTupleCon n = tCon (foldr kArr kTyp (replicate n kTyp)) (tupleCon n)

tTuple :: [TypeT a] -> TypeT a
tTuple types = foldl (tApp kTyp) (tTupleCon (length types)) types

tPair :: TypeT a -> TypeT a -> TypeT a
tPair t1 t2 = tTuple [t1, t2]

tTriple :: TypeT a -> TypeT a -> TypeT a -> TypeT a
tTriple t1 t2 t3 = tTuple [t1, t2, t3]

-- Rows

tRowNil :: TypeT a
tRowNil = tCon kRow "{}"

-- Records

tRecordCon :: TypeT a
tRecordCon = tCon (kArr kRow kTyp) "#"

tRecord :: TypeT a -> TypeT a
tRecord = tApp kTyp tRecordCon

-- Pattern

varPat
  :: t1
  -> Name
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
varPat = embed2 PVar

conPat
  :: t2
  -> Name
  -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10]
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
conPat = embed3 PCon

asPat
  :: t3
  -> Name
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
asPat = embed3 PAs

litPat
  :: t4
  -> Prim
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
litPat = embed2 PLit

anyPat
  :: t5
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
anyPat = embed1 PAny

orPat
  :: t6
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
orPat = embed3 POr

tuplePat
  :: t7
  -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10]
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
tuplePat = embed2 PTuple

listPat
  :: t8
  -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10]
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
listPat = embed2 PList

rowPat
  :: t9
  -> Name
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
rowPat = embed4 PRow

annPat
  :: t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
annPat = embed2 PAnn

-- Expr

varExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Name
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
varExpr = embed2 EVar

conExpr
  :: (Functor e2, Functor e4)
  => t2
  -> Name
  -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
conExpr = embed3 ECon

litExpr
  :: (Functor e2, Functor e4)
  => t3
  -> Prim
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
litExpr = embed2 ELit

appExpr
  :: (Functor e2, Functor e4)
  => t4
  -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
appExpr = embed2 EApp

fixExpr
  :: (Functor e2, Functor e4)
  => t5
  -> Name
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
fixExpr = embed4 EFix

lamExpr
  :: (Functor e2, Functor e4)
  => t6
  -> e1
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
lamExpr = embed3 ELam

ifExpr
  :: (Functor e2, Functor e4)
  => t7
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
ifExpr = embed4 EIf

patExpr
  :: (Functor e2, Functor e4)
  => t8
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> [e2 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
patExpr = embed3 EPat

letExpr
  :: (Functor e2, Functor e4)
  => t9
  -> e3
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
letExpr = embed4 ELet

funExpr
  :: (Functor e2, Functor e4)
  => t10
  -> [e4 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
funExpr = embed2 EFun

op1Expr
  :: (Functor e2, Functor e4)
  => t11
  -> Op1 t11
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
op1Expr = embed3 EOp1

op2Expr
  :: (Functor e2, Functor e4)
  => t12
  -> Op2 t12
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
op2Expr = embed4 EOp2

tupleExpr
  :: (Functor e2, Functor e4)
  => t13
  -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
tupleExpr = embed2 ETuple

listExpr
  :: (Functor e2, Functor e4)
  => t14
  -> [Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
listExpr = embed2 EList

rowExpr
  :: (Functor e2, Functor e4)
  => t15
  -> Name
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
rowExpr = embed4 ERow

holeExpr
  :: (Functor e2, Functor e4)
  => t16
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
holeExpr = embed1 EHole

annExpr
  :: (Functor e2, Functor e4)
  => t17
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
annExpr = embed2 EAnn

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

kindOf :: Type -> Kind
kindOf = project >>> \case
    TVar a _     -> a
    TCon a _     -> a
    TApp a _ _   -> a
    TArr{}       -> kTyp
    TRow{}       -> kRow

kindVars :: Kind -> [Name]
kindVars = nub . cata (\case
    KVar var     -> [var]
    KArr k1 k2   -> k1 <> k2
    _            -> [])

typeVars :: TypeT a -> [(Name, Kind)]
typeVars = nub . cata (\case
    TVar k var   -> [(var, k)]
    TApp _ t1 t2 -> t1 <> t2
    TArr   t1 t2 -> t1 <> t2
    TRow _ t1 t2 -> t1 <> t2
    _            -> [])

toPolytype :: Type -> Polytype
toPolytype = cata $ \case
    TVar k var   -> tVar k var
    TCon k con   -> tCon k con
    TApp k t1 t2 -> tApp k t1 t2
    TArr   t1 t2 -> tArr t1 t2
    TRow n t1 t2 -> tRow n t1 t2

fromPolytype :: [Type] -> Polytype -> Type
fromPolytype ts = cata $ \case
    TGen n       -> ts !! n
    TApp k t1 t2 -> tApp k t1 t2
    TVar k var   -> tVar k var
    TCon k con   -> tCon k con
    TArr   t1 t2 -> tArr t1 t2
    TRow n t1 t2 -> tRow n t1 t2

toScheme :: Type -> Scheme
toScheme = Forall [] [] . toPolytype

tupleCon :: Int -> Name
tupleCon size = "(" <> Text.replicate (pred size) "," <> ")"

predicateName :: PredicateT a -> Name
predicateName (InClass name _) = name

predicateType :: PredicateT a -> a
predicateType (InClass _ t) = t

getKindVar :: Kind -> Maybe Name
getKindVar = project >>> \case
    KVar v   -> Just v
    _        -> Nothing

getTypeVar :: Type -> Maybe Name
getTypeVar = project >>> \case
    TVar _ v -> Just v
    _        -> Nothing

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

exprTag :: (Functor e2, Functor e4) => Expr t t t t t t t t t t t t t t t t u e1 e2 e3 e4 -> t
exprTag = cata $ \case
    EVar    t _     -> t
    EHole   t       -> t
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
    ERow    t _ _ _ -> t
    EAnn    _ e     -> e

patternTag :: Pattern t t t t t t t t t u -> t
patternTag = cata $ \case
    PVar    t _     -> t
    PCon    t _ _   -> t
    PLit    t _     -> t
    PAs     t _ _   -> t
    POr     t _ _   -> t
    PAny    t       -> t
    PTuple  t _     -> t
    PList   t _     -> t
    PRow    t _ _ _ -> t
    PAnn    _ p     -> p

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
    OFpip   t       -> t
    OBpip   t       -> t
    OOpt    t       -> t
    OStr    t       -> t
    ODot    t       -> t
    OField  t       -> t

bindingTag :: Binding t p -> t
bindingTag = \case
    BPat    t _     -> t
    BFun    t _ _   -> t

astTag :: Ast t -> t
astTag = exprTag . astExpr

-- clauseTag (already defined)

-------------------------------------------------------------------------------

newtype Substitution a = Sub { getSub :: Map Name a }

class Substitutable t a where
    apply :: Substitution a -> t -> t

instance Substitutable t a => Substitutable [t] a where
    apply = fmap . apply

deriving instance (Show a) =>
    Show (Substitution a)

deriving instance (Eq a) =>
    Eq (Substitution a)

deriving instance
    Functor Substitution

instance Semigroup (Substitution Type) where
    (<>) = compose

instance Monoid (Substitution Type) where
    mempty = nullSub

instance Substitutable (TypeT a) (TypeT a) where
    apply = typeSubstitute

instance Substitutable Polytype Type where
    apply sub = cata $ \case
        TVar kind var        -> toPolytype (withDefault (tVar kind var) var sub)
        ty                   -> embed ty

instance (Substitutable t a) => Substitutable (PredicateT t) a where
    apply = fmap . apply

instance (Substitutable t a) => Substitutable (ProgPattern t u) a where
    apply sub = cata $ \case
        PVar    t var        -> varPat    (apply sub t) var
        PCon    t con ps     -> conPat    (apply sub t) con ps
        PLit    t prim       -> litPat    (apply sub t) prim
        PAs     t as p       -> asPat     (apply sub t) as p
        POr     t p q        -> orPat     (apply sub t) p q
        PAny    t            -> anyPat    (apply sub t)
        PTuple  t ps         -> tuplePat  (apply sub t) ps
        PList   t ps         -> listPat   (apply sub t) ps
        PRow    t lab p r    -> rowPat    (apply sub t) lab p r
        PAnn    t p          -> annPat    t p

instance (Substitutable t a, Substitutable p a) => Substitutable (Binding t p) a where
    apply sub = \case
        BPat t p             -> BPat (apply sub t) (apply sub p)
        BFun t name ps       -> BFun (apply sub t) name (apply sub ps)

instance (Substitutable g a) => Substitutable (Choice g) a where
    apply sub = \case
        Choice es e           -> Choice (apply sub es) (apply sub e)

instance (Substitutable t a, Substitutable p a, Substitutable (Choice g) a) => Substitutable (Clause t p g) a where
    apply sub = \case
        Clause  t p gs       -> Clause (apply sub t) (apply sub p) (apply sub gs)

instance (Substitutable t a) => Substitutable (ProgExpr t u) a where
    apply sub = cata $ \case
        EVar    t var        -> varExpr    (apply sub t) var
        EHole   t            -> holeExpr   (apply sub t)
        ECon    t con es     -> conExpr    (apply sub t) con es
        ELit    t prim       -> litExpr    (apply sub t) prim
        EApp    t es         -> appExpr    (apply sub t) es
        ELet    t bind e1 e2 -> letExpr    (apply sub t) (apply sub bind) e1 e2
        EFix    t name e1 e2 -> fixExpr    (apply sub t) name e1 e2
        ELam    t ps e       -> lamExpr    (apply sub t) (apply sub ps) e
        EIf     t e1 e2 e3   -> ifExpr     (apply sub t) e1 e2 e3
        EPat    t es cs      -> patExpr    (apply sub t) es (apply sub cs)
        EFun    t cs         -> funExpr    (apply sub t) (apply sub cs)
        EOp1    t op a       -> op1Expr    (apply sub t) (apply sub op) a
        EOp2    t op a b     -> op2Expr    (apply sub t) (apply sub op) a b
        ETuple  t es         -> tupleExpr  (apply sub t) es
        EList   t es         -> listExpr   (apply sub t) es
        ERow    t lab e r    -> rowExpr    (apply sub t) lab e r
        EAnn    t e          -> annExpr    t e

instance (Substitutable t a) => Substitutable (Op1 t) a where
    apply sub = \case
        ONeg   t             -> ONeg   (apply sub t)
        ONot   t             -> ONot   (apply sub t)

instance (Substitutable t a) => Substitutable (Op2 t) a where
    apply sub = \case
        OEq    t             -> OEq    (apply sub t)
        ONeq   t             -> ONeq   (apply sub t)
        OAnd   t             -> OAnd   (apply sub t)
        OOr    t             -> OOr    (apply sub t)
        OAdd   t             -> OAdd   (apply sub t)
        OSub   t             -> OSub   (apply sub t)
        OMul   t             -> OMul   (apply sub t)
        ODiv   t             -> ODiv   (apply sub t)
        OPow   t             -> OPow   (apply sub t)
        OMod   t             -> OMod   (apply sub t)
        OLt    t             -> OLt    (apply sub t)
        OGt    t             -> OGt    (apply sub t)
        OLte   t             -> OLte   (apply sub t)
        OGte   t             -> OGte   (apply sub t)
        OLarr  t             -> OLarr  (apply sub t)
        ORarr  t             -> ORarr  (apply sub t)
        OFpip  t             -> OFpip  (apply sub t)
        OBpip  t             -> OBpip  (apply sub t)
        OOpt   t             -> OOpt   (apply sub t)
        OStr   t             -> OStr   (apply sub t)
        ODot   t             -> ODot   (apply sub t)
        OField t             -> OField (apply sub t)

instance (Substitutable t a) => Substitutable (Ast t) a where
    apply sub = \case
        Ast expr             -> Ast (apply sub expr)

instance Substitutable Scheme Type where
    apply sub = \case
        Forall ks ps pt      -> Forall ks ps (apply sub pt)

-------------------------------------------------------------------------------

instance Semigroup (Substitution Kind) where
    (<>) = compose

instance Monoid (Substitution Kind) where
    mempty = nullSub

instance Substitutable Kind Kind where
    apply = kindSubstitute

instance Substitutable (TypeT a) Kind where
    apply sub = cata $ \case
        TVar k var           -> tVar (apply sub k) var
        TCon k con           -> tCon (apply sub k) con
        TApp k t1 t2         -> tApp (apply sub k) t1 t2
        ty                   -> embed ty

instance Substitutable Scheme Kind where
    apply sub = \case
        Forall ks ps pt      -> Forall (apply sub ks) ps (apply sub pt)

-------------------------------------------------------------------------------

nullSub :: Substitution a
nullSub = Sub mempty

compose :: (Substitutable a a) => Substitution a -> Substitution a -> Substitution a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

mapsTo :: Name -> a -> Substitution a
mapsTo name val = Sub (Map.singleton name val)

withDefault :: a -> Name -> Substitution a -> a
withDefault default_ name = Map.findWithDefault default_ name . getSub

fromList :: [(Name, a)] -> Substitution a
fromList = Sub . Map.fromList

toList :: Substitution a -> [(Name, a)]
toList = Map.toList . getSub

domain :: Substitution a -> [Name]
domain (Sub sub) = Map.keys sub

-------------------------------------------------------------------------------

typeSubstitute :: Substitution (TypeT a) -> TypeT a -> TypeT a
typeSubstitute sub = cata $ \case
    TVar kind var -> withDefault (tVar kind var) var sub
    ty            -> embed ty

merge :: (Eq a) => Substitution a -> Substitution a -> Maybe (Substitution a)
merge s1 s2
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    allEqual = all (\v -> applySub s1 v == applySub s2 v)
        (domain s1 `intersect` domain s2)

    applySub :: Substitution a -> Name -> Maybe a
    applySub sub var = Map.lookup var (getSub sub)

normalizer :: [(Name, Kind)] -> Substitution Type
normalizer vars = fromList (zipWith (\(v, k) a -> (v, tVar k a)) vars letters)

normalize :: Type -> Type
normalize ty = apply (normalizer (typeVars ty)) ty

-------------------------------------------------------------------------------

kindSubstitute :: Substitution Kind -> Kind -> Kind
kindSubstitute sub = cata $ \case
   KVar var   -> withDefault (kVar var) var sub
   ty         -> embed ty

applyBoth
  :: (Substitutable t Type, Substitutable t Kind)
  => (Substitution Type, Substitution Kind) -> t -> t
applyBoth (typeSub, kindSub) = apply kindSub . apply typeSub

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data Error
    = GenericError
    | UnificationError UnificationError
    | NotInScope Name
    | ConstructorNotInScope Name
    | NoSuchClass Name
    | MissingInstance Name Type

data UnificationError
    = InfiniteType
    | InfiniteKind
    | IncompatibleTypes
    | IncompatibleKinds
    | CannotMerge

deriving instance Show Error
deriving instance Eq   Error

deriving instance Show UnificationError
deriving instance Eq   UnificationError

-------------------------------------------------------------------------------

bindKind
  :: (MonadError UnificationError m)
  => Name
  -> Kind
  -> m (Substitution Kind)
bindKind name kind
    | getKindVar kind == Just name            = pure mempty
    | name `elem` kindVars kind               = throwError InfiniteKind
    | otherwise                               = pure (name `mapsTo` kind)

unifyKinds
  :: (MonadError UnificationError m)
  => Kind
  -> Kind
  -> m (Substitution Kind)
unifyKinds k l = fn (project k) (project l)
  where
    fn (KArr k1 k2) (KArr l1 l2)              = unifyKindPairs (k1, k2) (l1, l2)
    fn (KVar name) _                          = bindKind name l
    fn _ (KVar name)                          = bindKind name k
    fn _ _ | k == l                           = pure mempty
    fn _ _                                    = throwError IncompatibleKinds

unifyKindPairs
  :: (MonadError UnificationError m)
  => (Kind, Kind)
  -> (Kind, Kind)
  -> m (Substitution Kind)
unifyKindPairs (k1, k2) (l1, l2) = do
    sub1 <- unifyKinds k1 l1
    sub2 <- unifyKinds (apply sub1 k2) (apply sub1 l2)
    pure (sub2 <> sub1)

-------------------------------------------------------------------------------

bindType
  :: (MonadError UnificationError m)
  => Name
  -> Kind
  -> Type
  -> m (Substitution Type, Substitution Kind)
bindType name kind ty
    | getTypeVar ty == Just name              = (,) mempty <$> kindSub
    | name `elem` (fst <$> free ty)           = throwError InfiniteType
    | otherwise                               = (,) (name `mapsTo` ty) <$> kindSub
  where
    kindSub = unifyKinds kind (kindOf ty)

unifyTypes
  :: ( MonadSupply Int f m
     , MonadError UnificationError m )
  => Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
unifyTypes t u = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyTypePairs (t1, t2) (u1, u2)
    fn (TApp _ t1 t2) (TApp _ u1 u2)          = unifyTypePairs (t1, t2) (u1, u2)
    fn TRow{} TRow{}                          = unifyRows unifyTypes unifyTypePairs t u
    fn (TVar kind name) _                     = bindType name kind u
    fn _ (TVar kind name)                     = bindType name kind t
    fn (TCon k1 a) (TCon k2 b) | a == b       = (mempty ,) <$> unifyKinds k1 k2
    fn _ _                                    = throwError IncompatibleTypes

matchTypes
  :: ( MonadSupply Int f m
     , MonadError UnificationError m )
  => Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
matchTypes t u = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = matchTypePairs (t1, t2) (u1, u2)
    fn (TApp _ t1 t2) (TApp _ u1 u2)          = matchTypePairs (t1, t2) (u1, u2)
    fn TRow{} TRow{}                          = unifyRows matchTypes matchTypePairs t u
    fn (TVar kind name) _                     = bindType name kind u
    fn (TCon k1 a) (TCon k2 b) | a == b       = (mempty ,) <$> unifyKinds k1 k2
    fn _ _                                    = throwError IncompatibleTypes

unifyTypePairs
  :: ( MonadSupply Int f m
     , MonadError UnificationError m )
  => (Type, Type)
  -> (Type, Type)
  -> m (Substitution Type, Substitution Kind)
unifyTypePairs (t1, t2) (u1, u2) = do
    subs1 <- unifyTypes t1 u1
    subs2 <- unifyTypes (applyBoth subs1 t2) (applyBoth subs1 u2)
    pure (subs2 <> subs1)

matchTypePairs
  :: ( MonadSupply Int f m
     , MonadError UnificationError m )
  => (Type, Type)
  -> (Type, Type)
  -> m (Substitution Type, Substitution Kind)
matchTypePairs (t1, t2) (u1, u2) = do
    (typeSub1, kindSub1) <- matchTypes t1 u1
    (typeSub2, kindSub2) <- matchTypes t2 u2
    (,) <$> mergeSubs typeSub1 typeSub2 <*> mergeSubs kindSub1 kindSub2
  where
    mergeSubs sub1 sub2 = maybe (throwError CannotMerge) pure (merge sub1 sub2)

-------------------------------------------------------------------------------

unifyRows
  :: ( MonadSupply Int f m
     , MonadError UnificationError m )
  => (Type -> Type -> m (Substitution Type, Substitution Kind))
  -> ((Type, Type) -> (Type, Type) -> m (Substitution Type, Substitution Kind))
  -> Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
unifyRows combineTypes combinePairs t u =
    fn (mapRep t, final t) (mapRep u, final u)
  where
    mapRep = foldr (uncurry (Map.insertWith (<>))) mempty . fields

    fromMap =
        Map.foldrWithKey (flip . foldr . tRow)

    fields = para $ \case
        TRow label ty rest -> (label, [fst ty]):snd rest
        _                  -> []

    final = cata $ \case
        TRow _ _ r         -> r
        t                  -> embed t

    fn (m1, j) (m2, k)
        | Map.null m1 && Map.null m2 = combineTypes j k
        | Map.null m1 = combineTypes j (fromMap k m2)
        | otherwise =
            case Map.lookup a m2 of
                Just (u:us) ->
                    combinePairs
                        (fromMap j (updateMap m1 ts), t)
                        (fromMap k (updateMap m2 us), u)
                _ -> do
                    when (k == j) $ throwError IncompatibleTypes
                    s <- demand
                    let tv = tVar kRow ("$r" <> showt s)
                    combinePairs
                        (fromMap j (updateMap m1 ts), k)
                        (fromMap tv m2, tRow a t tv)
      where
        (a, t:ts) = Map.elemAt 0 m1
        updateMap m = \case
            [] -> Map.delete a m
            ts -> Map.insert a ts m
