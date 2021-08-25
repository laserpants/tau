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
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError, runExceptT)
import Control.Monad.Extra (allM, (||^))
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Either.Combinators (fromRight, rightToMaybe)
import Data.Either.Extra (eitherToMaybe)
import Data.Eq.Deriving (deriveEq1)
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.List (nub, intersect)
import Data.List.Extra (notNull)
import Data.Map.Strict (Map)
import Data.Ord.Deriving (deriveOrd1)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Tuple.Extra (first)
import Data.Void (Void)
import Debug.Trace
import Tau.Env (Env)
import Tau.Util (Name, embed1, embed2, embed3, embed4, letters, (<$$>), liftMaybe, nats)
import Text.Show.Deriving (deriveShow1)
import TextShow
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
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
data PredicateF a = InClass Name a

-- | A standalone type class constraint
type Predicate = PredicateF Type

-- | Polymorphic type scheme
data Scheme = Forall [Kind] [PredicateF Int] Polytype

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

data PatternF t1 t2 t3 t4 a
    = PVar    t1 Name                    -- ^ Variable pattern
    | PCon    t1 Name [a]                -- ^ Constuctor pattern
    | PAs     t1 Name a                  -- ^ As-pattern
    | POr     t2 a a                     -- ^ Or-pattern
    | PLit    t3 Prim                    -- ^ Literal pattern
    | PAny    t3                         -- ^ Wildcard pattern
    | PTuple  t3 [a]                     -- ^ Tuple pattern
    | PList   t3 [a]                     -- ^ List pattern
    | PRow    t3 Name a a                -- ^ Row pattern
    | PRecord t3 a                       -- ^ Record pattern
    | PAnn    t4 a                       -- ^ Explicit type annotation

-- | Pattern
type Pattern t1 t2 t3 t4 = Fix (PatternF t1 t2 t3 t4)

data ExprF t1 t2 t3 t4 e1 e2 e3 e4 a
    = EVar    t1 Name                    -- ^ Variable
    | ECon    t1 Name [a]                -- ^ Data constructor
    | ELit    t1 Prim                    -- ^ Literal value
    | EApp    t1 [a]                     -- ^ Function application
    | EFix    t1 Name a a                -- ^ Recursive let
    | ELam    t1 e1 a                    -- ^ Lambda abstraction
    | EIf     t1 a a a                   -- ^ If-clause
    | EPat    t1 a [e2 a]                -- ^ Match expressions
    | ELet    t2 e3 a a                  -- ^ Let expression
    | EFun    t3 [e4 a]                  -- ^ Fun expression
    | EOp1    t3 (Op1 t3) a              -- ^ Unary operator
    | EOp2    t3 (Op2 t3) a a            -- ^ Binary operator
    | ETuple  t3 [a]                     -- ^ Tuple
    | EList   t3 [a]                     -- ^ List literal
    | ERow    t3 Name a a                -- ^ Row expression
    | ERecord t3 a                       -- ^ Record expression
    | EHole   t3                         -- ^ Blank argument in partial function application
    | EAnn    t4 a                       -- ^ Explicit type annotation

-- | Language expression
type Expr t1 t2 t3 t4 e1 e2 e3 e4 = Fix (ExprF t1 t2 t3 t4 e1 e2 e3 e4)

-- | Name binding-part of let expressions
data Binding t p
    = BPat t p                           -- ^ Pattern binding
    | BFun t Name [p]                    -- ^ Function binding

-- | Pattern clause choice. A pattern matching clause consists of one or more choices,
-- each of which is a (possibly empty) list of predicates, known as guards, and a target
-- expression.
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

-- | Operator associativity
data Assoc
    = AssocL                             -- ^ Operator is left-associative
    | AssocR                             -- ^ Operator is right-associative
    | AssocN                             -- ^ Operator is non-associative

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

deriving instance (Show t1, Show t2, Show t3, Show t4, Show a) =>
    Show (PatternF t1 t2 t3 t4 a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq a) =>
    Eq (PatternF t1 t2 t3 t4 a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord a) =>
    Ord (PatternF t1 t2 t3 t4 a)

deriveShow1 ''PatternF
deriveEq1   ''PatternF
deriveOrd1  ''PatternF

deriving instance Functor     (PatternF t1 t2 t3 t4)
deriving instance Foldable    (PatternF t1 t2 t3 t4)
deriving instance Traversable (PatternF t1 t2 t3 t4)

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

deriving instance Functor     (Binding t)
deriving instance Foldable    (Binding t)
deriving instance Traversable (Binding t)

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

deriving instance (Show t1, Show t2, Show t3, Show t4, Show e1, Show (e2 a), Show e3, Show (e4 a), Show a) =>
    Show (ExprF t1 t2 t3 t4 e1 e2 e3 e4 a)

deriving instance (Eq t1, Eq t2, Eq t3, Eq t4, Eq e1, Eq (e2 a), Eq e3, Eq (e4 a), Eq a) =>
    Eq (ExprF t1 t2 t3 t4 e1 e2 e3 e4 a)

deriving instance (Ord t1, Ord t2, Ord t3, Ord t4, Ord e1, Ord (e2 a), Ord e3, Ord (e4 a), Ord a) =>
    Ord (ExprF t1 t2 t3 t4 e1 e2 e3 e4 a)

deriveShow1 ''ExprF
deriveEq1   ''ExprF
deriveOrd1  ''ExprF

deriving instance (Functor e2, Functor e4) =>
    Functor (ExprF t1 t2 t3 t4 e1 e2 e3 e4)

deriving instance (Foldable e2, Foldable e4) =>
    Foldable (ExprF t1 t2 t3 t4 e1 e2 e3 e4)

deriving instance (Traversable e2, Traversable e4) =>
    Traversable (ExprF t1 t2 t3 t4 e1 e2 e3 e4)

-------------------------------------------------------------------------------
-- Core
-------------------------------------------------------------------------------

type CMatrix a = [([Name], a)]

data CoreF a
    = CVar Name                 -- ^ Variable
    | CLit Prim                 -- ^ Primitive value
    | CApp [a]                  -- ^ Function application
    | CLet Name a a             -- ^ Let expression
    | CLam Name a               -- ^ Lambda abstraction
    | CIf  a ~a ~a              -- ^ If-clause
    | CPat a (CMatrix a)        -- ^ Pattern match clause matrix

-- | Core language expression used for interpreted program evaluation and code
-- generation
type Core = Fix CoreF

-------------------------------------------------------------------------------

-- Type class instances for Core

deriving instance (Show a) => Show (CoreF a)
deriving instance (Eq   a) => Eq   (CoreF a)
deriving instance (Ord  a) => Ord  (CoreF a)

deriveShow1 ''CoreF
deriveEq1   ''CoreF
deriveOrd1  ''CoreF

deriving instance Functor     CoreF
deriving instance Foldable    CoreF
deriving instance Traversable CoreF

-------------------------------------------------------------------------------

cVar :: Name -> Core
cVar = embed1 CVar
{-# INLINE cVar #-}

cLit :: Prim -> Core
cLit = embed1 CLit
{-# INLINE cLit #-}

cApp :: [Core] -> Core
cApp = embed1 CApp
{-# INLINE cApp #-}

cLet :: Name -> Core -> Core -> Core
cLet = embed3 CLet
{-# INLINE cLet #-}

cLam :: Name -> Core -> Core
cLam = embed2 CLam
{-# INLINE cLam #-}

cIf :: Core -> Core -> Core -> Core
cIf = embed3 CIf
{-# INLINE cIf #-}

cPat :: Core -> CMatrix Core -> Core
cPat = embed2 CPat
{-# INLINE cPat #-}

-------------------------------------------------------------------------------
-- Prog
-------------------------------------------------------------------------------

type ProgExpr t u = Expr t t t u [ProgPattern t u]
    (Clause t (ProgPattern t u)) (ProgBinding t u)
    (Clause t [ProgPattern t u])

type ProgPattern t u = Pattern t t t u
type ProgBinding t u = Binding t (ProgPattern t u)
type ProgClause  t u = Clause t [ProgPattern t u] (ProgExpr t u)

newtype Ast t = Ast { astExpr :: ProgExpr t Void }

data TypeInfoT e t = TypeInfo
    { nodeErrors      :: e
    , nodeType        :: t
    , nodePredicates  :: [Predicate] }

type TypeInfo e = TypeInfoT e Type

data ClassInfo p e = ClassInfo
    { classSignature  :: PredicateF p
    , classPredicates :: [PredicateF p]
    , classMethods    :: [(Name, e)] }

type Instance = ClassInfo Type (Ast (TypeInfo ()))

-- Environments

type Context = Env (Set Name)

type TypeEnv = Env Scheme

type KindEnv = Env Kind

type ClassEnv = Env
    ( ClassInfo Name Type                          -- Abstract interface
    , [ClassInfo Type (Ast (TypeInfo ()))] )       -- Instances

type ConstructorEnv = Env (Set Name, Int)

-- | Product type
data Product = Mul Name [Type]

-- | A type declaration is a sum of products
data Typedecl = Sum Name [Name] [Product]

-- | Top-level declaration, e.g., f(x, y) = foo, or name = "Foo"
data Topdecl t u = Top t (Binding t (ProgPattern t u)) (ProgExpr t u)

-------------------------------------------------------------------------------

getClassEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ClassEnv
getClassEnv (e, _, _, _) = e
{-# INLINE getClassEnv #-}

askClassEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ClassEnv
askClassEnv = asks getClassEnv
{-# INLINE askClassEnv #-}

getTypeEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> TypeEnv
getTypeEnv (_, e, _, _) = e
{-# INLINE getTypeEnv #-}

askTypeEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m TypeEnv
askTypeEnv = asks getTypeEnv
{-# INLINE askTypeEnv #-}

getKindEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> KindEnv
getKindEnv (_, _, e, _) = e
{-# INLINE getKindEnv #-}

askKindEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m KindEnv
askKindEnv = asks getKindEnv
{-# INLINE askKindEnv #-}

getConstructorEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ConstructorEnv
getConstructorEnv (_, _, _, e) = e
{-# INLINE getConstructorEnv #-}

askConstructorEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ConstructorEnv
askConstructorEnv = asks getConstructorEnv
{-# INLINE askConstructorEnv #-}

inClassEnv
  :: (ClassEnv -> ClassEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inClassEnv f (e1, e2, e3, e4) = (f e1, e2, e3, e4)
{-# INLINE inClassEnv #-}

inTypeEnv
  :: (TypeEnv -> TypeEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inTypeEnv f (e1, e2, e3, e4) = (e1, f e2, e3, e4)
{-# INLINE inTypeEnv #-}

inKindEnv
  :: (KindEnv -> KindEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inKindEnv f (e1, e2, e3, e4) = (e1, e2, f e3, e4)
{-# INLINE inKindEnv #-}

inConstructorEnv
  :: (ConstructorEnv -> ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inConstructorEnv f (e1, e2, e3, e4) = (e1, e2, e3, f e4)
{-# INLINE inConstructorEnv #-}

-------------------------------------------------------------------------------

-- Type class instances for Predicate

deriving instance (Show a) =>
    Show (PredicateF a)

deriving instance (Eq a) =>
    Eq (PredicateF a)

deriving instance (Ord a) =>
    Ord (PredicateF a)

deriveShow1 ''PredicateF
deriveEq1   ''PredicateF
deriveOrd1  ''PredicateF

deriving instance Functor     PredicateF
deriving instance Foldable    PredicateF
deriving instance Traversable PredicateF

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

-- Type class instances for Product and Typedecl

deriving instance Show Product
deriving instance Eq   Product
deriving instance Ord  Product

deriving instance Show Typedecl
deriving instance Eq   Typedecl
deriving instance Ord  Typedecl

deriving instance (Show t) => Show (Ast t)
deriving instance (Eq   t) => Eq   (Ast t)
deriving instance (Ord  t) => Ord  (Ast t)

instance Functor Ast where
  fmap f (Ast expr) = Ast (mapExprTag f expr)

deriving instance (Show t, Show u) => Show (Topdecl t u)
deriving instance (Eq   t, Eq   u) => Eq   (Topdecl t u)
deriving instance (Ord  t, Ord  u) => Ord  (Topdecl t u)

-------------------------------------------------------------------------------

addErrors :: (Eq e) => [e] -> TypeInfoT [e] t -> TypeInfoT [e] t
addErrors errs TypeInfo{..} = TypeInfo{ nodeErrors = nub (errs <> nodeErrors), .. }

hasErrors :: ProgExpr (TypeInfoT [e] t) u -> Bool
hasErrors = foldrExprTag (\ti rest -> rest || notNull (nodeErrors ti)) False

allErrors :: ProgExpr (TypeInfoT [e] t) u -> [e]
allErrors = foldrExprTag (\ti es -> nodeErrors ti <> es) []

constructorEnv :: [(Name, ([Name], Int))] -> ConstructorEnv
constructorEnv = Env.fromList . (first Set.fromList <$$>)

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

instance (Substitutable Error a, Substitutable Type a) => Substitutable (TypeInfo [Error]) a where
    apply sub = \case
        TypeInfo e ty ps -> TypeInfo (apply sub e) (apply sub ty) (apply sub ps)

instance (Substitutable Scheme t) => Substitutable TypeEnv t where
    apply = Env.map . apply

instance (Substitutable Type t) => Substitutable (ClassInfo Type (Ast (TypeInfo e))) t where
    apply sub ClassInfo{..} =
        ClassInfo{ classPredicates = apply sub classPredicates
                 , classSignature  = apply sub classSignature
                 , .. }

instance Substitutable Error Type where
    apply = fmap . apply

instance Substitutable Error Kind where
    apply = fmap . apply

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Kind

kVar :: Name -> Kind
kVar = embed1 KVar
{-# INLINE kVar #-}

kCon :: Name -> Kind
kCon = embed1 KCon
{-# INLINE kCon #-}

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr
{-# INLINE kArr #-}

infixr 1 `kArr`

kTyp :: Kind
kTyp = kCon "*"
{-# INLINE kTyp #-}

kClass :: Kind
kClass = kCon "Constraint"
{-# INLINE kClass #-}

kRow :: Kind
kRow = kCon "Row"
{-# INLINE kRow #-}

kFun :: Kind
kFun = kTyp `kArr` kTyp
{-# INLINE kFun #-}

kFun2 :: Kind
kFun2 = kTyp `kArr` kTyp `kArr` kTyp
{-# INLINE kFun2 #-}

-- Type

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar
{-# INLINE tVar #-}

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon
{-# INLINE tCon #-}

tRow :: Name -> TypeT a -> TypeT a -> TypeT a
tRow = embed3 TRow
{-# INLINE tRow #-}

tApp :: Kind -> TypeT a -> TypeT a -> TypeT a
tApp = embed3 TApp
{-# INLINE tApp #-}

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr
{-# INLINE tArr #-}

infixr 1 `tArr`

tGen :: a -> TypeT a
tGen = embed1 TGen
{-# INLINE tGen #-}

typ :: Name -> TypeT a
typ = tCon kTyp
{-# INLINE typ #-}

-- Built-in types

tVoid :: TypeT a
tVoid = typ "Void"
{-# INLINE tVoid #-}

tUnit :: TypeT a
tUnit = typ "Unit"
{-# INLINE tUnit #-}

tBool :: TypeT a
tBool = typ "Bool"
{-# INLINE tBool #-}

tNat :: TypeT a
tNat = typ "Nat"
{-# INLINE tNat #-}

tInt :: TypeT a
tInt = typ "Int"
{-# INLINE tInt #-}

tInteger :: TypeT a
tInteger = typ "Integer"
{-# INLINE tInteger #-}

tFloat :: TypeT a
tFloat = typ "Float"
{-# INLINE tFloat #-}

tDouble :: TypeT a
tDouble = typ "Double"
{-# INLINE tDouble #-}

tChar :: TypeT a
tChar = typ "Char"
{-# INLINE tChar #-}

tString :: TypeT a
tString = typ "String"
{-# INLINE tString #-}

tSymbol :: TypeT a
tSymbol = typ "Symbol"
{-# INLINE tSymbol #-}

-- Lists

tListCon :: TypeT a
tListCon = tCon kFun "List"
{-# INLINE tListCon #-}

tList :: TypeT a -> TypeT a
tList = tApp kTyp tListCon
{-# INLINE tList #-}

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
{-# INLINE tRowNil #-}

-- Records

tRecordCon :: TypeT a
tRecordCon = tCon (kArr kRow kTyp) "#"

tRecord :: TypeT a -> TypeT a
tRecord = tApp kTyp tRecordCon

--

tIsVar :: TypeT a -> Bool
tIsVar = project >>> \case
    TVar{}  -> True
    _       -> False

tIsCon :: TypeT a -> Bool
tIsCon = project >>> \case
    TCon{}  -> True
    _       -> False

tIsRow :: TypeT a -> Bool
tIsRow = project >>> \case
    TRow{}  -> True
    _       -> False

tIsApp :: TypeT a -> Bool
tIsApp = project >>> \case
    TApp{}  -> True
    _       -> False

tIsArr :: TypeT a -> Bool
tIsArr = project >>> \case
    TArr{}  -> True
    _       -> False

-------------------------------------------------------------------------------

-- Pattern

varPat :: t1 -> Name -> Pattern t1 t2 t3 t4
varPat = embed2 PVar
{-# INLINE varPat #-}

conPat :: t1 -> Name -> [Pattern t1 t2 t3 t4] -> Pattern t1 t2 t3 t4
conPat = embed3 PCon
{-# INLINE conPat #-}

asPat :: t1 -> Name -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4
asPat = embed3 PAs
{-# INLINE asPat #-}

litPat :: t3 -> Prim -> Pattern t1 t2 t3 t4
litPat = embed2 PLit
{-# INLINE litPat #-}

anyPat :: t3 -> Pattern t1 t2 t3 t4
anyPat = embed1 PAny
{-# INLINE anyPat #-}

orPat :: t2 -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4
orPat = embed3 POr
{-# INLINE orPat #-}

tuplePat :: t3 -> [Pattern t1 t2 t3 t4] -> Pattern t1 t2 t3 t4
tuplePat = embed2 PTuple
{-# INLINE tuplePat #-}

listPat :: t3 -> [Pattern t1 t2 t3 t4] -> Pattern t1 t2 t3 t4
listPat = embed2 PList
{-# INLINE listPat #-}

rowPat :: t3 -> Name -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4
rowPat = embed4 PRow
{-# INLINE rowPat #-}

recordPat :: t3 -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4
recordPat = embed2 PRecord
{-# INLINE recordPat #-}

annPat :: t4 -> Pattern t1 t2 t3 t4 -> Pattern t1 t2 t3 t4
annPat = embed2 PAnn
{-# INLINE annPat #-}

-- Expr

varExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Name
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
varExpr = embed2 EVar
{-# INLINE varExpr #-}

conExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Name
  -> [Expr t1 t2 t3 t4 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
conExpr = embed3 ECon
{-# INLINE conExpr #-}

litExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Prim
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
litExpr = embed2 ELit
{-# INLINE litExpr #-}

appExpr
  :: (Functor e2, Functor e4)
  => t1
  -> [Expr t1 t2 t3 t4 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
appExpr = embed2 EApp
{-# INLINE appExpr #-}

fixExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Name
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
fixExpr = embed4 EFix
{-# INLINE fixExpr #-}

lamExpr
  :: (Functor e2, Functor e4)
  => t1
  -> e1
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
lamExpr = embed3 ELam
{-# INLINE lamExpr #-}

ifExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
ifExpr = embed4 EIf
{-# INLINE ifExpr #-}

patExpr
  :: (Functor e2, Functor e4)
  => t1
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> [e2 (Expr t1 t2 t3 t4 e1 e2 e3 e4)]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
patExpr = embed3 EPat
{-# INLINE patExpr #-}

letExpr
  :: (Functor e2, Functor e4)
  => t2
  -> e3
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
letExpr = embed4 ELet
{-# INLINE letExpr #-}

funExpr
  :: (Functor e2, Functor e4)
  => t3
  -> [e4 (Expr t1 t2 t3 t4 e1 e2 e3 e4)]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
funExpr = embed2 EFun
{-# INLINE funExpr #-}

op1Expr
  :: (Functor e2, Functor e4)
  => t3
  -> Op1 t3
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
op1Expr = embed3 EOp1
{-# INLINE op1Expr #-}

op2Expr
  :: (Functor e2, Functor e4)
  => t3
  -> Op2 t3
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
op2Expr = embed4 EOp2
{-# INLINE op2Expr #-}

tupleExpr
  :: (Functor e2, Functor e4)
  => t3
  -> [Expr t1 t2 t3 t4 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
tupleExpr = embed2 ETuple
{-# INLINE tupleExpr #-}

listExpr
  :: (Functor e2, Functor e4)
  => t3
  -> [Expr t1 t2 t3 t4 e1 e2 e3 e4]
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
listExpr = embed2 EList
{-# INLINE listExpr #-}

rowExpr
  :: (Functor e2, Functor e4)
  => t3
  -> Name
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
rowExpr = embed4 ERow
{-# INLINE rowExpr #-}

recordExpr
  :: (Functor e2, Functor e4)
  => t3
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
recordExpr = embed2 ERecord
{-# INLINE recordExpr #-}

holeExpr
  :: (Functor e2, Functor e4)
  => t3
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
holeExpr = embed1 EHole
{-# INLINE holeExpr #-}

annExpr
  :: (Functor e2, Functor e4)
  => t4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
annExpr = embed2 EAnn
{-# INLINE annExpr #-}

-- List cons constructors

listExprCons
  :: (Functor e2, Functor e4)
  => t1
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
listExprCons t hd tl = conExpr t "(::)" [hd, tl]
{-# INLINE listExprCons #-}

listPatCons
  :: t1
  -> Pattern t1 t2 t3 t4
  -> Pattern t1 t2 t3 t4
  -> Pattern t1 t2 t3 t4
listPatCons t hd tl = conPat t "(::)" [hd, tl]
{-# INLINE listPatCons #-}

-- Row constructor

rowExprCons
  :: (Functor e2, Functor e4)
  => t1
  -> Name
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Expr t1 t2 t3 t4 e1 e2 e3 e4
rowExprCons t label expr row = conExpr t ("{" <> label <> "}") [expr, row]
{-# INLINE rowExprCons #-}

rowPatCons
  :: t1
  -> Name
  -> Pattern t1 t2 t3 t4
  -> Pattern t1 t2 t3 t4
  -> Pattern t1 t2 t3 t4
rowPatCons t label pat row = conPat t ("{" <> label <> "}") [pat, row]
{-# INLINE rowPatCons #-}

isVar
  :: (Functor e2, Functor e4)
  => Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Bool
isVar = project >>> \case
    EVar{}  -> True
    _       -> False

isCon
  :: (Functor e2, Functor e4)
  => Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Bool
isCon = project >>> \case
    ECon{}  -> True
    _       -> False

isHole
  :: (Functor e2, Functor e4)
  => Expr t1 t2 t3 t4 e1 e2 e3 e4
  -> Bool
isHole = project >>> \case
    EHole{} -> True
    _       -> False

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

predicateName :: PredicateF a -> Name
predicateName (InClass name _) = name

predicateType :: PredicateF a -> a
predicateType (InClass _ t) = t

getKindVar :: Kind -> Maybe Name
getKindVar = project >>> \case
    KVar v   -> Just v
    _        -> Nothing

getTypeVar :: Type -> Maybe Name
getTypeVar = project >>> \case
    TVar _ v -> Just v
    _        -> Nothing

unfoldArr :: Type -> [Type]
unfoldArr = para $ \case
    TArr a b   -> snd a <> snd b
    t          -> [embed (fst <$> t)]

unfoldApp :: Type -> [Type]
unfoldApp = para $ \case
    TApp _ a b -> snd a <> snd b
    t          -> [embed (fst <$> t)]

lookupRowType :: Name -> Type -> Maybe Type
lookupRowType name = para $ \case
    TRow label (r, _) (_, next) -> if name == label then Just r else next
    _                           -> Nothing

unpackRecordType :: Type -> Maybe Type
unpackRecordType = para $ \case
    TApp _ (Fix (TCon _ c), _) (t, _) | "#" == c -> Just t
    TApp _ (_, a) _ -> a
    _               -> Nothing

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

exprTag :: (Functor e2, Functor e4) => Expr t t t u e1 e2 e3 e4 -> t
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
    ERecord t _     -> t
    EAnn    _ e     -> e

patternTag :: Pattern t t t u -> t
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
    PRecord t _     -> t
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

setExprTag :: t -> ProgExpr t Void -> ProgExpr t Void
setExprTag t = project >>> \case
    EVar    _ var         -> varExpr    t var
    EHole   _             -> holeExpr   t
    ECon    _ con es      -> conExpr    t con es
    ELit    _ prim        -> litExpr    t prim
    EApp    _ es          -> appExpr    t es
    ELet    _ bind e1 e2  -> letExpr    t bind e1 e2
    EFix    _ name e1 e2  -> fixExpr    t name e1 e2
    ELam    _ ps e        -> lamExpr    t ps e
    EIf     _ e1 e2 e3    -> ifExpr     t e1 e2 e3
    EPat    _ es cs       -> patExpr    t es cs
    EFun    _ cs          -> funExpr    t cs
    EOp1    _ op a        -> op1Expr    t op a
    EOp2    _ op a b      -> op2Expr    t op a b
    ETuple  _ es          -> tupleExpr  t es
    EList   _ es          -> listExpr   t es
    ERow    _ lab e r     -> rowExpr    t lab e r
    ERecord _ r           -> recordExpr t r

setPatternTag :: t -> ProgPattern t Void -> ProgPattern t Void
setPatternTag t = project >>> \case
    PVar    _ var         -> varPat     t var
    PCon    _ con ps      -> conPat     t con ps
    PLit    _ prim        -> litPat     t prim
    PAs     _ as p        -> asPat      t as p
    POr     _ p q         -> orPat      t p q
    PAny    _             -> anyPat     t
    PTuple  _ ps          -> tuplePat   t ps
    PList   _ ps          -> listPat    t ps
    PRow    _ lab p r     -> rowPat     t lab p r

primName :: Prim -> Name
primName = \case
    TUnit      -> "Unit"
    TBool    _ -> "Bool"
    TInt     _ -> "Int"
    TInteger _ -> "Integer"
    TFloat   _ -> "Float"
    TDouble  _ -> "Double"
    TChar    _ -> "Char"
    TString  _ -> "String"
    TSymbol  _ -> "Symbol"

-- | Return the precedence of a binary operator
opPrecedence :: Op2 t -> Int
opPrecedence = \case
    OEq    _ -> 4
    ONeq   _ -> 4
    OAnd   _ -> 3
    OOr    _ -> 2
    OAdd   _ -> 6
    OSub   _ -> 6
    OMul   _ -> 7
    ODiv   _ -> 7
    OPow   _ -> 8
    OLt    _ -> 4
    OGt    _ -> 4
    OLte   _ -> 4
    OGte   _ -> 4
    OLarr  _ -> 9
    ORarr  _ -> 9
    OFpip  _ -> 1
    OBpip  _ -> 1
    OOpt   _ -> 3
    OStr   _ -> 5
    ODot   _ -> 11
    OField _ -> 11

-- | Return the associativity of a binary operator
opAssoc :: Op2 t -> Assoc
opAssoc = \case
    OEq    _ -> AssocN
    ONeq   _ -> AssocN
    OAnd   _ -> AssocR
    OOr    _ -> AssocR
    OAdd   _ -> AssocL
    OSub   _ -> AssocL
    OMul   _ -> AssocL
    ODiv   _ -> AssocL
    OPow   _ -> AssocR
    OLt    _ -> AssocN
    OGt    _ -> AssocN
    OLte   _ -> AssocN
    OGte   _ -> AssocN
    ORarr  _ -> AssocL
    OLarr  _ -> AssocR
    OFpip  _ -> AssocL
    OBpip  _ -> AssocR
    OOpt   _ -> AssocN
    OStr   _ -> AssocR
    ODot   _ -> AssocL
    OField _ -> AssocL

-- | Return the symbolic representation of a binary operator
op2Symbol :: Op2 t -> Name
op2Symbol = \case
    OEq     _ -> "=="
    ONeq    _ -> "/="
    OAnd    _ -> "&&"
    OOr     _ -> "||"
    OAdd    _ -> "+"
    OSub    _ -> "-"
    OMul    _ -> "*"
    ODiv    _ -> "/"
    OPow    _ -> "^"
    OMod    _ -> "%"
    OLt     _ -> "<"
    OGt     _ -> ">"
    OLte    _ -> "<="
    OGte    _ -> ">="
    OLarr   _ -> "<<"
    ORarr   _ -> ">>"
    OFpip   _ -> "|>"
    OBpip   _ -> "<|"
    OOpt    _ -> "?"
    OStr    _ -> "++"
    ODot    _ -> "."
    OField  _ -> "."

-------------------------------------------------------------------------------

mapExprTag :: (a -> b) -> ProgExpr a u -> ProgExpr b u
mapExprTag f = cata $ \case

    EVar    t var            -> varExpr    (f t) var
    EHole   t                -> holeExpr   (f t)
    ECon    t con es         -> conExpr    (f t) con es
    ELit    t prim           -> litExpr    (f t) prim
    EApp    t es             -> appExpr    (f t) es
    ELet    t bind e1 e2     -> letExpr    (f t) (mapBind bind) e1 e2
    EFix    t name e1 e2     -> fixExpr    (f t) name e1 e2
    ELam    t ps e           -> lamExpr    (f t) (mapPattern <$> ps) e
    EIf     t e1 e2 e3       -> ifExpr     (f t) e1 e2 e3
    EPat    t es cs          -> patExpr    (f t) es (mapClause1 <$> cs)
    EFun    t cs             -> funExpr    (f t) (mapClause <$> cs)
    EOp1    t op a           -> op1Expr    (f t) (mapOp1 op) a
    EOp2    t op a b         -> op2Expr    (f t) (mapOp2 op) a b
    ETuple  t es             -> tupleExpr  (f t) es
    EList   t es             -> listExpr   (f t) es
    ERow    t lab e r        -> rowExpr    (f t) lab e r
    ERecord t r              -> recordExpr (f t) r
    EAnn    t e              -> annExpr    t e
  where
    mapBind = \case
        BPat    t p          -> BPat       (f t) (mapPattern p)
        BFun    t name ps    -> BFun       (f t) name (mapPattern <$> ps)

    mapClause = \case
        Clause  t ps cs      -> Clause     (f t) (mapPattern <$> ps) cs

    mapClause1 = \case
        Clause  t p cs       -> Clause     (f t) (mapPattern p) cs

    mapPattern = cata $ \case
        PVar    t var        -> varPat     (f t) var
        PCon    t con ps     -> conPat     (f t) con ps
        PLit    t prim       -> litPat     (f t) prim
        PAs     t as p       -> asPat      (f t) as p
        POr     t p q        -> orPat      (f t) p q
        PAny    t            -> anyPat     (f t)
        PTuple  t ps         -> tuplePat   (f t) ps
        PList   t ps         -> listPat    (f t) ps
        PRow    t lab p r    -> rowPat     (f t) lab p r
        PRecord t r          -> recordPat  (f t) r
        PAnn    t p          -> annPat     t p

    mapOp1 = \case
        ONeg    t            -> ONeg       (f t)
        ONot    t            -> ONot       (f t)

    mapOp2 = \case
        OEq     t            -> OEq        (f t)
        ONeq    t            -> ONeq       (f t)
        OAnd    t            -> OAnd       (f t)
        OOr     t            -> OOr        (f t)
        OAdd    t            -> OAdd       (f t)
        OSub    t            -> OSub       (f t)
        OMul    t            -> OMul       (f t)
        ODiv    t            -> ODiv       (f t)
        OPow    t            -> OPow       (f t)
        OMod    t            -> OMod       (f t)
        OLt     t            -> OLt        (f t)
        OGt     t            -> OGt        (f t)
        OLte    t            -> OLte       (f t)
        OGte    t            -> OGte       (f t)
        OLarr   t            -> OLarr      (f t)
        ORarr   t            -> ORarr      (f t)
        OFpip   t            -> OFpip      (f t)
        OBpip   t            -> OBpip      (f t)
        OOpt    t            -> OOpt       (f t)
        OStr    t            -> OStr       (f t)
        ODot    t            -> ODot       (f t)
        OField  t            -> OField     (f t)

foldrExprTag :: (a -> b -> b) -> b -> ProgExpr a u -> b
foldrExprTag f s e = foldr1 (.) (foldExpr f e) s
  where
    foldExpr :: (a -> b -> b) -> ProgExpr a u -> [b -> b]
    foldExpr f = cata $ \case

        EVar    t _          -> [f t]
        EHole   t            -> [f t]
        ECon    t _ es       -> (f t:concat es)
        ELit    t _          -> [f t]
        EApp    t es         -> (f t:concat es)
        ELet    t bind e1 e2 -> (f t:foldBind f bind <> e1 <> e2)
        EFix    t _ e1 e2    -> (f t:e1 <> e2)
        ELam    t ps e       -> (f t:concatMap (foldPattern f) ps <> e)
        EIf     t e1 e2 e3   -> (f t:e1 <> e2 <> e3)
        EPat    t e cs       -> (f t:e <> concatMap (foldClause1 f) cs)
        EFun    t cs         -> (f t:concatMap (foldClause f) cs)
        EOp1    t op a       -> (f t:foldOp1 f op <> a)
        EOp2    t op a b     -> (f t:foldOp2 f op <> a <> b)
        ETuple  t es         -> (f t:concat es)
        EList   t es         -> (f t:concat es)
        ERow    t _ e r      -> (f t:e <> r)
        ERecord t r          -> (f t:r)
        EAnn    _ e          -> e

    foldClause :: (t -> s -> s) -> Clause t [ProgPattern t u] [s -> s] -> [s -> s]
    foldClause f = \case
        Clause  t ps cs      -> (f t:concatMap (foldPattern f) ps <> concatMap (foldChoice f) cs)

    foldClause1 :: (t -> s -> s) -> Clause t (ProgPattern t u) [s -> s] -> [s -> s]
    foldClause1 f = \case
        Clause  t p cs       -> (f t:foldPattern f p <> concatMap (foldChoice f) cs)

    foldChoice :: (t -> s -> s) -> Choice [s -> s] -> [s -> s]
    foldChoice f = \case
        Choice es e          -> concat (e:es)

    foldPattern :: (t -> s -> s) -> ProgPattern t u -> [s -> s]
    foldPattern f = cata $ \case
        PVar    t _          -> [f t]
        PCon    t _ ps       -> (f t:concat ps)
        PLit    t _          -> [f t]
        PAs     t _ p        -> (f t:p)
        POr     t p q        -> (f t:p <> q)
        PAny    t            -> [f t]
        PTuple  t ps         -> (f t:concat ps)
        PList   t ps         -> (f t:concat ps)
        PRow    t _ p r      -> (f t:p <> r)
        PRecord t r          -> (f t:r)
        PAnn    _ p          -> p

    foldBind :: (t -> s -> s) -> Binding t (ProgPattern t u) -> [s -> s]
    foldBind f = \case
        BPat    t p          -> (f t:foldPattern f p)
        BFun    t _ ps       -> (f t:concatMap (foldPattern f) ps)

    foldOp1 :: (t -> s -> s) -> Op1 t -> [s -> s]
    foldOp1 f = \case
        ONeg    t            -> [f t]
        ONot    t            -> [f t]

    foldOp2 :: (t -> s -> s) -> Op2 t -> [s -> s]
    foldOp2 f = \case
        OEq     t            -> [f t]
        ONeq    t            -> [f t]
        OAnd    t            -> [f t]
        OOr     t            -> [f t]
        OAdd    t            -> [f t]
        OSub    t            -> [f t]
        OMul    t            -> [f t]
        ODiv    t            -> [f t]
        OPow    t            -> [f t]
        OMod    t            -> [f t]
        OLt     t            -> [f t]
        OGt     t            -> [f t]
        OLte    t            -> [f t]
        OGte    t            -> [f t]
        OLarr   t            -> [f t]
        ORarr   t            -> [f t]
        OFpip   t            -> [f t]
        OBpip   t            -> [f t]
        OOpt    t            -> [f t]
        OStr    t            -> [f t]
        ODot    t            -> [f t]
        OField  t            -> [f t]

traverseExprTag :: (Applicative f) => (a -> f b) -> ProgExpr a u -> f (ProgExpr b u)
traverseExprTag f = cata $ \case

        EVar    t var        -> varExpr    <$> f t <*> pure var
        EHole   t            -> holeExpr   <$> f t
        ECon    t con es     -> conExpr    <$> f t <*> pure con <*> sequenceA es
        ELit    t prim       -> litExpr    <$> f t <*> pure prim
        EApp    t es         -> appExpr    <$> f t <*> sequenceA es
        ELet    t bind e1 e2 -> letExpr    <$> f t <*> binding bind <*> e1 <*> e2
        EFix    t name e1 e2 -> fixExpr    <$> f t <*> pure name <*> e1 <*> e2
        ELam    t ps e       -> lamExpr    <$> f t <*> traverse pattern_ ps <*> e
        EIf     t e1 e2 e3   -> ifExpr     <$> f t <*> e1 <*> e2 <*> e3
        EPat    t e cs       -> patExpr    <$> f t <*> e <*> traverse clause1 cs
        EFun    t cs         -> funExpr    <$> f t <*> traverse clause cs
        EOp1    t op a       -> op1Expr    <$> f t <*> op1 op <*> a
        EOp2    t op a b     -> op2Expr    <$> f t <*> op2 op <*> a <*> b
        ETuple  t es         -> tupleExpr  <$> f t <*> sequenceA es
        EList   t es         -> listExpr   <$> f t <*> sequenceA es
        ERow    t lab e r    -> rowExpr    <$> f t <*> pure lab <*> e <*> r
        ERecord t r          -> recordExpr <$> f t <*> r
        EAnn    t e          -> annExpr  t <$> e
  where
    binding = \case
        BPat    t p          -> BPat       <$> f t <*> pattern_ p
        BFun    t name ps    -> BFun       <$> f t <*> pure name <*> traverse pattern_ ps

    clause = \case
        Clause  t ps cs      -> Clause     <$> f t <*> traverse pattern_ ps <*> traverse choice cs

    clause1 = \case
        Clause  t p cs       -> Clause     <$> f t <*> pattern_ p <*> traverse choice cs

    choice = \case
        Choice es e          -> Choice     <$> sequenceA es <*> e

    pattern_ = cata $ \case
        PVar    t var        -> varPat     <$> f t <*> pure var
        PCon    t con ps     -> conPat     <$> f t <*> pure con <*> sequenceA ps
        PLit    t prim       -> litPat     <$> f t <*> pure prim
        PAs     t as p       -> asPat      <$> f t <*> pure as <*> p
        POr     t p q        -> orPat      <$> f t <*> p <*> q
        PAny    t            -> anyPat     <$> f t
        PTuple  t ps         -> tuplePat   <$> f t <*> sequenceA ps
        PList   t ps         -> listPat    <$> f t <*> sequenceA ps
        PRow    t lab p r    -> rowPat     <$> f t <*> pure lab <*> p <*> r
        PRecord t r          -> recordPat  <$> f t <*> r
        PAnn    t p          -> annPat   t <$> p

    op1 = \case
        ONeg    t            -> ONeg       <$> f t
        ONot    t            -> ONot       <$> f t

    op2 = \case
        OEq     t            -> OEq        <$> f t
        ONeq    t            -> ONeq       <$> f t
        OAnd    t            -> OAnd       <$> f t
        OOr     t            -> OOr        <$> f t
        OAdd    t            -> OAdd       <$> f t
        OSub    t            -> OSub       <$> f t
        OMul    t            -> OMul       <$> f t
        ODiv    t            -> ODiv       <$> f t
        OPow    t            -> OPow       <$> f t
        OMod    t            -> OMod       <$> f t
        OLt     t            -> OLt        <$> f t
        OGt     t            -> OGt        <$> f t
        OLte    t            -> OLte       <$> f t
        OGte    t            -> OGte       <$> f t
        OLarr   t            -> OLarr      <$> f t
        ORarr   t            -> ORarr      <$> f t
        OFpip   t            -> OFpip      <$> f t
        OBpip   t            -> OBpip      <$> f t
        OOpt    t            -> OOpt       <$> f t
        OStr    t            -> OStr       <$> f t
        ODot    t            -> ODot       <$> f t
        OField  t            -> OField     <$> f t

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

instance (Substitutable t a) => Substitutable (PredicateF t) a where
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
        PRecord t p          -> recordPat (apply sub t) p
        PAnn    t p          -> annPat    t p

instance (Substitutable t a, Substitutable p a) => Substitutable (Binding t p) a where
    apply sub = \case
        BPat t p             -> BPat (apply sub t) (apply sub p)
        BFun t name ps       -> BFun (apply sub t) name (apply sub ps)

instance (Substitutable g a) => Substitutable (Choice g) a where
    apply sub = \case
        Choice es e          -> Choice (apply sub es) (apply sub e)

instance (Substitutable t a, Substitutable p a, Substitutable (Choice c) a) => Substitutable (Clause t p c) a where
    apply sub = \case
        Clause  t p cs       -> Clause (apply sub t) (apply sub p) (apply sub cs)

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
        ERecord t e          -> recordExpr (apply sub t) e
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
{-# INLINE nullSub #-}

compose :: (Substitutable a a) => Substitution a -> Substitution a -> Substitution a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

mapsTo :: Name -> a -> Substitution a
mapsTo name val = Sub (Map.singleton name val)

withDefault :: a -> Name -> Substitution a -> a
withDefault default_ name = Map.findWithDefault default_ name . getSub

fromList :: [(Name, a)] -> Substitution a
fromList = Sub . Map.fromList
{-# INLINE fromList #-}

toList :: Substitution a -> [(Name, a)]
toList = Map.toList . getSub
{-# INLINE toList #-}

domain :: Substitution a -> [Name]
domain (Sub sub) = Map.keys sub
{-# INLINE domain #-}

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

normalizeExpr :: ProgExpr (TypeInfo [Error]) u -> ProgExpr (TypeInfo [Error]) u
normalizeExpr expr = apply sub expr
  where
    sub :: Substitution Type
    sub = fromList [(v, tVar k a) | ((v, k), a) <- zip vars (("a" <>) . showt <$> tail nats)]
    vars = nub (foldrExprTag (\t vs -> free (nodeType t) <> vs) [] expr)

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

data ErrorF t
    = UnificationError UnificationError
    | NotInScope Name
    | ConstructorNotInScope Name
    | NoSuchClass Name
    | MissingInstance Name t
    | PatternArityMismatch Name Int Int
    | NonBooleanGuard (Ast t)
    | NonExhaustivePatterns
    | AmbiguousType Name t

type Error = ErrorF Type

data UnificationError
    = InfiniteType
    | InfiniteKind
    | IncompatibleTypes
    | IncompatibleKinds
    | CannotMerge
    | ContextReductionFailed
    | ClassMismatch

deriving instance (Show t) => Show (ErrorF t)
deriving instance (Eq   t) => Eq   (ErrorF t)

deriving instance Functor ErrorF

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
  :: ( MonadSupply Int m
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
  :: ( MonadSupply Int m
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
  :: ( MonadSupply Int m
     , MonadError UnificationError m )
  => (Type, Type)
  -> (Type, Type)
  -> m (Substitution Type, Substitution Kind)
unifyTypePairs (t1, t2) (u1, u2) = do
    subs1 <- unifyTypes t1 u1
    subs2 <- unifyTypes (applyBoth subs1 t2) (applyBoth subs1 u2)
    pure (subs2 <> subs1)

matchTypePairs
  :: ( MonadSupply Int m
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
  :: ( MonadSupply Int m
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
                    s <- supply
                    let tv = tVar kRow ("$r" <> showt s)
                    combinePairs
                        (fromMap j (updateMap m1 ts), k)
                        (fromMap tv m2, tRow a t tv)
      where
        (a, t:ts) = Map.elemAt 0 m1
        updateMap m = \case
            [] -> Map.delete a m
            ts -> Map.insert a ts m

-------------------------------------------------------------------------------

super :: ClassEnv -> Name -> [Name]
super env name = maybe [] (fmap predicateName . classPredicates . fst)
                          (Env.lookup name env)

super1 :: ClassEnv -> Name -> [Name]
super1 env name = name:super env name

instances :: ClassEnv -> Name -> [Instance]
instances env name = maybe [] snd (Env.lookup name env)

bySuper :: ClassEnv -> Predicate -> [Predicate]
bySuper env self@(InClass name ty) =
    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

byInstance
  :: ( MonadError UnificationError m
     , MonadSupply Int m )
  => ClassEnv
  -> Predicate
  -> m (Maybe [Predicate])
byInstance env self@(InClass name ty) = do
    r <- sequence [runExceptT (tryInstance i) | i <- instances env name]
    pure (msum (rightToMaybe <$> r))
  where
    tryInstance ClassInfo{..} = applyBoth <$> matchClass classSignature self
                                          <*> pure classPredicates

entail :: ClassEnv -> [Predicate] -> Predicate -> Bool
entail env ps cl = any (cl `elem`) (bySuper env <$> ps)

isHeadNormalForm :: Predicate -> Bool
isHeadNormalForm (InClass _ t) =
    flip cata t $ \case
        TApp _ t1 _ -> t1
        TVar{}      -> True
        _           -> False

toHeadNormalForm
  :: (MonadError UnificationError m, MonadSupply Int m)
  => ClassEnv
  -> [Predicate]
  -> m [Predicate]
toHeadNormalForm env ps =
    fmap concat (mapM (hnf env) ps)
  where
    hnf env tycl
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = byInstance env tycl >>= \case
            Nothing  -> throwError ContextReductionFailed
            Just cls -> toHeadNormalForm env cls

simplify :: ClassEnv -> [Predicate] -> [Predicate]
simplify env = loop [] 
  where
    loop qs [] = qs
    loop qs (p:ps) = loop (if entail env (qs <> ps) p then qs else p:qs) ps

reduce
  :: (MonadSupply Int m)
  => ClassEnv
  -> [Predicate]
  -> m (Either UnificationError [Predicate])
reduce env cls = runExceptT (simplify env <$> toHeadNormalForm env cls)

reduceSet
  :: (MonadSupply Int m)
  => ClassEnv
  -> [Name]
  -> m [Name]
reduceSet env vars = do
    let ps = [InClass name (tVar kTyp "a") | name <- vars]
    qs <- fromRight (error "Implementation error") <$> reduce env ps
    pure (predicateName <$> qs)

unifyClass, matchClass
  :: ( MonadError UnificationError m
     , MonadSupply Int m )
  => Predicate
  -> Predicate
  -> m (Substitution Type, Substitution Kind)
unifyClass = lifted unifyTypes
matchClass = lifted matchTypes

lifted
  :: ( MonadError UnificationError m
     , MonadSupply Int m )
  => (Type -> Type -> m a)
  -> Predicate
  -> Predicate
  -> m a
lifted m (InClass c1 t1) (InClass c2 t2)
    | c1 == c2  = m t1 t2
    | otherwise = throwError ClassMismatch

-------------------------------------------------------------------------------

withClassInfo
  :: (MonadError Error m, MonadSupply Int m)
  => ([PredicateF Name] -> ClassInfo Type (Ast (TypeInfo ())) -> m a)
  -> Name
  -> Type
  -> ClassEnv
  -> m a
withClassInfo fn name ty env = do
    (ClassInfo{..}, insts) <- liftMaybe (NoSuchClass name) (Env.lookup name env)
    info <- sequence [tryMatch i | i <- insts]
    msum info & maybe (throwError (MissingInstance name ty)) (fn classPredicates)
  where
    tryMatch info@ClassInfo{..} = do
        sub <- eitherToMaybe <$> runExceptT (matchTypes (predicateType classSignature) ty)
        pure (applyBoth <$> sub <*> pure info)
