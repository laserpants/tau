{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
module Tau.Prog where

import Data.List (nub)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first)
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Tool
import Tau.Type
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

-- | Product type
data Product = Mul Name [Type]
    deriving (Show, Eq, Ord)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq, Ord)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data ClassInfo p a = ClassInfo 
    { classSuper     :: List (PredicateT p)
    , classSignature :: PredicateT p
    , classMethods   :: List (Name, a)
    } deriving (Show, Eq)

-- Environments

type Context = Env (Set Name)

type TypeEnv = Env Scheme

type ClassEnv = Env 
    ( ClassInfo Name Type                          -- Abstract interface
    , List (ClassInfo Type (Ast (TypeInfo ()))) )  -- Instances

type ConstructorEnv = Env (Set Name, Int)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data TypeInfoT e t = TypeInfo
    { nodeType       :: t
    , nodePredicates :: [Predicate] 
    , nodeErrors     :: e
    }

type TypeInfo e = TypeInfoT e Type

-- Type class instances for TypeInfo

deriving instance (Show e, Show t) => 
    Show (TypeInfoT e t)

deriving instance (Eq e, Eq t) => 
    Eq (TypeInfoT e t)

deriving instance Functor (TypeInfoT e)

instance (Typed t) => Typed (TypeInfoT e t) where
    typeOf = typeOf . nodeType 

instance FreeIn TypeEnv where
    free = free . Env.elems

instance (Show e) => Tag (TypeInfo [e]) where
    tarr t1 t2 = TypeInfo{ nodeType       = nodeType t1 `tArr` nodeType t2
                         , nodePredicates = nodePredicates t1 <> nodePredicates t2
                         , nodeErrors     = nodeErrors t1 <> nodeErrors t2 }

    tapp t1 t2 = TypeInfo{ nodeType       = tApp (nodeType t1) (nodeType t2)
                         , nodePredicates = nodePredicates t1 <> nodePredicates t2
                         , nodeErrors     = nodeErrors t1 <> nodeErrors t2 }

    fromType t = TypeInfo{ nodeType       = t
                         , nodePredicates = []
                         , nodeErrors     = [] }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

patternPredicates :: ProgPattern (TypeInfoT e t) -> [Predicate]
patternPredicates = nodePredicates . patternTag

exprPredicates :: ProgExpr (TypeInfoT e t) -> [Predicate]
exprPredicates = nodePredicates . exprTag

guardPredicates :: Guard (ProgExpr (TypeInfoT e t)) -> [Predicate]
guardPredicates (Guard es e) = exprPredicates e <> (exprPredicates =<< es)

clausePredicates :: Clause s (ProgPattern (TypeInfoT e t)) (ProgExpr (TypeInfoT e t)) -> [Predicate]
clausePredicates (Clause _ ps gs) = concat ((patternPredicates <$> ps) <> (guardPredicates <$> gs))

astPredicates :: Ast (TypeInfoT e t) -> [Predicate]
astPredicates = exprPredicates . getAst

constructorEnv :: [(Name, ([Name], Int))] -> ConstructorEnv
constructorEnv = Env.fromList . (first Set.fromList <$$>)

simplifyPredicates :: TypeInfo e -> TypeInfo e
simplifyPredicates (TypeInfo ty ps e) = TypeInfo ty (nub (filter relevant ps)) e
  where
    freeVars = free ty
    relevant (InClass _ (Fix (TVar _ var))) 
        | var `notElem` freeVars = False
    relevant _                   = True

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

astTypeVars :: Ast (TypeInfo e) -> [(Name, Kind)]
astTypeVars (Ast expr) = nub (exprTypeVars expr)
  where
    exprTypeVars = cata $ \case
        EVar    t _            -> typeVars (typeOf t)
        ECon    t _ as         -> typeVars (typeOf t) <> concat as
        ELit    t _            -> typeVars (typeOf t)
        EApp    t as           -> typeVars (typeOf t) <> concat as
        ELet    t bind a1 a2   -> typeVars (typeOf t) <> bindingTypeVars bind <> a1 <> a2
        EFix    t _ a1 a2      -> typeVars (typeOf t) <> a1 <> a2
        ELam    t ps a         -> typeVars (typeOf t) <> (patternTypeVars =<< ps) <> a
        EIf     t a1 a2 a3     -> typeVars (typeOf t) <> a1 <> a2 <> a3
        EPat    t as clauses   -> typeVars (typeOf t) <> concat as <> (clauseTypeVars =<< clauses)
        EFun    t clauses      -> typeVars (typeOf t) <> (clauseTypeVars =<< clauses)
        EOp1    t op a         -> typeVars (typeOf t) <> op1TypeVars op <> a
        EOp2    t op a b       -> typeVars (typeOf t) <> op2TypeVars op <> a <> b
        ETuple  t as           -> typeVars (typeOf t) <> concat as
        EList   t as           -> typeVars (typeOf t) <> concat as
        ERecord t row          -> typeVars (typeOf t) <> concat row

    bindingTypeVars = \case
        BLet    t p            -> typeVars (typeOf t) <> patternTypeVars p
        BFun    t _ ps         -> typeVars (typeOf t) <> (patternTypeVars =<< ps)

    clauseTypeVars = \case
        Clause  t ps gs        -> typeVars (typeOf t) <> (patternTypeVars =<< ps) <> (guardTypeVars =<< gs)

    guardTypeVars = \case
        Guard es e             -> concat es <> e

    patternTypeVars = cata $ \case
        PVar    t var          -> typeVars (typeOf t)
        PCon    t _ ps         -> typeVars (typeOf t) <> concat ps
        PLit    t _            -> typeVars (typeOf t)
        PAs     t _ p          -> typeVars (typeOf t) <> p
        POr     t p q          -> typeVars (typeOf t) <> p <> q
        PAny    t              -> typeVars (typeOf t)
        PTuple  t ps           -> typeVars (typeOf t) <> concat ps
        PList   t ps           -> typeVars (typeOf t) <> concat ps
        PRecord t row          -> typeVars (typeOf t) <> concat row

    op1TypeVars = \case
        ONeg    t              -> typeVars (typeOf t)
        ONot    t              -> typeVars (typeOf t)

    op2TypeVars = \case
        OEq     t              -> typeVars (typeOf t)
        ONeq    t              -> typeVars (typeOf t)
        OAnd    t              -> typeVars (typeOf t)
        OOr     t              -> typeVars (typeOf t)
        OAdd    t              -> typeVars (typeOf t)
        OSub    t              -> typeVars (typeOf t)
        OMul    t              -> typeVars (typeOf t)
        ODiv    t              -> typeVars (typeOf t)
        OPow    t              -> typeVars (typeOf t)
        OMod    t              -> typeVars (typeOf t)
        OLt     t              -> typeVars (typeOf t)
        OGt     t              -> typeVars (typeOf t)
        OLte    t              -> typeVars (typeOf t)
        OGte    t              -> typeVars (typeOf t)
        OLarr   t              -> typeVars (typeOf t)
        ORarr   t              -> typeVars (typeOf t)
        OFpipe  t              -> typeVars (typeOf t)
        OBpipe  t              -> typeVars (typeOf t)
        OOpt    t              -> typeVars (typeOf t)
        OStrc   t              -> typeVars (typeOf t)
        ONdiv   t              -> typeVars (typeOf t)
