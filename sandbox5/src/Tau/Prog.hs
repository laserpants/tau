{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
module Tau.Prog where

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
