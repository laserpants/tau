{-# LANGUAGE StrictData #-}
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
    ( ClassInfo Name Type                     -- Abstract interface
    , List (ClassInfo Type (Ast TypeInfo)) )  -- Instances

type ConstructorEnv = Env (Set Name, Int)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

patternPredicates :: ProgPattern (TypeInfoT t) -> [Predicate]
patternPredicates = nodePredicates . patternTag

exprPredicates :: ProgExpr (TypeInfoT t) -> [Predicate]
exprPredicates = nodePredicates . exprTag

astPredicates :: Ast (TypeInfoT t) -> [Predicate]
astPredicates = exprPredicates . getAst

constructorEnv :: [(Name, ([Name], Int))] -> ConstructorEnv
constructorEnv = Env.fromList . (first Set.fromList <$$>)
