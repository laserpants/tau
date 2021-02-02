{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where

import Control.Arrow (second)
import Data.Functor.Foldable
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Void
import Tau.Env
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

-- | Base functor for Kind
data KindF a 
    = KTyp
--  | KCls
    | KArr a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

-- | Kinds
type Kind = Fix KindF

-- | Base functor for Type
data TypeF g a
    = TVar Kind Name 
    | TCon Kind Name 
    | TArr a a
    | TApp a a
    | TGen g
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

-- | Types
type TypeT a = Fix (TypeF a)

type Type   = TypeT Void
type IxType = TypeT Int

-- | Type class constraints
data PredicateT a = InClass Name (TypeT a)
    deriving (Show, Eq, Ord)

type Predicate   = PredicateT Void
type IxPredicate = PredicateT Int

-- | Polymorphic type schemes
data Scheme = Forall [Kind] [IxPredicate] IxType
    deriving (Show, Eq)
