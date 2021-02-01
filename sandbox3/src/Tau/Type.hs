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
type Type a = Fix (TypeF a)

-- | Base functor for Scheme
data SchemeF a
    = Forall Kind Name [Name] a
    | Scheme (Type Int)
    deriving (Functor, Foldable, Traversable)

deriveShow  ''SchemeF
deriveEq    ''SchemeF
deriveShow1 ''SchemeF
deriveEq1   ''SchemeF

-- | Polymorphic type schemes
type Scheme = Fix SchemeF
