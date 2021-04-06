{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Error where

import Data.Text (Text)
import Tau.Lang
import Tau.Tool
import Tau.Type

data UnificationError
    = InfiniteType
    | KindMismatch
    | MergeFailed
    | IncompatibleTypes
    | IncompatibleRows
    deriving (Show, Eq)

data ErrorT t
    = Err Text
    -- 
    -- 
    | CannotUnify UnificationError t t
    | CannotMatch UnificationError t t
    -- 
    -- Expr type inference errors
    | BadGuardCondition t
    | ClausePatternTypeMismatch t t
    | ClauseExprTypeMismatch (ProgExpr TypeInfo) t t
    -- Pattern type inference errors
    | ListPatternTypeUnficationError 
    | NoDataConstructor Name
    | ConstructorPatternArityMismatch Name Int Int
    | ConstructorPatternTypeMismatch Name t [t]
    -- 
    -- 
    | UnboundTypeIdentifier Name
    -- 
    -- 
    | MissingClass Name
    | MissingInstance Name t
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Error = ErrorT Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

