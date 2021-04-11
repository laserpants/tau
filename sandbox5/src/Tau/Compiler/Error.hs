{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Error where

import Data.Text (Text)
import Tau.Lang
import Tau.Prog
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
    = CannotUnify t t UnificationError
    | CannotMatch t t UnificationError
    | UnboundTypeIdentifier Name
    | MissingClass Name
    | MissingInstance Name t
    | NoDataConstructor Name
    | ListElemUnficationError
    | ListPatternElemUnficationError
    | ConstructorPatternArityMismatch Name Int Int
    | ConstructorPatternTypeMismatch Name
    | NonBooleanGuardCondition
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Error = ErrorT Type
