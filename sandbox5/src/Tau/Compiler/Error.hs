{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Error where

import Data.Text (Text)
import Tau.Lang
import Tau.Tooling
import Tau.Type

data UnificationError
    = InfiniteType
    | InfiniteKind
    | IncompatibleTypes
    | IncompatibleKinds
    | MergeFailed
    | ClassMismatch
    | ContextReductionFailed
--    | IncompatibleRows
    deriving (Show, Eq)

data Error
    = CannotUnify Type Type UnificationError
    | KindMismatch Kind Kind UnificationError
    | NotInScope Name
    | MissingDataConstructor Name
    | NonExhaustivePatterns
--    | CannotMatch t t UnificationError
    | MissingClass Name
    | MissingInstance Name Type
    | ListElemUnficationError
    | ListPatternElemUnficationError
    | ConstructorPatternArityMismatch Name Int Int
    | ConstructorPatternTypeMismatch Name
    | GuardConditionNotABool
    deriving (Show, Eq) -- , Functor, Foldable, Traversable)

--type Error = ErrorT Type
