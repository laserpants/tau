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
    | InfiniteKind
    | IncompatibleTypes
    | IncompatibleKinds
    | MergeFailed
--    | IncompatibleRows
    deriving (Show, Eq)

data ErrorT t
    = CannotUnify t t UnificationError
    | KindMismatch Kind Kind UnificationError
    | UnboundTypeIdentifier Name
    | MissingDataConstructor Name
--    | CannotMatch t t UnificationError
    | MissingClass Name
    | MissingInstance Name t
    | ListElemUnficationError
    | ListPatternElemUnficationError
    | ConstructorPatternArityMismatch Name Int Int
    | ConstructorPatternTypeMismatch Name
    | GuardConditionNotABool
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Error = ErrorT Type
