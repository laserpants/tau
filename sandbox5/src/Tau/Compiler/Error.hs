module Tau.Compiler.Error where

import Data.Text (Text)
import Tau.Tool
import Tau.Type

data UnificationError
    = InfiniteType
    | KindMismatch
    | MergeFailed
    | IncompatibleTypes
    | IncompatibleRows
    deriving (Show, Eq)

data Error 
    = Err Text
    -- 
    | CannotUnify UnificationError Type Type
    | CannotMatch UnificationError Type Type
    -- Pattern type inference errors
    | ListPatternTypeUnficationError Error
    | NoDataConstructor Name
    | ConstructorPatternArityMismatch Name Int Int
    -- 
    | UnboundTypeIdentifier Name
    -- 
    | MissingClassInstance Name Type
    deriving (Show, Eq)

