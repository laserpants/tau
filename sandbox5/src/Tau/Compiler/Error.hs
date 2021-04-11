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
    = Err Text
    -- 
    | CannotUnify t t UnificationError 
    | CannotMatch t t UnificationError 
    -- 
    | UnboundTypeIdentifier Name
    | MissingClass Name
    | MissingInstance Name t
    | NoDataConstructor Name
    -- 
    | ListPatternElemUnficationError 
    -- Expr type inference errors
--    | BadGuardCondition t
--    | ClausePatternTypeMismatch t t
----    | ClauseExprTypeMismatch (ProgExpr (TypeInfo (ErrorT t))) t t
--    -- Pattern type inference errors
    | ConstructorPatternArityMismatch Name Int Int
    | ConstructorPatternTypeMismatch Name 
--    -- 
--    -- 
--    -- 
--    -- 
--    | MissingClass Name
--    | MissingInstance Name t
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Error = ErrorT Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

