{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Tau.Lang
import Tau.Tool
import Tau.Type

data TypeInfoT t = TypeInfo
    { nodeType       :: t
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

type TypeInfo = TypeInfoT Type

inferAst = undefined

inferPrim = undefined

inferPattern = undefined

inferOp1 = undefined

inferOp2 = undefined

inferClause = undefined
