{-# LANGUAGE StrictData #-}
module Tau.Lang.Prog where

import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util

-- | Product type
data Product = Prod Name [Type]
    deriving (Show, Eq)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq)

type ProgExpr = Expr () (Pattern ()) 
                        (Binding (Pattern ())) 
                        [Pattern ()] 
                        (Op1 ()) 
                        (Op2 ())

data Definition = Def Name ProgExpr
    deriving (Show, Eq)

data Module = Module 
    { moduleName  :: Name
    , moduleTypes :: [Datatype]
    , moduleDefs  :: [Definition]
    } deriving (Show, Eq)
