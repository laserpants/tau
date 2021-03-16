{-# LANGUAGE StrictData #-}
module Tau.Lang.Prog where

import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))

type ProgExpr = Expr () (Pattern () ()) 
                        (Binding (Pattern () ())) 
                        [Pattern () ()] 
                        (Op1 ()) 
                        (Op2 ())

-- | Product type
data Product = Prod Name [Type]
    deriving (Show, Eq)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq)

--xx = Sum "List" ["a"] 
--    [ Prod "Cons" [tVar kTyp "a", tList (tVar kTyp "a")]
--    , Prod "Nil"  []
--    ]

-- | Top-level definition
data Definition = Def 
    { defName    :: Name 
    , defClauses :: [Clause (Pattern () ()) ProgExpr] 
    , defLocal   :: [Definition]
    } deriving (Show, Eq)

-- | Type class instance
data Instance a = Instance
    { predicates   :: [Predicate]
    , instanceType :: Type
    , instanceDict :: a
    } deriving (Show, Eq)

-- | Type class
type Class a = ([Name], [Instance a])

type ClassEnv a = Env (Class a)

data Module = Module 
    { moduleName      :: Name
    , moduleTypes     :: [Datatype]
    , moduleDefs      :: [Definition]
    , moduleClasses   :: [Class ProgExpr]
    , moduleInstances :: [Instance ProgExpr]
    } deriving (Show, Eq)
