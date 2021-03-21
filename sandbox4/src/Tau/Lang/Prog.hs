{-# LANGUAGE StrictData #-}
module Tau.Lang.Prog where

import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))

type ProgExpr = Expr () (Pattern () () ()) 
                        (Binding (Pattern () () ())) 
                        [Pattern () () ()] 
                        (Op1 ()) 
                        (Op2 ())
                        () 
                        ()

-- | Product type
data Product = Prod Name [Type]
    deriving (Show, Eq)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq)

-- | Top-level definition
data Definition = Def 
    { defName    :: Name 
    , defClauses :: [Clause (Pattern () () ()) ProgExpr] 
    , defLocal   :: [Definition]
    } deriving (Show, Eq)

-- ClassInfo
type ClassInfo p a = ([PredicateT p], PredicateT p, [(Name, a)])

--type ClassDef = ([PredicateT Name], PredicateT Name, [(Name, Type)])
--type ClassDef = ClassInfo Name Type

---- | Type class instance
--data Instance a = Instance
--    { predicates   :: [Predicate]
--    , instanceType :: Type
--    , instanceDict :: a
--    } deriving (Show, Eq)

--type Instance2 = ([Predicate], Predicate, [(Name, ProgExpr)])
--type Instance2 = ClassInfo Type ProgExpr

--data Instance2 = Instance2
--    { predicates2   :: [Predicate]
--    , instanceType2 :: Type
--    , instanceMethods :: [(Name, ProgExpr)]
--    } deriving (Show, Eq)


--type ClassInfo a = ([Name], [(Name, Type)], [Instance a])
    -- superClasses
    -- classMethods
    -- classInstances

--type ClassEnv a = Env (ClassInfo a)
--type ClassEnv a = Env ([Name], Name, [(Name, Type)], [Instance a])


data Module = Module 
    { moduleName      :: Name
    , moduleTypes     :: [Datatype]
    , moduleDefs      :: [Definition]
    , moduleClasses   :: [ClassInfo Name Type]
    , moduleInstances :: [ClassInfo Type ProgExpr]
    } deriving (Show, Eq)
