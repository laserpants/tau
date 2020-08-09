{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Ast where

import Data.Eq.Deriving
import Data.Functor.Foldable
import Tau.Pattern
import Tau.Prim
import Tau.Type
import Tau.Util
import Text.Show.Deriving

-- | Source language expression tree 
data ExprF a 
    = VarS Name
    | LamS Name a
    | AppS [a]
    | LitS Prim
    | LetS [(Name, a)] a
    | IfS a a a
    | CaseS a [(Pattern, a)]
    | OpS (OpF a)
    | AnnS a Type
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Expr = Fix ExprF

-- | Operators
data OpF a
    = AddS a a
    | SubS a a
    | MulS a a
    | EqS a a 
    | LtS a a 
    | GtS a a 
    | NegS a
    | NotS a
    deriving (Show, Eq, Functor, Foldable, Traversable)

-- | VarS constructor
varS :: Name -> Expr
varS = Fix . VarS

-- | LamS constructor
lamS :: Name -> Expr -> Expr
lamS a = Fix . LamS a 

-- | AppS constructor
appS :: [Expr] -> Expr
appS = Fix . AppS

-- | LitS constructor
litS :: Prim -> Expr
litS = Fix . LitS

-- | LetS constructor
letS :: [(Name, Expr)] -> Expr -> Expr
letS a = Fix . LetS a

-- | IfS constructor
ifS :: Expr -> Expr -> Expr -> Expr
ifS a1 a2 a3 = Fix (IfS a1 a2 a3)

-- | CaseS constructor
caseS :: Expr -> [(Pattern, Expr)] -> Expr
caseS a = Fix . CaseS a

-- | OpS constructor
opS :: OpF Expr -> Expr
opS = Fix . OpS

-- annS = TODO

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)
$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)
