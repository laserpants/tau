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

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)
$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)
