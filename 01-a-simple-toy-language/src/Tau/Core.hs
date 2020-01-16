module Tau.Core where

import Data.Map (Map)
import Data.Text (Text)
import Tau.Type
import Tau.Util


type Env = Map Name Value


data Value
    = Int !Integer
    | Bool !Bool
    | String !Text
    | Char !Char
    | Unit
    | Closure !Name !Expr !Env
    deriving (Show, Eq)


data Expr
    = Var !Name
    | App !Expr !Expr
    | Lam !Name !Expr
    | Let !Name !Expr !Expr
    | Lit !Value
    | Fix !Expr
    | If !Expr !Expr !Expr
    | Op !Op !Expr !Expr
    | Neg !Expr
    deriving (Show, Eq)


data Op
    = Add
    | Sub
    | Mul
    | Eq
    deriving (Show, Eq, Ord)


data Program = Program !(Map Name Expr) !Expr
    deriving (Show, Eq)
