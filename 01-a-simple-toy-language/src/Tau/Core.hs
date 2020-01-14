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
    | Closure !Name !Expr Env
    deriving (Show, Eq)


--instance Show Value where
--    show (Int n)    = show n
--    show (Bool b)   = show b
--    show (String s) = show s
--    show (Char c)   = show c
--    show Unit       = "()"
--    show Closure{}  = "<function>"


data Expr
    = Var !Name
    | App !Expr !Expr
    | Lam !Name !Expr
    | Let !Name !Expr !Expr
    | Lit !Value
    | Fix !Expr
    | If !Expr !Expr !Expr
    | Op !Op !Expr !Expr
    deriving (Show, Eq)


data Op
    = Add
    | Sub
    | Mul
    | Eq
    deriving (Show, Eq, Ord)


data Program = Program !(Map Name Expr) !Expr
    deriving (Show, Eq)
