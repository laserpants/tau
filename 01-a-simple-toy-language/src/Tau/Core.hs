module Tau.Core where

import Data.Map (Map)
import Tau.Util


type Env = Map Var Value


data Value 
    = Int !Integer 
    | Bool !Bool
    -- | Int32 !Int32
    -- | Int64 !Int64
    -- | Float !Double
    -- | Unit
    -- | Char !Char
    -- | String !Text
    | Closure !Var !Expr Env
    deriving (Eq)


instance Show Value where
    show (Int n)    = show n
    show (Bool b)   = show b
    -- show (VFloat f)  = show f
    -- show (VChar c)   = show c
    -- show (VString s) = show s
    -- show VUnit       = "()"
    show Closure{}  = "<<closure>>"


data Expr
    = Var !Var
    | App !Expr !Expr
    | Lam !Var !Expr
    | Let !Var !Expr !Expr
    -- | Case ...
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


data Program = Program !(Map Var Expr) !Expr
    deriving (Show, Eq)
