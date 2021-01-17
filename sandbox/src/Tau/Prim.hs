{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Prim where

import Tau.Env (Env)
import Tau.Expr
import qualified Data.Text as Text
import qualified Tau.Env as Env

class Prim a where
    toLiteral  :: a -> Literal
    toPrim :: Literal -> a

instance Prim Int where
    toLiteral = LInt
    toPrim = \case
        LInt lit -> lit
        _        -> 0

instance Prim String where
    toLiteral = LString . Text.pack
    toPrim = \case
        LString lit -> Text.unpack lit
        _           -> ""

instance Prim () where
    toLiteral = const LUnit
    toPrim = const ()

instance Prim Bool where
    toLiteral = LBool
    toPrim = \case
        LBool lit -> lit
        _         -> False

class IsFun f where
    toFun :: f -> Fun

instance (Prim a, Prim b) => IsFun (a -> b) where
    toFun f = Fun1 (\a -> let b = f (toPrim a) in toLiteral b)

instance (Prim a, Prim b, Prim c) => IsFun (a -> b -> c) where
    toFun f = Fun2 (\a b -> let c = f (toPrim a) (toPrim b) in toLiteral c)

instance (Prim a, Prim b, Prim c, Prim d) => IsFun (a -> b -> c -> d) where
    toFun f = Fun3 (\a b c -> let d = f (toPrim a) (toPrim b) (toPrim c) in toLiteral d)

instance (Prim a, Prim b, Prim c, Prim d, Prim e) => IsFun (a -> b -> c -> d -> e) where
    toFun f = Fun4 (\a b c d -> let e = f (toPrim a) (toPrim b) (toPrim c) (toPrim d) in toLiteral e)

instance (Prim a, Prim b, Prim c, Prim d, Prim e, Prim f) => IsFun (a -> b -> c -> d -> e -> f) where
    toFun f = Fun5 (\a b c d e -> let g = f (toPrim a) (toPrim b) (toPrim c) (toPrim d) (toPrim e) in toLiteral g)

data Fun 
    = Fun1 (Literal -> Literal)
    | Fun2 (Literal -> Literal -> Literal)
    | Fun3 (Literal -> Literal -> Literal -> Literal)
    | Fun4 (Literal -> Literal -> Literal -> Literal -> Literal)
    | Fun5 (Literal -> Literal -> Literal -> Literal -> Literal -> Literal)

arity :: Fun -> Int
arity = \case
    Fun1 _ -> 1
    Fun2 _ -> 2
    Fun3 _ -> 3
    Fun4 _ -> 4
    Fun5 _ -> 5

applyFun :: Fun -> [Literal] -> Literal
applyFun fun args =
    case fun of
        Fun1 f -> f (head args)
        Fun2 f -> f (head args) (args !! 1)
        Fun3 f -> f (head args) (args !! 1) (args !! 2)
        Fun4 f -> f (head args) (args !! 1) (args !! 2) (args !! 3)
        Fun5 f -> f (head args) (args !! 1) (args !! 2) (args !! 3) (args !! 4)

primEnv :: Env Fun
primEnv = Env.fromList
    [ ( "showInt"  , toFun (show :: Int -> String) )
    , ( "showBool" , toFun (show :: Bool -> String) )
    ]
