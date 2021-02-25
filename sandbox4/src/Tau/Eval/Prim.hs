{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Eval.Prim where

import Tau.Util.Env (Env)
import Tau.Lang.Expr
import Tau.Util
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

class Prim a where
    toLiteral :: a -> Literal
    primitive :: Literal -> a

instance Prim Int where
    toLiteral = LInt
    primitive = \case
        LInt lit -> lit
        _        -> 0

instance Prim Integer where
    toLiteral = LInteger
    primitive = \case
        LInteger lit -> lit
        _            -> 0

instance Prim Double where
    toLiteral = LFloat
    primitive = \case
        LFloat lit -> lit
        _          -> 0

instance Prim String where
    toLiteral = LString . Text.pack
    primitive = \case
        LString lit -> Text.unpack lit
        _           -> ""

instance Prim Char where
    toLiteral = LChar
    primitive = \case
        LChar lit -> lit
        _         -> ' '

instance Prim () where
    toLiteral = const LUnit
    primitive = const ()

instance Prim Bool where
    toLiteral = LBool
    primitive = \case
        LBool lit -> lit
        _         -> False

fun1 :: (Prim a, Prim b) => (a -> b) -> Fun 
fun1 f = Fun1 (\a -> let b = f (primitive a) in toLiteral b)

fun2 :: (Prim a, Prim b, Prim c) => (a -> b -> c) -> Fun 
fun2 f = Fun2 (\a b -> let c = f (primitive a) (primitive b) in toLiteral c)

fun3 :: (Prim a, Prim b, Prim c, Prim d) => (a -> b -> c -> d) -> Fun 
fun3 f = Fun3 (\a b c -> let d = f (primitive a) (primitive b) (primitive c) in toLiteral d)

fun4 :: (Prim a, Prim b, Prim c, Prim d, Prim e) => (a -> b -> c -> d -> e) -> Fun 
fun4 f = Fun4 (\a b c d -> let e = f (primitive a) (primitive b) (primitive c) (primitive d) in toLiteral e)

fun5 :: (Prim a, Prim b, Prim c, Prim d, Prim e, Prim f) => (a -> b -> c -> d -> e -> f) -> Fun 
fun5 f = Fun5 (\a b c d e -> let g = f (primitive a) (primitive b) (primitive c) (primitive d) (primitive e) in toLiteral g)

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

--primEnv :: Env Fun
--primEnv = Env.fromList
--    -- Int:show
--    -- Int:(==)
--    -- String:length
--    -- String:concat
--    [ ( "showInt"    , fun1 (show   :: Int -> String) )
--    , ( "showBool"   , fun1 (show   :: Bool -> String) )
--    , ( "showUnit"   , fun1 (show   :: () -> String) )
--    , ( "(+)Int"     , fun2 ((+)    :: Int -> Int -> Int) )
--    , ( "(*)Int"     , fun2 ((*)    :: Int -> Int -> Int) )
--    , ( "(-)Int"     , fun2 ((-)    :: Int -> Int -> Int) )
--    , ( "(==)Int"    , fun2 ((==)   :: Int -> Int -> Bool) )
--    , ( "(==)Bool"   , fun2 ((==)   :: Bool -> Bool -> Bool) )
--    , ( "(==)Unit"   , fun2 ((==)   :: () -> () -> Bool) )
--    , ( "(==)String" , fun2 ((==)   :: String -> String -> Bool) )
--    , ( "strlen"     , fun1 (length :: String -> Int) )
--    , ( "strconcat"  , fun2 ((++)   :: String -> String -> String) )
--    , ( "strconcat3" , fun3 ((\s t u -> s ++ t ++ u) :: String -> String -> String -> String) )  -- TODO: remove
--    ]
