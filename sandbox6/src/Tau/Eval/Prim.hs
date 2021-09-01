{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Eval.Prim where

import Data.Text (Text)
import Tau.Env (Env)
import Tau.Misc (Prim(..))
import qualified Data.Text as Text
import qualified Tau.Env as Env

class PrimType a where
    toPrim   :: a -> Prim
    fromPrim :: Prim -> a

instance PrimType Int where
    toPrim = TInt
    fromPrim = \case
        TInt lit -> lit
        _        -> 0

instance PrimType Integer where
    toPrim = TBig
    fromPrim = \case
        TBig lit -> lit
        _        -> 0

instance PrimType Float where
    toPrim = TFloat
    fromPrim = \case
        TFloat lit -> lit
        _          -> 0

instance PrimType Double where
    toPrim = TDouble
    fromPrim = \case
        TDouble lit -> lit
        _           -> 0

instance PrimType Text where
    toPrim = TString 
    fromPrim = \case
        TString lit -> lit
        _           -> Text.pack ""

instance PrimType Char where
    toPrim = TChar
    fromPrim = \case
        TChar lit -> lit
        _         -> ' '

instance PrimType () where
    toPrim = const TUnit
    fromPrim = const ()

instance PrimType Bool where
    toPrim = TBool
    fromPrim = \case
        TBool lit -> lit
        _         -> False

fun1 :: (PrimType a, PrimType b) => (a -> b) -> Fun 
fun1 f = Fun1 (\a -> let b = f (fromPrim a) in toPrim b)

fun2 :: (PrimType a, PrimType b, PrimType c) => (a -> b -> c) -> Fun 
fun2 f = Fun2 (\a b -> let c = f (fromPrim a) (fromPrim b) in toPrim c)

fun3 :: (PrimType a, PrimType b, PrimType c, PrimType d) => (a -> b -> c -> d) -> Fun 
fun3 f = Fun3 (\a b c -> let d = f (fromPrim a) (fromPrim b) (fromPrim c) in toPrim d)

fun4 :: (PrimType a, PrimType b, PrimType c, PrimType d, PrimType e) => (a -> b -> c -> d -> e) -> Fun 
fun4 f = Fun4 (\a b c d -> let e = f (fromPrim a) (fromPrim b) (fromPrim c) (fromPrim d) in toPrim e)

fun5 :: (PrimType a, PrimType b, PrimType c, PrimType d, PrimType e, PrimType f) => (a -> b -> c -> d -> e -> f) -> Fun 
fun5 f = Fun5 (\a b c d e -> let g = f (fromPrim a) (fromPrim b) (fromPrim c) (fromPrim d) (fromPrim e) in toPrim g)

data Fun 
    = Fun1 (Prim -> Prim)
    | Fun2 (Prim -> Prim -> Prim)
    | Fun3 (Prim -> Prim -> Prim -> Prim)
    | Fun4 (Prim -> Prim -> Prim -> Prim -> Prim)
    | Fun5 (Prim -> Prim -> Prim -> Prim -> Prim -> Prim)

arity :: Fun -> Int
arity = \case
    Fun1 _ -> 1
    Fun2 _ -> 2
    Fun3 _ -> 3
    Fun4 _ -> 4
    Fun5 _ -> 5

applyFun :: Fun -> [Prim] -> Prim
applyFun fun args =
    case fun of
        Fun1 f -> f (head args)
        Fun2 f -> f (head args) (args !! 1)
        Fun3 f -> f (head args) (args !! 1) (args !! 2)
        Fun4 f -> f (head args) (args !! 1) (args !! 2) (args !! 3)
        Fun5 f -> f (head args) (args !! 1) (args !! 2) (args !! 3) (args !! 4)

primEnv :: Env Fun
primEnv = Env.fromList
    [ ( "Unit.(==)"            , fun2 ((==) :: () -> () -> Bool) )
    , ( "Bool.(==)"            , fun2 ((==) :: Bool -> Bool -> Bool) )
    , ( "Int.(==)"             , fun2 ((==) :: Int -> Int -> Bool) )
    , ( "Integer.(==)"         , fun2 ((==) :: Integer -> Integer -> Bool) )
    , ( "Float.(==)"           , fun2 ((==) :: Float -> Float -> Bool) )
    , ( "Double.(==)"          , fun2 ((==) :: Double -> Double -> Bool) )
    , ( "Char.(==)"            , fun2 ((==) :: Char -> Char -> Bool) )
    , ( "String.(==)"          , fun2 ((==) :: Text -> Text -> Bool) )

    , ( "Unit.(/=)"            , fun2 ((/=) :: () -> () -> Bool) )
    , ( "Bool.(/=)"            , fun2 ((/=) :: Bool -> Bool -> Bool) )
    , ( "Int.(/=)"             , fun2 ((/=) :: Int -> Int -> Bool) )
    , ( "Integer.(/=)"         , fun2 ((/=) :: Integer -> Integer -> Bool) )
    , ( "Float.(/=)"           , fun2 ((/=) :: Float -> Float -> Bool) )
    , ( "Double.(/=)"          , fun2 ((/=) :: Double -> Double -> Bool) )
    , ( "Char.(/=)"            , fun2 ((/=) :: Char -> Char -> Bool) )
    , ( "String.(/=)"          , fun2 ((/=) :: Text -> Text -> Bool) )

    , ( "Int.(+)"              , fun2 ((+) :: Int -> Int -> Int ) )
    , ( "Integer.(+)"          , fun2 ((+) :: Integer -> Integer -> Integer ) )
    , ( "Float.(+)"            , fun2 ((+) :: Float -> Float -> Float ) )
    , ( "Double.(+)"           , fun2 ((+) :: Double -> Double -> Double ) )

    , ( "Int.(-)"              , fun2 ((-) :: Int -> Int -> Int ) )
    , ( "Integer.(-)"          , fun2 ((-) :: Integer -> Integer -> Integer ) )
    , ( "Float.(-)"            , fun2 ((-) :: Float -> Float -> Float ) )
    , ( "Double.(-)"           , fun2 ((-) :: Double -> Double -> Double ) )

    , ( "Int.(*)"              , fun2 ((*) :: Int -> Int -> Int ) )
    , ( "Integer.(*)"          , fun2 ((*) :: Integer -> Integer -> Integer ) )
    , ( "Float.(*)"            , fun2 ((*) :: Float -> Float -> Float ) )
    , ( "Double.(*)"           , fun2 ((*) :: Double -> Double -> Double ) )

    , ( "Float.(/)"            , fun2 ((/) :: Float -> Float -> Float ) )
    , ( "Double.(/)"           , fun2 ((/) :: Double -> Double -> Double ) )

    , ( "Bool.(<)"             , fun2 ((<) :: Bool -> Bool -> Bool ) )
    , ( "Int.(<)"              , fun2 ((<) :: Int -> Int -> Bool ) )
    , ( "Integer.(<)"          , fun2 ((<) :: Integer -> Integer -> Bool ) )
    , ( "Float.(<)"            , fun2 ((<) :: Float -> Float -> Bool ) )
    , ( "Double.(<)"           , fun2 ((<) :: Double -> Double -> Bool ) )
    , ( "Char.(<)"             , fun2 ((<) :: Char -> Char -> Bool ) )
    , ( "String.(<)"           , fun2 ((<) :: Text -> Text -> Bool ) )
    , ( "Unit.(<)"             , fun2 ((<) :: () -> () -> Bool ) )

    , ( "Bool.(<=)"            , fun2 ((<=) :: Bool -> Bool -> Bool ) )
    , ( "Int.(<=)"             , fun2 ((<=) :: Int -> Int -> Bool ) )
    , ( "Integer.(<=)"         , fun2 ((<=) :: Integer -> Integer -> Bool ) )
    , ( "Float.(<=)"           , fun2 ((<=) :: Float -> Float -> Bool ) )
    , ( "Double.(<=)"          , fun2 ((<=) :: Double -> Double -> Bool ) )
    , ( "Char.(<=)"            , fun2 ((<=) :: Char -> Char -> Bool ) )
    , ( "String.(<=)"          , fun2 ((<=) :: Text -> Text -> Bool ) )
    , ( "Unit.(<=)"            , fun2 ((<=) :: () -> () -> Bool ) )

    , ( "Bool.(>)"             , fun2 ((>) :: Bool -> Bool -> Bool ) )
    , ( "Int.(>)"              , fun2 ((>) :: Int -> Int -> Bool ) )
    , ( "Integer.(>)"          , fun2 ((>) :: Integer -> Integer -> Bool ) )
    , ( "Float.(>)"            , fun2 ((>) :: Float -> Float -> Bool ) )
    , ( "Double.(>)"           , fun2 ((>) :: Double -> Double -> Bool ) )
    , ( "Char.(>)"             , fun2 ((>) :: Char -> Char -> Bool ) )
    , ( "String.(>)"           , fun2 ((>) :: Text -> Text -> Bool ) )
    , ( "Unit.(>)"             , fun2 ((>) :: () -> () -> Bool ) )

    , ( "Bool.(>=)"            , fun2 ((>=) :: Bool -> Bool -> Bool ) )
    , ( "Int.(>=)"             , fun2 ((>=) :: Int -> Int -> Bool ) )
    , ( "Integer.(>=)"         , fun2 ((>=) :: Integer -> Integer -> Bool ) )
    , ( "Float.(>=)"           , fun2 ((>=) :: Float -> Float -> Bool ) )
    , ( "Double.(>=)"          , fun2 ((>=) :: Double -> Double -> Bool ) )
    , ( "Char.(>=)"            , fun2 ((>=) :: Char -> Char -> Bool ) )
    , ( "String.(>=)"          , fun2 ((>=) :: Text -> Text -> Bool ) )
    , ( "Unit.(>=)"            , fun2 ((>=) :: () -> () -> Bool ) )

    , ( "Bool.show"            , fun1 (Text.pack . show :: Bool -> Text ) )
    , ( "Int.show"             , fun1 (Text.pack . show :: Int -> Text ) )
    , ( "Integer.show"         , fun1 (Text.pack . show :: Integer -> Text ) )
    , ( "Float.show"           , fun1 (Text.pack . show :: Float -> Text ) )
    , ( "Double.show"          , fun1 (Text.pack . show :: Double -> Text ) )
    , ( "Char.show"            , fun1 (Text.pack . show :: Char -> Text ) )
    , ( "Unit.show"            , fun1 (Text.pack . show :: () -> Text ) )
    , ( "String.show"          , fun1 (id :: Text -> Text) )

    , ( "Int.fromInteger"      , fun1 (fromInteger :: Integer -> Int) )
    , ( "Integer.fromInteger"  , fun1 (fromInteger :: Integer -> Integer) )
    , ( "Float.fromInteger"    , fun1 (fromInteger :: Integer -> Float) )
    , ( "Double.fromInteger"   , fun1 (fromInteger :: Integer -> Double) )

    , ( "Integer.fromInt"      , fun1 (fromIntegral :: Int -> Integer) )
    , ( "Integer.(%)"          , fun2 (mod :: Integer -> Integer -> Integer) )

    , ( "Float.fromDouble"     , fun1 (fromRational . toRational :: Double -> Float) )

    , ( "Bool.id"              , fun1 (id :: Bool -> Bool) )
    , ( "Int.id"               , fun1 (id :: Int -> Int) )
    , ( "Integer.id"           , fun1 (id :: Integer -> Integer) )
    , ( "Float.id"             , fun1 (id :: Float -> Float) )
    , ( "Double.id"            , fun1 (id :: Double -> Double) )
    , ( "Char.id"              , fun1 (id :: Char -> Char) )
    , ( "String.id"            , fun1 (id :: Text -> Text) )
    , ( "Unit.id"              , fun1 (id :: () -> ()) )

    , ( "String.length"        , fun1 (Text.length :: Text -> Int ) )

    , ( "(++)"                 , fun2 ((<>) :: Text -> Text -> Text ) )

    , ( "(&&)"                 , fun2 ((&&) :: Bool -> Bool -> Bool ) )
    , ( "(||)"                 , fun2 ((||) :: Bool -> Bool -> Bool ) )
    ]
