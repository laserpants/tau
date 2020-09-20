{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Env.Builtin where

import Tau.Env (Env)
import Tau.Eval
import Tau.Patterns
import Tau.Type
import Tau.Util
import Tau.Util.TH
import Tau.Value
import qualified Tau.Env as Env

maxRecord :: Int
maxRecord = 40

values :: ValueEnv Eval
values = Env.fromList $
    [ ("Some"     , dataCon "Some" 1)
    , ("None"     , dataCon "None" 0)
    , ("Succ"     , dataCon "Succ" 1)
    , ("Zero"     , dataCon "Zero" 0)
    , ("Ok"       , dataCon "Ok" 1)
    , ("Fail"     , dataCon "Fail" 1)
    , ("Mono"     , dataCon "Mono" 1)     -- TODO: remove
    ] <> 
    [("#Struct" <> intToText n, dataCon ("#Struct" <> intToText n) (n*2)) | n <- [1..maxRecord]]

typeSchemes :: Env Scheme
typeSchemes = Env.fromList $
    [ ( "Cons"     , $(parseScheme "forall a. a -> List a -> List a") )
    , ( "Nil"      , $(parseScheme "forall a. List a") )
    , ( "Some"     , $(parseScheme "forall a. a -> Option a") )
    , ( "None"     , $(parseScheme "forall a. Option a") )
    , ( "Succ"     , $(parseScheme "Nat -> Nat") )
    , ( "Zero"     , $(parseScheme "Nat") )
    , ( "Ok"       , $(parseScheme "forall a b. b -> Result a b") )
    , ( "Fail"     , $(parseScheme "forall a b. a -> Result a b") )
    , ( "#Tuple2"  , $(parseScheme "forall a b. a -> b -> #Tuple2 a b") )
    , ( "#Tuple3"  , $(parseScheme "forall a b c. a -> b -> c -> #Tuple3 a b c") )
    , ( "#Tuple4"  , $(parseScheme "forall a b c d. a -> b -> c -> d -> #Tuple4 a b c d") )
    , ( "#Tuple5"  , $(parseScheme "forall a b c d e. a -> b -> c -> d -> e -> #Tuple5 a b c d e") )
    , ( "#Tuple6"  , $(parseScheme "forall a b c d e f. a -> b -> c -> d -> e -> f -> #Tuple6 a b c d e f") )
    , ( "#Tuple7"  , $(parseScheme "forall a b c d e f g. a -> b -> c -> d -> e -> f -> g -> #Tuple7 a b c d e f g")  )
    , ( "#Tuple8"  , $(parseScheme "forall a b c d e f g h. a -> b -> c -> d -> e -> f -> g -> h -> #Tuple8 a b c d e f g h")  )
    , ( "Mono"     , $(parseScheme "forall a. a -> Mono a") )
    ] <>
    [("#Struct" <> intToText n, structScheme n) | n <- [1..maxRecord]]

constructors :: ConstructorEnv
constructors = constructorEnv $
    [ ("Nil"      , ["Nil", "Cons"])
    , ("Cons"     , ["Nil", "Cons"])
    , ("Some"     , ["Some", "None"])
    , ("None"     , ["Some", "None"])
    , ("Succ"     , ["Succ", "Zero"])
    , ("Zero"     , ["Succ", "Zero"])
    , ("Ok"       , ["Ok", "Fail"])
    , ("Fail"     , ["Ok", "Fail"])
    , ("#Tuple2"  , ["#Tuple2"])
    , ("#Tuple3"  , ["#Tuple3"])
    , ("#Tuple4"  , ["#Tuple4"])
    , ("#Tuple5"  , ["#Tuple5"])
    , ("#Tuple6"  , ["#Tuple6"])
    , ("#Tuple7"  , ["#Tuple7"])
    , ("#Tuple8"  , ["#Tuple8"])
    , ("Mono"     , ["Mono"])
    ] <> 
    [(con, [con]) | n <- [1..maxRecord], let con = "#Struct" <> intToText n]

kindEnv :: Env Kind
kindEnv = Env.fromList
    [ ( "List"    , $(parseKind "* -> *") )
    , ( "Option"  , $(parseKind "* -> *") )
    , ( "Nat"     , $(parseKind "*") )
    , ( "Result"  , $(parseKind "* -> * -> *") )
    ]

structScheme :: Int -> Scheme
structScheme n = Forall names [] (foldr arrT (foldl appT (conT con) vars) vars)
  where
    names = take (n*2) letters
    vars = varT <$> names
    con = "#Struct" <> intToText n
