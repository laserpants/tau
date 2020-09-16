{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.PatternAnomaliesCheckTests where

import Control.Monad.Reader
import Tau.Expr
import Tau.Patterns
import Tau.Util.TH
import Test.Hspec
import Utils

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Nil",  ["Nil", "Cons"])
    , ("Cons", ["Nil", "Cons"])
    ]

isExhaustive :: [Pattern] -> Bool
isExhaustive = flip runReader testConstructorEnv . exhaustive

describePatterns :: [Pattern] -> String
describePatterns patterns = 
    (if length patterns > 1 then "Patterns " else "Pattern") 
    <> concatMap (\p -> "\n      | " <> prettyString p) patterns

exhaustivePatterns :: [Pattern] -> SpecWith ()
exhaustivePatterns patterns = 
    describe (describePatterns patterns) $ 
        it ("✔ " <> (if length patterns > 1 then "are" else "is") <> " exhaustive") $
            isExhaustive patterns
            
nonExhaustivePatterns :: [Pattern] -> SpecWith ()
nonExhaustivePatterns patterns = 
    describe (describePatterns patterns) $ 
        it ("✗ " <> (if length patterns > 1 then "are" else "is") <> " not exhaustive") $
            not (isExhaustive patterns)

isUseful :: Pattern -> [Pattern] -> Bool
isUseful pat patterns = runReader (useful (fmap (:[]) patterns) [pat]) testConstructorEnv 

describeUsefulPatterns :: Pattern -> [Pattern] -> String
describeUsefulPatterns pat patterns = 
    "The pattern"
    <> "\n      | " <> prettyString pat 
    <> "\n    added to the pattern(s)" 
    <> concatMap (\p -> "\n      | " <> prettyString p) patterns

usefulPattern :: Pattern -> [Pattern] -> SpecWith ()
usefulPattern pat patterns = 
    describe (describeUsefulPatterns pat patterns) $ 
        it "✔ is useful" $
            isUseful pat patterns

notUsefulPattern :: Pattern -> [Pattern] -> SpecWith ()
notUsefulPattern pat patterns = 
    describe (describeUsefulPatterns pat patterns) $ 
        it "✗ is not useful" $
            not (isUseful pat patterns)

testPatternAnomaliesCheck :: SpecWith ()
testPatternAnomaliesCheck = do
    exhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Nil")
        , $(parsePattern "Cons z zs")
        ]

    exhaustivePatterns
        [ $(parsePattern "x :: y :: ys)")
        , $(parsePattern "[]")
        , $(parsePattern "z :: zs")
        ]

    nonExhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Cons z zs")
        ]

    nonExhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Cons z zs")
        , $(parsePattern "Cons _ _")
        ]

    exhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Cons z zs")
        , $(parsePattern "Cons _ _")
        , $(parsePattern "Nil")
        ]

    exhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Nil")
        , $(parsePattern "Cons z Nil")
        ]

    exhaustivePatterns
        [ $(parsePattern "x :: y :: ys")
        , $(parsePattern "[]")
        , $(parsePattern "[z]")
        ]

    nonExhaustivePatterns
        [ $(parsePattern "Cons x (Cons y ys)")
        , $(parsePattern "Nil")
        ]

    nonExhaustivePatterns
        [ $(parsePattern "Nil")
        ]

    exhaustivePatterns
        [ anyP
        ]

    exhaustivePatterns
        [ $(parsePattern "Cons x ys")
        , $(parsePattern "Nil")
        ]

    exhaustivePatterns
        [ $(parsePattern "Cons x ys")
        , $(parsePattern "x")
        ]

    exhaustivePatterns
        [ litP (Int 5)
        , varP "x"
        ]

    nonExhaustivePatterns
        [ litP (Int 5)
        , litP (Int 4)
        ]

    exhaustivePatterns
        [ litP (Bool True)
        , litP (Bool False)
        ]

    exhaustivePatterns
        [ litP (Bool True)
        , anyP
        ]

    nonExhaustivePatterns
        [ litP (Bool True)
        ]

    exhaustivePatterns
        [ litP Unit
        ]

    nonExhaustivePatterns
        [ litP (String "x")
        , litP (String "y")
        ]

    exhaustivePatterns
        [ litP (String "x")
        , litP (String "y")
        , anyP
        ]

    notUsefulPattern
        (conP "Nil" [])
        [ $(parsePattern "Cons x ys")
        , $(parsePattern "x")
        ]

    notUsefulPattern
        (conP "Nil" [])
        [ $(parsePattern "Cons x ys")
        , $(parsePattern "x")
        , $(parsePattern "Nil")
        ]

    usefulPattern
        (conP "Nil" [])
        [ $(parsePattern "Cons x ys")
        ]
