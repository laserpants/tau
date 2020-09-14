{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.PatternAnomaliesCheckTests where

import Control.Monad.Reader
import TH
import Tau.Expr
import Tau.Patterns
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
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Nil")
        , $(mkPattern "Cons z zs")
        ]

    nonExhaustivePatterns
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Cons z zs")
        ]

    nonExhaustivePatterns
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Cons z zs")
        , $(mkPattern "Cons _ _")
        ]

    exhaustivePatterns
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Cons z zs")
        , $(mkPattern "Cons _ _")
        , $(mkPattern "Nil")
        ]

    exhaustivePatterns
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Nil")
        , $(mkPattern "Cons z Nil")
        ]

    nonExhaustivePatterns
        [ $(mkPattern "Cons x (Cons y ys)")
        , $(mkPattern "Nil")
        ]

    nonExhaustivePatterns
        [ $(mkPattern "Nil")
        ]

    exhaustivePatterns
        [ anyP
        ]

    exhaustivePatterns
        [ $(mkPattern "Cons x ys")
        , $(mkPattern "Nil")
        ]

    exhaustivePatterns
        [ $(mkPattern "Cons x ys")
        , $(mkPattern "x")
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
        [ $(mkPattern "Cons x ys")
        , $(mkPattern "x")
        ]

    notUsefulPattern
        (conP "Nil" [])
        [ $(mkPattern "Cons x ys")
        , $(mkPattern "x")
        , $(mkPattern "Nil")
        ]

    usefulPattern
        (conP "Nil" [])
        [ $(mkPattern "Cons x ys")
        ]
