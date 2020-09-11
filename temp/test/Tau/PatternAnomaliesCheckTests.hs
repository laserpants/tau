{-# LANGUAGE OverloadedStrings #-}
module Tau.PatternAnomaliesCheckTests where

import Control.Monad.Reader
import Test.Hspec
import Tau.Expr
import Tau.Patterns
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
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Nil" []
        , conP "Cons" [varP "z", varP "zs"]
        ]

    nonExhaustivePatterns
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Cons" [varP "z", varP "zs"]
        ]

    nonExhaustivePatterns
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Cons" [varP "z", varP "zs"]
        , conP "Cons" [anyP, anyP]
        ]

    exhaustivePatterns
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Cons" [varP "z", varP "zs"]
        , conP "Cons" [anyP, anyP]
        , conP "Nil" []
        ]

    exhaustivePatterns
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Nil" []
        , conP "Cons" [varP "z", conP "Nil" []]
        ]

    nonExhaustivePatterns
        [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
        , conP "Nil" []
        ]

    nonExhaustivePatterns
        [ conP "Nil" []
        ]

    exhaustivePatterns
        [ anyP
        ]

    exhaustivePatterns
        [ conP "Cons" [varP "x", varP "ys"]
        , conP "Nil" []
        ]

    exhaustivePatterns
        [ conP "Cons" [varP "x", varP "ys"]
        , varP "x"
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
        [ conP "Cons" [varP "x", varP "ys"]
        , varP "x" 
        ]

    notUsefulPattern
        (conP "Nil" [])
        [ conP "Cons" [varP "x", varP "ys"]
        , varP "x"
        , conP "Nil" [] 
        ]

    usefulPattern
        (conP "Nil" [])
        [ conP "Cons" [varP "x", varP "ys"]
        ]
