{-# LANGUAGE OverloadedStrings #-}
module Tau.PatternAnomaliesTests where

import Control.Monad.Reader
import Tau.Comp.Core
import Tau.Lang.Expr
import Test.Hspec
import Utils

testConstrEnv :: ConstructorEnv
testConstrEnv = constructorEnv
    [ ("Nil"      , ["Nil", "Cons"])
    , ("Cons"     , ["Nil", "Cons"])
    , ("Some"     , ["Some", "None"])
    , ("None"     , ["Some", "None"])
    , ("Succ"     , ["Succ", "Zero"])
    , ("Zero"     , ["Succ", "Zero"])
    , ("Ok"       , ["Ok", "Fail"])
    , ("Fail"     , ["Ok", "Fail"])
    ]

isExhaustive :: [[Pattern t]] -> Bool
isExhaustive = flip runReader testConstrEnv . exhaustive

patternDescription :: [[Pattern t]] -> String
patternDescription patterns =
    "Patterns " <> concatMap (\p -> "\n      | " <> prettyString p) patterns

exhaustivePatterns :: [[Pattern t]] -> SpecWith ()
exhaustivePatterns patterns =
    describe (patternDescription patterns) $ 
        it ("✔ " <> " are exhaustive") (isExhaustive patterns)
            
nonExhaustivePatterns :: [[Pattern t]] -> SpecWith ()
nonExhaustivePatterns patterns =
    describe (patternDescription patterns) $ 
        it ("✗ " <> " are not exhaustive") (not (isExhaustive patterns))

testPatternAnomalies :: SpecWith ()
testPatternAnomalies = do

    exhaustivePatterns
        [ [] ]

    exhaustivePatterns
        [ [litPat () (LBool True)]
        , [litPat () (LBool False)]
        ]

    nonExhaustivePatterns
        [ [litPat () (LBool True)]
        ]

    exhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Nil" []]
        , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
        ]

    nonExhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
        ]

    nonExhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
        , [conPat () "Cons" [anyPat (), anyPat ()]]
        ]

    exhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
        , [conPat () "Cons" [anyPat (), anyPat ()]]
        , [conPat () "Nil" []]
        ]

    exhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Nil" []]
        , [conPat () "Cons" [varPat () "z", conPat () "Nil" []]]
        ]

    nonExhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
        , [conPat () "Nil" []]
        ]

    nonExhaustivePatterns
        [ [conPat () "Nil" []]
        ]

    exhaustivePatterns
        [ [anyPat ()]
        ]

    exhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", varPat () "ys"]]
        , [conPat () "Nil" []]
        ]

    exhaustivePatterns
        [ [conPat () "Cons" [varPat () "x", varPat () "ys"]]
        , [varPat () "x"]
        ]

    exhaustivePatterns
        [ [litPat () (LInt 5)]
        , [varPat () "x"]
        ]

    nonExhaustivePatterns
        [ [litPat () (LInt 5)]
        , [litPat () (LInt 4)]
        ]

    exhaustivePatterns
        [ [litPat () (LInt 5), litPat () (LInt 5)]
        , [varPat () "x", varPat () "y"]
        ]

    nonExhaustivePatterns
        [ [litPat () (LInt 5), litPat () (LInt 5)]
        , [varPat () "x", litPat () (LInt 0)]
        ]

    exhaustivePatterns
        [ [litPat () (LBool True)]
        , [litPat () (LBool False)]
        ]

    exhaustivePatterns
        [ [litPat () (LBool True)]
        , [anyPat ()]
        ]

    nonExhaustivePatterns
        [ [litPat () (LBool True)]
        ]

    exhaustivePatterns
        [ [litPat () LUnit]
        ]

    exhaustivePatterns
        [ [litPat () LUnit, litPat () LUnit]
        ]

    exhaustivePatterns
        [ [litPat () LUnit, anyPat ()]
        ]

    nonExhaustivePatterns
        [ [litPat () LUnit, litPat () (LInt 3)]
        ]

    nonExhaustivePatterns
        [ [litPat () (LString "x")]
        , [litPat () (LString "y")]
        ]

    exhaustivePatterns
        [ [litPat () (LString "x")]
        , [litPat () (LString "y")]
        , [anyPat ()]
        ]

    nonExhaustivePatterns
        [ [tupPat () [litPat () (LInt 1), litPat () (LInt 2)]]
        ]

    exhaustivePatterns
        [ [tupPat () [anyPat (), anyPat ()]]
        ]

    exhaustivePatterns
        [ [tupPat () [litPat () (LInt 1), litPat () (LInt 2)]]
        , [tupPat () [anyPat (), anyPat ()]]
        ]

    nonExhaustivePatterns
        [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LInt 2)]]
        , [tupPat () [conPat () "Nil" [], anyPat ()]]
        ]

    exhaustivePatterns
        [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
        , [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool False)]]
        , [tupPat () [conPat () "Nil" [], anyPat ()]]
        ]

    nonExhaustivePatterns
        [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
        , [tupPat () [conPat () "Cons" [litPat () (LInt 3), varPat () "xs"], litPat () (LBool False)]]
        , [tupPat () [conPat () "Nil" [], anyPat ()]]
        ]

    exhaustivePatterns
        [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
        , [tupPat () [conPat () "Cons" [litPat () (LInt 3), varPat () "xs"], litPat () (LBool False)]]
        , [tupPat () [conPat () "Nil" [], anyPat ()]]
        , [anyPat ()]
        ]

--    nonExhaustivePatterns
--        [ $(parsePattern "{ x = 3, y = 4 }")
--        , $(parsePattern "{ x = 6, y = 7 }")
--        ]
--
--    exhaustivePatterns
--        [ $(parsePattern "{ x = 3, y = 4 }")
--        , $(parsePattern "{ x = 6, y = 7 }")
--        , $(parsePattern "{ x = _, y = 7 }")
--        , $(parsePattern "{ x = x, y = _ }")
--        ]
--
--    exhaustivePatterns
--        [ $(parsePattern "{ x = _ }")
--        ]
--
--    exhaustivePatterns
--        [ $(parsePattern "{ x = _, y = a }")
--        ]
--
--    exhaustivePatterns
--        [ $(parsePattern "{ a = x }")
--        ]
--
--    exhaustivePatterns
--        [ $(parsePattern "{ x = 3, y = { a = 3 } }")
--        , $(parsePattern "{ x = 6, y = { a = 4 } }")
--        , $(parsePattern "{ x = _, y = { a = 5 } }")
--        , $(parsePattern "{ x = x, y = { a = _ } }")
--        ]
--
--    nonExhaustivePatterns
--        [ $(parsePattern "{ x = 3, y = { a = 3 } }")
--        , $(parsePattern "{ x = 6, y = { a = 4 } }")
--        , $(parsePattern "{ x = _, y = { a = 5 } }")
--        , $(parsePattern "{ x = x, y = { a = 6 } }")
--        ]

-- Or-patterns

-- As-patterns

