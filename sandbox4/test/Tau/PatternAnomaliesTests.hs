{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
module Tau.PatternAnomaliesTests where

import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Tau.Comp.Core
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Util
import Test.Hspec
import Utils
import qualified Data.Text as Text

type PatternClause = Clause (Pattern ()) (Ast () (Op1 ()) (Op2 ()))

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

-- Patterns

isExhaustive :: [[Pattern t]] -> Bool
isExhaustive = flip runReader testConstrEnv . exhaustive

patternDescription :: [[Pattern t]] -> String
patternDescription pss =
    "The patterns " <> concatMap (\ps -> "\n    | " <> Text.unpack (renderDoc (patternSeq ps))) pss

--patternSeq :: [Pattern t] -> Doc a
--patternSeq []     = ""
--patternSeq (p:ps) = foldl conArg (pretty p) ps

exhaustivePatterns :: [[Pattern t]] -> SpecWith ()
exhaustivePatterns patterns =
    describe (patternDescription patterns) $ 
        it ("✔ " <> " are exhaustive\n") (isExhaustive patterns)

nonExhaustivePatterns :: [[Pattern t]] -> SpecWith ()
nonExhaustivePatterns patterns =
    describe (patternDescription patterns) $ 
        it ("✗ " <> " are not exhaustive\n") (not (isExhaustive patterns))

-- Clauses

--isExhaustive :: [[Pattern t]] -> Bool
isExhaustive2 = flip runReader testConstrEnv . clausesAreExhaustive

--clauseDescription :: [[Pattern t]] -> String
clauseDescription cs =
    "The clauses " <> concatMap (\c -> "\n    | " <> Text.unpack (renderDoc (pretty c))) cs

--exhaustivePatterns :: [[Pattern t]] -> SpecWith ()
exhaustiveClauses clauses =
    describe (clauseDescription clauses) $ 
        it ("✔ " <> " are exhaustive\n") (isExhaustive2 clauses)

--nonExhaustiveClauses :: [[Pattern t]] -> SpecWith ()
nonExhaustiveClauses clauses =
    describe (clauseDescription clauses) $ 
        it ("✗ " <> " are not exhaustive\n") (not (isExhaustive2 clauses))

--

testPatternAnomalies :: SpecWith ()
testPatternAnomalies = do

    -- Patterns

    describe "\nPatterns\n" $ do

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

        -- Tuple patterns

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

        -- Record patterns

        nonExhaustivePatterns
            [ [recPat () (fieldSet [Field () "x" (litPat () (LInt 3)), Field () "y" (litPat () (LInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (LInt 6)), Field () "y" (litPat () (LInt 7))])]
            ]

        exhaustivePatterns
            [ [recPat () (fieldSet [Field () "x" (litPat () (LInt 3)), Field () "y" (litPat () (LInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (LInt 6)), Field () "y" (litPat () (LInt 7))])]
            , [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (litPat () (LInt 7))])]
            , [recPat () (fieldSet [Field () "x" (varPat () "x"), Field () "y" (anyPat ())])]
            ]

        exhaustivePatterns
            [ [recPat () (fieldSet [Field () "x" (anyPat ())])] ]

        exhaustivePatterns
            [ [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (varPat () "a")])] ]

        exhaustivePatterns
            [ [recPat () (fieldSet 
                  [ Field () "x" (litPat () (LInt 3))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 3))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (litPat () (LInt 6))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 4))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (anyPat ())
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 5))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (varPat () "x")
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (anyPat ())
                      ]))
                  ])]
            ]

        nonExhaustivePatterns
            [ [recPat () (fieldSet 
                  [ Field () "x" (litPat () (LInt 3))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 3))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (litPat () (LInt 6))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 4))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (anyPat ())
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 5))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (varPat () "x")
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (LInt 6))
                      ]))
                  ])]
            ]

        -- List patterns

        describe "\nList patterns\n" $ do

            nonExhaustivePatterns
                [ [lstPat () [litPat () (LInt 1), litPat () (LInt 2)]]
                ]

            nonExhaustivePatterns
                [ [lstPat () [varPat () "x", litPat () (LInt 2)]]
                ]

            exhaustivePatterns
                [ [lstPat () [varPat () "x", litPat () (LInt 2)]]
                , [anyPat ()]
                ]

            nonExhaustivePatterns
                [ [lstPat () [varPat () "x", varPat () "y"]]
                ]

            exhaustivePatterns
                [ [conPat () "[]" []]
                , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
                ]

            exhaustivePatterns
                [ [lstPat () []]
                , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
                ]

            exhaustivePatterns
                [ [lstPat () []]
                , [lstPat () [varPat () "x"]]
                , [lstPat () [varPat () "x", varPat () "y"]]
                , [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
                ]

        -- Or-patterns

        describe "\nOr-patterns\n" $ do

            nonExhaustivePatterns
                [ [litPat () (LBool False)]
                ]

            exhaustivePatterns
                [ [orPat () (litPat () (LBool False)) (litPat () (LBool True))]
                ]

        -- As-patterns

        describe "\nAs-patterns\n" $ do

            exhaustivePatterns
                [ [asPat () "cons" (conPat () "Cons" [varPat () "x", varPat () "ys"])]
                , [conPat () "Nil" []]
                ]

            nonExhaustivePatterns
                [ [asPat () "cons" (conPat () "Cons" [varPat () "x", varPat () "ys"])]
                ]

            exhaustivePatterns
                [ [asPat () "foo" (anyPat ())]
                ]

        -- Combined patterns

        describe "\nCombined patterns\n" $ do

            nonExhaustivePatterns
                [ [asPat () "x" (orPat () (litPat () (LInt 1)) (litPat () (LInt 2)))]
                ]

            exhaustivePatterns
                [ [asPat () "x" (orPat () (litPat () (LInt 1)) (litPat () (LInt 2)))]
                , [anyPat ()]
                ]

    -- Clauses

    describe "\nClauses\n" $ do

        exhaustiveClauses
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
              , Clause [varPat () "a"] [] (litExpr () (LBool False))
              ] :: [PatternClause] )

        nonExhaustiveClauses
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        nonExhaustiveClauses
            ( [ Clause [varPat () "x"] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [varPat () "x"] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [varPat () "x"] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        nonExhaustiveClauses
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [anyPat ()] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [varPat () "x"] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        nonExhaustiveClauses
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [varExpr () "aEqualsB"] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        exhaustiveClauses
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [varExpr () "aEqualsB"] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )
