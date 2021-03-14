{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.PatternAnomaliesTests where

import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Tau.Comp.Core
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Lang.Prog
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
    , ("Mono"     , ["Mono"])
    ]

class IsExhaustive a where
    isExhaustive :: (MonadReader ConstructorEnv m) => a -> m Bool
    description  :: a -> String

instance IsExhaustive [[Pattern t]] where
    isExhaustive = exhaustive
    description  = \pss -> "The patterns " <> concatMap (\ps -> "\n    | " <> showDoc (patternSeq ps)) pss

instance (Pretty a) => IsExhaustive [Clause (Pattern t) a] where
    isExhaustive = clausesAreExhaustive
    description  = \cs -> "The clauses " <> concatMap (\c -> "\n    | " <> showDoc (pretty c)) cs

instance IsExhaustive ProgExpr where
    isExhaustive = checkExhaustive
    description  = \e -> "All patterns in the expression " <> showDoc (pretty e)

showDoc :: Doc a -> String
showDoc = Text.unpack . renderDoc 

runIsExhaustive :: (IsExhaustive a) => a -> Bool
runIsExhaustive = flip runReader testConstrEnv . isExhaustive

testExhaustive :: (IsExhaustive a) => a -> SpecWith ()
testExhaustive item = do
    describe (description item) $
        it ("✔ " <> " are exhaustive\n") (runIsExhaustive item)

testNonExhaustive :: (IsExhaustive a) => a -> SpecWith ()
testNonExhaustive item =
    describe (description item) $ 
        it ("✗ " <> " are not exhaustive\n") (not (runIsExhaustive item))

testPatternAnomalies :: SpecWith ()
testPatternAnomalies = do

    -- Patterns
 
    describe "\nPatterns\n" $ do
 
        testExhaustive
            [ [] :: [Pattern t] ]

        testExhaustive
            [ [litPat () (LBool True)]
            , [litPat () (LBool False)]
            ]

        testNonExhaustive
            [ [litPat () (LBool True)]
            ]

        testExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Nil" []]
            , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
            ]

        testNonExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
            ]

        testNonExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
            , [conPat () "Cons" [anyPat (), anyPat ()]]
            ]

        testExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Cons" [varPat () "z", varPat () "zs"]]
            , [conPat () "Cons" [anyPat (), anyPat ()]]
            , [conPat () "Nil" []]
            ]

        testExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Nil" []]
            , [conPat () "Cons" [varPat () "z", conPat () "Nil" []]]
            ]

        testNonExhaustive
            [ [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]]
            , [conPat () "Nil" []]
            ]

        testNonExhaustive
            [ [conPat () "Nil" []]
            ]

        testExhaustive
            [ [anyPat ()]
            ]

        testExhaustive
            [ [conPat () "Cons" [varPat () "x", varPat () "ys"]]
            , [conPat () "Nil" []]
            ]

        testExhaustive
            [ [conPat () "Cons" [varPat () "x", varPat () "ys"]]
            , [varPat () "x"]
            ]

        testExhaustive
            [ [litPat () (LInt 5)]
            , [varPat () "x"]
            ]

        testNonExhaustive
            [ [litPat () (LInt 5)]
            , [litPat () (LInt 4)]
            ]

        testExhaustive
            [ [litPat () (LInt 5), litPat () (LInt 5)]
            , [varPat () "x", varPat () "y"]
            ]

        testNonExhaustive
            [ [litPat () (LInt 5), litPat () (LInt 5)]
            , [varPat () "x", litPat () (LInt 0)]
            ]

        testExhaustive
            [ [litPat () (LBool True)]
            , [litPat () (LBool False)]
            ]

        testExhaustive
            [ [litPat () (LBool True)]
            , [anyPat ()]
            ]

        testNonExhaustive
            [ [litPat () (LBool True)]
            ]

        testExhaustive
            [ [litPat () LUnit]
            ]

        testExhaustive
            [ [litPat () LUnit, litPat () LUnit]
            ]

        testExhaustive
            [ [litPat () LUnit, anyPat ()]
            ]

        testNonExhaustive
            [ [litPat () LUnit, litPat () (LInt 3)]
            ]

        testNonExhaustive
            [ [litPat () (LString "x")]
            , [litPat () (LString "y")]
            ]

        testExhaustive
            [ [litPat () (LString "x")]
            , [litPat () (LString "y")]
            , [anyPat ()]
            ]

        -- Tuple patterns

        testNonExhaustive
            [ [tupPat () [litPat () (LInt 1), litPat () (LInt 2)]]
            ]

        testExhaustive
            [ [tupPat () [anyPat (), anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [litPat () (LInt 1), litPat () (LInt 2)]]
            , [tupPat () [anyPat (), anyPat ()]]
            ]

        testNonExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LInt 2)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
            , [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testNonExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
            , [tupPat () [conPat () "Cons" [litPat () (LInt 3), varPat () "xs"], litPat () (LBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LBool True)]]
            , [tupPat () [conPat () "Cons" [litPat () (LInt 3), varPat () "xs"], litPat () (LBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            , [anyPat ()]
            ]

        -- Record patterns

        testNonExhaustive
            [ [recPat () (fieldSet [Field () "x" (litPat () (LInt 3)), Field () "y" (litPat () (LInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (LInt 6)), Field () "y" (litPat () (LInt 7))])]
            ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (litPat () (LInt 3)), Field () "y" (litPat () (LInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (LInt 6)), Field () "y" (litPat () (LInt 7))])]
            , [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (litPat () (LInt 7))])]
            , [recPat () (fieldSet [Field () "x" (varPat () "x"), Field () "y" (anyPat ())])]
            ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (anyPat ())])] ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (varPat () "a")])] ]

        testExhaustive
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

        testNonExhaustive
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

            testNonExhaustive
                [ [lstPat () [litPat () (LInt 1), litPat () (LInt 2)]]
                ]

            testNonExhaustive
                [ [lstPat () [varPat () "x", litPat () (LInt 2)]]
                ]

            testExhaustive
                [ [lstPat () [varPat () "x", litPat () (LInt 2)]]
                , [anyPat ()]
                ]

            testNonExhaustive
                [ [lstPat () [varPat () "x", varPat () "y"]]
                ]

            testExhaustive
                [ [conPat () "[]" []]
                , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
                ]

            testExhaustive
                [ [lstPat () []]
                , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
                ]

            testExhaustive
                [ [lstPat () []]
                , [lstPat () [varPat () "x"]]
                , [lstPat () [varPat () "x", varPat () "y"]]
                , [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
                ]

        -- Or-patterns

        describe "\nOr-patterns\n" $ do

            testNonExhaustive
                [ [litPat () (LBool False)]
                ]

            testExhaustive
                [ [orPat () (litPat () (LBool False)) (litPat () (LBool True))]
                ]

        -- As-patterns

        describe "\nAs-patterns\n" $ do

            testExhaustive
                [ [asPat () "cons" (conPat () "Cons" [varPat () "x", varPat () "ys"])]
                , [conPat () "Nil" []]
                ]

            testNonExhaustive
                [ [asPat () "cons" (conPat () "Cons" [varPat () "x", varPat () "ys"])]
                ]

            testExhaustive
                [ [asPat () "foo" (anyPat ())]
                ]

        -- Combined patterns

        describe "\nCombined patterns\n" $ do

            testNonExhaustive
                [ [asPat () "x" (orPat () (litPat () (LInt 1)) (litPat () (LInt 2)))]
                ]

            testExhaustive
                [ [asPat () "x" (orPat () (litPat () (LInt 1)) (litPat () (LInt 2)))]
                , [anyPat ()]
                ]

    -- Clauses

    describe "\nClauses\n" $ do

        testExhaustive
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
              , Clause [varPat () "a"] [] (litExpr () (LBool False))
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [varPat () "x"] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [varPat () "x"] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [varPat () "x"] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [litPat () (LString "y")] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [anyPat ()] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (LString "x")] [] (litExpr () (LBool True))
              , Clause [anyPat ()] [varExpr () "pIsTrue"] (litExpr () (LBool True))
              , Clause [varPat () "x"] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [varExpr () "aEqualsB"] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [varExpr () "aEqualsB"] (litExpr () (LBool True))
              , Clause [conPat () "Nil" []] [] (litExpr () (LBool True))
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
              ] :: [PatternClause] )

    -- Expressions

    describe "\nExpressions\n" $ do

        testExhaustive 
            (letExpr () (BLet (varPat () "y")) (litExpr () (LInt 5)) (varExpr () "z") :: ProgExpr)

        testExhaustive 
            (letExpr () (BLet (conPat () "Mono" [varPat () "y"])) (conExpr () "Mono" [litExpr () (LInt 5)]) (varExpr () "y") :: ProgExpr)

        testExhaustive 
            (letExpr () (BLet (tupPat () [varPat () "x", varPat () "y"])) (tupExpr () [litExpr () (LInt 1), litExpr () (LInt 2)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (letExpr () (BLet (tupPat () [varPat () "x", litPat () (LInt 3)])) (tupExpr () [litExpr () (LInt 1), litExpr () (LInt 2)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (letExpr () (BLet (conPat () "Some" [varPat () "y"])) (conExpr () "Some" [litExpr () (LInt 5)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (lamExpr () [conPat () "Some" [varPat () "y"]] (varExpr () "y") :: ProgExpr)

        testExhaustive 
            (lamExpr () [conPat () "Mono" [varPat () "y"]] (varExpr () "y") :: ProgExpr)

        testNonExhaustive
            (lamExpr () [conPat () "Mono" [varPat () "x", varPat () "y"]] (
                patExpr () [varExpr () "x", varExpr () "y"] 
                    [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [] (litExpr () (LBool True))
                    , Clause [conPat () "Nil" []] [varExpr () "aEqualsB"] (litExpr () (LBool True))
                    , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [] (litExpr () (LBool True))
                    ]) :: ProgExpr)
