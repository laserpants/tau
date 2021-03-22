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

type PatternClause = Clause (Pattern () () ()) ProgExpr

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
    , ("Id"       , ["Id"])
    ]

class IsExhaustive a where
    isExhaustive :: (MonadReader ConstructorEnv m) => a -> m Bool
    description  :: a -> String

instance IsExhaustive [[Pattern t f g]] where
    isExhaustive = exhaustive
    description  = \pss -> "The patterns " <> concatMap (\ps -> "\n    | " <> showDoc (patternSeq ps)) pss

instance IsExhaustive [PatternClause] where
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
            [ [] :: [Pattern t f g] ]

        testExhaustive
            [ [litPat () (TBool True)]
            , [litPat () (TBool False)]
            ]

        testNonExhaustive
            [ [litPat () (TBool True)]
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
            [ [litPat () (TInt 5)]
            , [varPat () "x"]
            ]

        testNonExhaustive
            [ [litPat () (TInt 5)]
            , [litPat () (TInt 4)]
            ]

        testExhaustive
            [ [litPat () (TInt 5), litPat () (TInt 5)]
            , [varPat () "x", varPat () "y"]
            ]

        testNonExhaustive
            [ [litPat () (TInt 5), litPat () (TInt 5)]
            , [varPat () "x", litPat () (TInt 0)]
            ]

        testExhaustive
            [ [litPat () (TBool True)]
            , [litPat () (TBool False)]
            ]

        testExhaustive
            [ [litPat () (TBool True)]
            , [anyPat ()]
            ]

        testNonExhaustive
            [ [litPat () (TBool True)]
            ]

        testExhaustive
            [ [litPat () TUnit]
            ]

        testExhaustive
            [ [litPat () TUnit, litPat () TUnit]
            ]

        testExhaustive
            [ [litPat () TUnit, anyPat ()]
            ]

        testNonExhaustive
            [ [litPat () TUnit, litPat () (TInt 3)]
            ]

        testNonExhaustive
            [ [litPat () (TString "x")]
            , [litPat () (TString "y")]
            ]

        testExhaustive
            [ [litPat () (TString "x")]
            , [litPat () (TString "y")]
            , [anyPat ()]
            ]

        -- Tuple patterns

        testNonExhaustive
            [ [tupPat () [litPat () (TInt 1), litPat () (TInt 2)]]
            ]

        testExhaustive
            [ [tupPat () [anyPat (), anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [litPat () (TInt 1), litPat () (TInt 2)]]
            , [tupPat () [anyPat (), anyPat ()]]
            ]

        testNonExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (TInt 2)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (TBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testNonExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tupPat () [conPat () "Cons" [litPat () (TInt 3), varPat () "xs"], litPat () (TBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            ]

        testExhaustive
            [ [tupPat () [conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tupPat () [conPat () "Cons" [litPat () (TInt 3), varPat () "xs"], litPat () (TBool False)]]
            , [tupPat () [conPat () "Nil" [], anyPat ()]]
            , [anyPat ()]
            ]

        -- Record patterns

        testNonExhaustive
            [ [recPat () (fieldSet [Field () "x" (litPat () (TInt 3)), Field () "y" (litPat () (TInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (TInt 6)), Field () "y" (litPat () (TInt 7))])]
            ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (litPat () (TInt 3)), Field () "y" (litPat () (TInt 4))])]
            , [recPat () (fieldSet [Field () "x" (litPat () (TInt 6)), Field () "y" (litPat () (TInt 7))])]
            , [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (litPat () (TInt 7))])]
            , [recPat () (fieldSet [Field () "x" (varPat () "x"), Field () "y" (anyPat ())])]
            ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (anyPat ())])] ]

        testExhaustive
            [ [recPat () (fieldSet [Field () "x" (anyPat ()), Field () "y" (varPat () "a")])] ]

        testExhaustive
            [ [recPat () (fieldSet 
                  [ Field () "x" (litPat () (TInt 3))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 3))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (litPat () (TInt 6))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 4))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (anyPat ())
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 5))
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
                  [ Field () "x" (litPat () (TInt 3))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 3))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (litPat () (TInt 6))
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 4))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (anyPat ())
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 5))
                      ]))
                  ])]
            , [recPat () (fieldSet 
                  [ Field () "x" (varPat () "x")
                  , Field () "y" (recPat () (fieldSet 
                      [ Field () "a" (litPat () (TInt 6))
                      ]))
                  ])]
            ]

        -- List patterns

        describe "\nList patterns\n" $ do

            testNonExhaustive
                [ [lstPat () [litPat () (TInt 1), litPat () (TInt 2)]]
                ]

            testNonExhaustive
                [ [lstPat () [varPat () "x", litPat () (TInt 2)]]
                ]

            testExhaustive
                [ [lstPat () [varPat () "x", litPat () (TInt 2)]]
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
                [ [litPat () (TBool False)]
                ]

            testExhaustive
                [ [orPat () (litPat () (TBool False)) (litPat () (TBool True))]
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
                [ [asPat () "x" (orPat () (litPat () (TInt 1)) (litPat () (TInt 2)))]
                ]

            testExhaustive
                [ [asPat () "x" (orPat () (litPat () (TInt 1)) (litPat () (TInt 2)))]
                , [anyPat ()]
                ]

    -- Clauses

    describe "\nClauses\n" $ do

        testExhaustive
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
              , Clause [varPat () "a"] [Guard [] (litExpr () (TBool False))]
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [varPat () "x"] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [varPat () "x"] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
              , Clause [varPat () "x"] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
              , Clause [litPat () (TString "y")] [Guard [] (litExpr () (TBool True))]
              , Clause [anyPat ()] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
              , Clause [litPat () (TString "y")] [Guard [] (litExpr () (TBool True))]
              , Clause [anyPat ()] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
              , Clause [litPat () (TString "y")] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
              , Clause [anyPat ()] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
              , Clause [anyPat ()] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
              , Clause [varPat () "x"] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
              , Clause [conPat () "Nil" []] [Guard [] (litExpr () (TBool True))]
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testNonExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
              , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        testExhaustive
            ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
              , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
              , Clause [conPat () "Nil" []] [Guard [] (litExpr () (TBool True))]
              , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
              ] :: [PatternClause] )

        --
        --    | (x :: xs)
        --      when x > 3 => 0
        --      when x < 3 => 1
        --      otherwise  => 2
        --      
        testNonExhaustive
            ( [ Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
                  , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
                  , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
                  ]
              ] :: [PatternClause] )

        --
        --    | x
        --      when x > 3 => 0
        --      when x < 3 => 1
        --      otherwise  => 2
        --      
        testExhaustive
            ( [ Clause [varPat () "x"] 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
                  , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
                  , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
                  ]
              ] :: [PatternClause] )

        --
        --    | (x :: xs)
        --      when x > 3 => 0
        --      when x < 3 => 1
        --      otherwise  => 2
        --    | []         => 5
        --      
        testExhaustive
            ( [ Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
                  , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
                  , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
                  ]
              , Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 5))]
              ] :: [PatternClause] )

    -- Expressions

    describe "\nExpressions\n" $ do

        testExhaustive 
            (letExpr () (BLet (varPat () "y")) (litExpr () (TInt 5)) (varExpr () "z") :: ProgExpr)

        testExhaustive 
            (letExpr () (BLet (conPat () "Id" [varPat () "y"])) (conExpr () "Id" [litExpr () (TInt 5)]) (varExpr () "y") :: ProgExpr)

        testExhaustive 
            (letExpr () (BLet (tupPat () [varPat () "x", varPat () "y"])) (tupExpr () [litExpr () (TInt 1), litExpr () (TInt 2)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (letExpr () (BLet (tupPat () [varPat () "x", litPat () (TInt 3)])) (tupExpr () [litExpr () (TInt 1), litExpr () (TInt 2)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (letExpr () (BLet (conPat () "Some" [varPat () "y"])) (conExpr () "Some" [litExpr () (TInt 5)]) (varExpr () "y") :: ProgExpr)

        testNonExhaustive 
            (lamExpr () [conPat () "Some" [varPat () "y"]] (varExpr () "y") :: ProgExpr)

        testExhaustive 
            (lamExpr () [conPat () "Id" [varPat () "y"]] (varExpr () "y") :: ProgExpr)

        testNonExhaustive
            (lamExpr () [conPat () "Id" [varPat () "x", varPat () "y"]] (
                patExpr () [varExpr () "x", varExpr () "y"] 
                    [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
                    , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
                    , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
                    ]) :: ProgExpr)
