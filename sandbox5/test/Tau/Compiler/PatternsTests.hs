{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.PatternsTests where

import Control.Monad.Reader
import Tau.Lang
import Tau.Compiler.Patterns
import Tau.Pretty
import Tau.Prog
import Tau.Tooling
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    , ("#"        , ( ["#"], 1 ))
    , ("{}"       , ( ["{}"], 0 ))
    ]

runPatterns :: Reader ConstructorEnv a -> a
runPatterns = flip runReader testConstructorEnv 

patternsAreExhaustive :: (Show t, RowType t) => [[ProgPattern t]] -> SpecWith ()
patternsAreExhaustive pss = 
    describe ("The patterns " <> prettyPrint pss) $
        it "✔ are exhaustive" $ runPatterns (exhaustive pss)

patternsAreNotExhaustive :: (Show t, RowType t) => [[ProgPattern t]] -> SpecWith ()
patternsAreNotExhaustive pss = 
    describe ("The patterns " <> prettyPrint pss) $
        it "✗ are not exhaustive" $ not (runPatterns (exhaustive pss))

testPatterns :: SpecWith ()
testPatterns = do

    patternsAreExhaustive 
        [ [] :: [ProgPattern ()]
        ] 

    patternsAreExhaustive 
        [ [litPat () (TBool True)]
        , [litPat () (TBool False)] 
        ]

    patternsAreNotExhaustive
        [ [litPat () (TBool True)]
        ]

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "[]" []]
        , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
        ] 

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "[]" []]
        , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
        ]

    patternsAreNotExhaustive
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
        ]

    patternsAreNotExhaustive
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
        , [conPat () "(::)" [anyPat (), anyPat ()]]
        ]

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
        , [conPat () "(::)" [anyPat (), anyPat ()]]
        , [conPat () "[]" []]
        ]

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "[]" []]
        , [conPat () "(::)" [varPat () "z", conPat () "[]" []]]
        ]

    patternsAreNotExhaustive
        [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
        , [conPat () "[]" []]
        ]

    patternsAreNotExhaustive
        [ [conPat () "[]" []]
        ]

    patternsAreExhaustive 
        [ [anyPat ()]
        ]

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", varPat () "ys"]]
        , [conPat () "[]" []]
        ]

    patternsAreExhaustive 
        [ [conPat () "(::)" [varPat () "x", varPat () "ys"]]
        , [varPat () "x"]
        ]

    patternsAreExhaustive 
        [ [litPat () (TInt 5)]
        , [varPat () "x"]
        ]

    patternsAreNotExhaustive
        [ [litPat () (TInt 5)]
        , [litPat () (TInt 4)]
        ]

    patternsAreExhaustive 
        [ [litPat () (TInt 5), litPat () (TInt 5)]
        , [varPat () "x", varPat () "y"]
        ]

    patternsAreNotExhaustive
        [ [litPat () (TInt 5), litPat () (TInt 5)]
        , [varPat () "x", litPat () (TInt 0)]
        ]

    patternsAreExhaustive 
        [ [litPat () (TBool True)]
        , [litPat () (TBool False)]
        ]

    patternsAreExhaustive 
        [ [litPat () (TBool True)]
        , [anyPat ()]
        ]

    patternsAreNotExhaustive
        [ [litPat () (TBool True)]
        ]

    patternsAreExhaustive
        [ [litPat () TUnit]
        ]

    patternsAreExhaustive
        [ [litPat () TUnit, litPat () TUnit]
        ]

    patternsAreExhaustive
        [ [litPat () TUnit, anyPat ()]
        ]

    patternsAreNotExhaustive
        [ [litPat () TUnit, litPat () (TInt 3)]
        ]

    patternsAreNotExhaustive
        [ [litPat () (TString "x")]
        , [litPat () (TString "y")]
        ]

    patternsAreExhaustive
        [ [litPat () (TString "x")]
        , [litPat () (TString "y")]
        , [anyPat ()]
        ]

    -- Tuple patterns

    describe "Tuple patterns" $ do

        patternsAreNotExhaustive
            [ [tuplePat () [litPat () (TInt 1), litPat () (TInt 2)]]
            ]

        patternsAreExhaustive
            [ [tuplePat () [anyPat (), anyPat ()]]
            ]

        patternsAreExhaustive
            [ [tuplePat () [litPat () (TInt 1), litPat () (TInt 2)]]
            , [tuplePat () [anyPat (), anyPat ()]]
            ]

        patternsAreNotExhaustive
            [ [tuplePat () [conPat () "(::)" [varPat () "x", varPat () "xs"], litPat () (TInt 2)]]
            , [tuplePat () [conPat () "[]" [], anyPat ()]]
            ]

        patternsAreExhaustive
            [ [tuplePat () [conPat () "(::)" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tuplePat () [conPat () "(::)" [varPat () "x", varPat () "xs"], litPat () (TBool False)]]
            , [tuplePat () [conPat () "[]" [], anyPat ()]]
            ]

        patternsAreNotExhaustive
            [ [tuplePat () [conPat () "(::)" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tuplePat () [conPat () "(::)" [litPat () (TInt 3), varPat () "xs"], litPat () (TBool False)]]
            , [tuplePat () [conPat () "[]" [], anyPat ()]]
            ]

        patternsAreExhaustive
            [ [tuplePat () [conPat () "(::)" [varPat () "x", varPat () "xs"], litPat () (TBool True)]]
            , [tuplePat () [conPat () "(::)" [litPat () (TInt 3), varPat () "xs"], litPat () (TBool False)]]
            , [tuplePat () [conPat () "[]" [], anyPat ()]]
            , [anyPat ()]
            ]

        -- (x, (y, z))
        patternsAreExhaustive
            [ [tuplePat () [varPat () "x", tuplePat () [varPat () "y", varPat () "z"]]]
            ]

     -- List patterns

    describe "List patterns" $ do

        patternsAreNotExhaustive
            [ [listPat () [litPat () (TInt 1), litPat () (TInt 2)]]
            ]

        patternsAreNotExhaustive
            [ [listPat () [varPat () "x", litPat () (TInt 2)]]
            ]

        patternsAreExhaustive
            [ [listPat () [varPat () "x", litPat () (TInt 2)]]
            , [anyPat ()]
            ]

        patternsAreNotExhaustive
            [ [listPat () [varPat () "x", varPat () "y"]]
            ]

        patternsAreExhaustive
            [ [conPat () "[]" []]
            , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
            ]

        patternsAreExhaustive
            [ [listPat () []]
            , [conPat () "(::)" [varPat () "x", varPat () "xs"]]
            ]

        patternsAreExhaustive
            [ [listPat () []]
            , [listPat () [varPat () "x"]]
            , [listPat () [varPat () "x", varPat () "y"]]
            , [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
            ]

     -- Or-patterns

    describe "Or-patterns" $ do

        patternsAreNotExhaustive
            [ [litPat () (TBool False)]
            ]

        patternsAreExhaustive
            [ [orPat () (litPat () (TBool False)) (litPat () (TBool True))]
            ]

     -- As-patterns

    describe "As-patterns" $ do

        patternsAreExhaustive
            [ [asPat () "cons" (conPat () "(::)" [varPat () "x", varPat () "ys"])]
            , [conPat () "[]" []]
            ]

        patternsAreNotExhaustive
            [ [asPat () "cons" (conPat () "(::)" [varPat () "x", varPat () "ys"])]
            ]

        patternsAreExhaustive
            [ [asPat () "foo" (anyPat ())]
            ]

    -- Combined patterns

    describe "Combined patterns" $ do

        patternsAreNotExhaustive
            [ [asPat () "x" (orPat () (litPat () (TInt 1)) (litPat () (TInt 2)))]
            ]

        patternsAreExhaustive
            [ [asPat () "x" (orPat () (litPat () (TInt 1)) (litPat () (TInt 2)))]
            , [anyPat ()]
            ]

    -- Record patterns

    describe "Record patterns" $ do

        patternsAreNotExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TInt 3)) (rowPat () "y" (litPat () (TInt 4)) (conPat () "{}" [])))]
            , [recordPat () (rowPat () "x" (litPat () (TInt 6)) (rowPat () "y" (litPat () (TInt 7)) (conPat () "{}" [])))]
            ]
 
        -- { x = x | {} }
        patternsAreExhaustive
            [ [rowPat () "x" (varPat () "x") (conPat () "{}" [])]
            ]

        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TInt 3)) (rowPat () "y" (litPat () (TInt 4)) (conPat () "{}" [])))]
            , [recordPat () (rowPat () "x" (litPat () (TInt 6)) (rowPat () "y" (litPat () (TInt 7)) (conPat () "{}" [])))]
            , [recordPat () (rowPat () "x" (anyPat ()) (rowPat () "y" (litPat () (TInt 7)) (conPat () "{}" [])))]
            , [recordPat () (rowPat () "x" (varPat () "x") (rowPat () "y" (anyPat ()) (conPat () "{}" [])))]
            ]

        -- { x = _ | {} }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (anyPat ()) (conPat () "{}" []))]
            ]

        -- { x = _, y = a | {} }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (anyPat ()) (rowPat () "y" (varPat () "a") (conPat () "{}" [])))] 
            ]

        -- | { x = 3, y = { a = 3 | {} } | {} }
        -- | { x = 6, y = { a = 4 | {} } | {} }
        -- | { x = _, y = { a = 5 | {} } | {} }
        -- | { x = x, y = { a = _ | {} } | {} }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TInt 3)) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 3)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TInt 6)) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 4)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (anyPat ()) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 5)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (varPat () "x") (rowPat () "y" (recordPat () (rowPat () "a" (anyPat ()) (conPat () "{}" []))) (conPat () "{}" [])))] 
            ]

        -- | { x = False, y = False | {} }
        -- | { x = False, y = True | {} }
        -- | { x = True, y = False | {} }
        -- | { x = True, y = True | {} }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool True)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool True)) (conPat () "{}" [])))] 
            ]

        -- (False, False)
        -- (False, True)
        -- (True, False)
        -- (True, True)
        patternsAreExhaustive
            [ [tuplePat () [litPat () (TBool False), litPat () (TBool False)]]
            , [tuplePat () [litPat () (TBool False), litPat () (TBool True)]]
            , [tuplePat () [litPat () (TBool True), litPat () (TBool False)]]
            , [tuplePat () [litPat () (TBool True), litPat () (TBool True)]]
            ]

        -- | { x = False, y = False | {} }
        -- | { x = True, y = False | {} }
        patternsAreNotExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            ]

        -- (False, False)
        -- (True, False)
        patternsAreNotExhaustive
            [ [tuplePat () [litPat () (TBool False), litPat () (TBool False)]]
            , [tuplePat () [litPat () (TBool True), litPat () (TBool False)]]
            ]

        -- | { x = False, y = False | {} }
        -- | { x = False, y = True | {} }
        -- | { x = True, y = False | {} }
        patternsAreNotExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool True)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            ]

        -- (False, False)
        -- (False, True)
        -- (True, False)
        patternsAreNotExhaustive
            [ [tuplePat () [litPat () (TBool False), litPat () (TBool False)]]
            , [tuplePat () [litPat () (TBool False), litPat () (TBool True)]]
            , [tuplePat () [litPat () (TBool True), litPat () (TBool False)]]
            ]

        patternsAreNotExhaustive
            [ [litPat () (TBool False), litPat () (TBool False)]
            , [litPat () (TBool False), litPat () (TBool True)]
            , [litPat () (TBool True), litPat () (TBool False)]
            ]

        patternsAreNotExhaustive
            [ [conPat () "#False" [], conPat () "#False" []]
            , [conPat () "#False" [], conPat () "#True" []]
            , [conPat () "#True" [], conPat () "#False" []]
            ]

        patternsAreExhaustive
            [ [conPat () "#False" []]
            , [conPat () "#True" []]
            ]

        patternsAreExhaustive
            [ [tuplePat () [conPat () "#False" [], conPat () "#False" []]]
            , [tuplePat () [conPat () "#False" [], conPat () "#True" []]]
            , [tuplePat () [conPat () "#True" [], conPat () "#False" []]]
            , [tuplePat () [conPat () "#True" [], conPat () "#True" []]]
            ]

        patternsAreNotExhaustive
            [ [tuplePat () [conPat () "#False" [], conPat () "#False" []]]
            , [tuplePat () [conPat () "#False" [], conPat () "#True" []]]
            , [tuplePat () [conPat () "#True" [], conPat () "#False" []]]
            ]



        -- | { x = False, y = False | {} }
        -- | { y = True, x = False | {} }
        -- | { x = True, y = False | {} }
        -- | { x = True, y = True | {} }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "y" (litPat () (TBool True)) (rowPat () "x" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool False)) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (litPat () (TBool True)) (conPat () "{}" [])))] 
            ]

        -- | { x = False, y = { z = False, a = False }| {} }
        -- | { x = False, y = { z = False, a = True }| {} }
        -- | { x = False, y = { z = True , a = False }| {} }
        -- | { x = False, y = { z = True , a = True }| {} }
        -- | { x = True, y = { z = False, a = False }| {} }
        -- | { x = True, y = { z = False, a = True }| {} }
        -- | { x = True, y = { z = True , a = False }| {} }
        -- | { x = True, y = { z = True , a = True }| {} }

        patternsAreExhaustive
            [ [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            ]

--        patternsAreExhaustive
--            [ [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            , [recordPat () (rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" [])))] 
--            ]


        -- | { x = 3, y = { a = 3 | {} } | {} }
        -- | { x = 6, y = { a = 4 | {} } | {} }
        -- | { x = _, y = { a = 5 | {} } | {} }
        -- | { x = x, y = { a = 6 | {} } | {} }
        patternsAreNotExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TInt 3)) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 3)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (litPat () (TInt 6)) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 4)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (anyPat ()) (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 5)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            , [recordPat () (rowPat () "x" (varPat () "x") (rowPat () "y" (recordPat () (rowPat () "a" (litPat () (TInt 6)) (conPat () "{}" []))) (conPat () "{}" [])))] 
            ]

        -- | { x = x | r }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (varPat () "x") (varPat () "r"))] 
            ]

        -- | { x = 1 | r }
        patternsAreNotExhaustive
            [ [recordPat () (rowPat () "x" (litPat () (TInt 1)) (varPat () "r"))] 
            ]

        -- | { x = () | r }
        patternsAreExhaustive
            [ [recordPat () (rowPat () "x" (litPat () TUnit) (varPat () "r"))] 
            ]




-- test35b = runReader (clausesAreExhaustive
--     [ Clause () (conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]) []
--     , Clause () (conPat () "[]" []) []
--     , Clause () (conPat () "(::)" [varPat () "z", varPat () "zs"]) []
--     ])
--     testConstructorEnv 
-- 
-- test35c = runReader (checkExhaustive (
--     patExpr () (varExpr () "x")
--         [ Clause () (conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]) []
--         , Clause () (conPat () "[]" []) []
--         , Clause () (conPat () "(::)" [varPat () "z", varPat () "zs"]) []
--         ]))
--     testConstructorEnv 
-- 
-- 
-- -- False
-- test36b = runReader (clausesAreExhaustive
--     [ Clause () (conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]) []
--     , Clause () (conPat () "(::)" [varPat () "z", varPat () "zs"]) []
--     ])
--     testConstructorEnv 


