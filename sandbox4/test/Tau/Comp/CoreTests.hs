{-# LANGUAGE OverloadedStrings #-}
module Tau.Comp.CoreTests where

import Tau.Comp.Core
import Tau.Lang.Expr
import Test.Hspec
import Utils

type TestMatrix = [[Pattern () () ()]]

computeDefaultMatrix :: TestMatrix -> TestMatrix -> SpecWith ()
computeDefaultMatrix m1 m2 = 
    it "✔ TODO\n" $
        defaultMatrix m1 == m2

testDefaultMatrix :: SpecWith ()
testDefaultMatrix = do

    computeDefaultMatrix 

        [ [ varPat () "a11", varPat () "a12" ]
        , [ varPat () "a21", varPat () "a22" ]
        , [ varPat () "a31", varPat () "a32" ]
        ]

        [ [ varPat () "a12" ]
        , [ varPat () "a22" ]
        , [ varPat () "a32" ]
        ]

    computeDefaultMatrix 

        [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
        , [ varPat () "a21", varPat () "a22", varPat () "a23" ]
        , [ varPat () "a31", varPat () "a32", varPat () "a33" ]
        ]

        [ [ varPat () "a12", varPat () "a13" ]
        , [ varPat () "a22", varPat () "a23" ]
        , [ varPat () "a32", varPat () "a33" ]
        ]

    computeDefaultMatrix 

        [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
        , [ conPat () "c" [], varPat () "a22", varPat () "a23" ]
        , [ varPat () "a31", varPat () "a32", varPat () "a33" ]
        ]

        [ [ varPat () "a12", varPat () "a13" ]
        , [ varPat () "a32", varPat () "a33" ]
        ]

    computeDefaultMatrix 

        [ [ litPat () (TInt 5), varPat () "a12", varPat () "a13" ]
        , [ conPat () "c" [], varPat () "a22", varPat () "a23" ]
        , [ varPat () "a31", varPat () "a32", varPat () "a33" ]
        ]

        [ [ varPat () "a32", varPat () "a33" ]
        ]

    computeDefaultMatrix 

        [ [ litPat () (TInt 5), varPat () "a12", varPat () "a13" ]
        , [ conPat () "c" [], varPat () "a22", varPat () "a23" ]
        , [ conPat () "c" [], varPat () "a32", varPat () "a33" ]
        ]

        []

    -- as-patterns

    describe "as-patterns\n" $ do

        computeDefaultMatrix 

            [ [ asPat () "b11" (varPat () "a11"), varPat () "a12" ]
            , [ varPat () "a21", varPat () "a22" ]
            , [ varPat () "a31", varPat () "a32" ]
            ]

            [ [ varPat () "a12" ]
            , [ varPat () "a22" ]
            , [ varPat () "a32" ]
            ]

        computeDefaultMatrix 

            [ [ asPat () "b11" (varPat () "a11"), asPat () "b12" (varPat () "a12") ]
            , [ varPat () "a21", varPat () "a22" ]
            , [ varPat () "a31", varPat () "a32" ]
            ]

            [ [ asPat () "b12" (varPat () "a12") ]
            , [ varPat () "a22" ]
            , [ varPat () "a32" ]
            ]

        computeDefaultMatrix 

            [ [ asPat () "b11" (varPat () "a11"), varPat () "a12", varPat () "a13" ]
            , [ asPat () "b21" (conPat () "c" []), varPat () "a22", varPat () "a23" ]
            , [ asPat () "b31" (varPat () "a31"), varPat () "a32", varPat () "a33" ]
            ]

            [ [ varPat () "a12", varPat () "a13" ]
            , [ varPat () "a32", varPat () "a33" ]
            ]

        computeDefaultMatrix 

            [ [ asPat () "b11" (litPat () (TInt 5)), varPat () "a12", varPat () "a13" ]
            , [ asPat () "b21" (conPat () "c" []), varPat () "a22", varPat () "a23" ]
            , [ asPat () "b31" (varPat () "a31"), varPat () "a32", varPat () "a33" ]
            ]

            [ [ varPat () "a32", varPat () "a33" ]
            ]

    -- or-patterns

    describe "or-patterns\n" $ do

        computeDefaultMatrix 

            [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
            , [ orPat () (conPat () "c" [varPat () "x"]) (conPat () "d" [varPat () "x"]), varPat () "a22", varPat () "a23" ]
            ]

            ([ [ varPat () "a12", varPat () "a13" ] ] <> defaultMatrix 
               [ [ conPat () "c" [varPat () "x"], varPat () "a22", varPat () "a23" ]
               , [ conPat () "d" [varPat () "x"], varPat () "a22", varPat () "a23" ]
             ]) 

        computeDefaultMatrix 

            [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
            , [ orPat () (conPat () "c" [varPat () "x"]) (conPat () "d" [varPat () "x"]), varPat () "a22", varPat () "a23" ]
            ]

            [ [ varPat () "a12", varPat () "a13" ] ]

        computeDefaultMatrix 

            [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
            , [ orPat () (varPat () "a21") (varPat () "b21"), varPat () "a22", varPat () "a23" ]
            ]

            ([ [ varPat () "a12", varPat () "a13" ] ] <> defaultMatrix 
               [ [ varPat () "a21", varPat () "a22", varPat () "a23" ]
               , [ varPat () "b21", varPat () "a22", varPat () "a23" ]
             ]) 

        computeDefaultMatrix 

            [ [ varPat () "a11", varPat () "a12", varPat () "a13" ]
            , [ orPat () (varPat () "a21") (varPat () "b21"), varPat () "a22", varPat () "a23" ]
            ]

            [ [ varPat () "a12", varPat () "a13" ] 
            , [ varPat () "a22", varPat () "a23" ]
            , [ varPat () "a22", varPat () "a23" ]
            ]
