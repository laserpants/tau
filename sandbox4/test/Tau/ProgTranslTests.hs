{-# LANGUAGE OverloadedStrings #-}
module Tau.ProgTranslTests where

import Tau.Lang.Expr
import Tau.Lang.Prog
import Test.Hspec
import Utils

testModule :: Module
testModule = Module
    { moduleName = "TestModule"
    , moduleTypes = 
        []
    , moduleDefs = 
        [ Def "factorial" [Clause [varPat () "n"] [] (fixExpr () "f" undefined undefined)] []
        , Def "map" [] []
        , Def "testList" [] []
        , Def "main" [] []
        ]
    , moduleClasses = 
        []
    , moduleInstances = 
        []
    }

testProgTransl :: SpecWith ()
testProgTransl =
    pure ()
