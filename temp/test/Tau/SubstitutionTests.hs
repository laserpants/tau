{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.SubstitutionTests where

import TH
import Tau.Expr
import Tau.Type
import Tau.Util
import Test.Hspec
import Utils

description :: Expr -> Name -> Expr -> String
description body var expr =
    "Substituting " <> prettyString expr <> " for " 
                    <> prettyString var <> " in " 
                    <> prettyString body

succeedSubstitute :: Expr -> (Name, Expr) -> Expr -> SpecWith ()
succeedSubstitute body (var, expr) expected =
    describe (description body var expr) $ 
        it ("✔ gives expected result: " <> prettyString expected) $
            apply (var `mapsTo` expr) body == expected

testSubstitute :: SpecWith ()
testSubstitute = do
    succeedSubstitute 
        $(mkExpr "let z = 3 in x")
        ("x", varS "y")
        $(mkExpr "let z = 3 in y")

    succeedSubstitute 
        $(mkExpr "let x = 3 in x + 5")
        ("x", varS "y")
        $(mkExpr "let x = 3 in x + 5")

    succeedSubstitute 
        $(mkExpr "let y = 3 in x + 5")
        ("x", litInt 8)
        $(mkExpr "let y = 3 in 8 + 5")

    succeedSubstitute 
        $(mkExpr "let y = x + 3 in 45")
        ("x", litInt 2)
        $(mkExpr "let y = 2 + 3 in 45")

    succeedSubstitute 
        $(mkExpr "let x = x + 3 in 45")
        ("x", litInt 2)
        $(mkExpr "let x = 2 + 3 in 45")

    succeedSubstitute 
        $(mkExpr "let rec x = x + 3 in 45")
        ("x", litInt 2)
        $(mkExpr "let rec x = x + 3 in 45")

    succeedSubstitute 
        $(mkExpr "let x = 3 in let y = x + 1 in 45")
        ("x", litInt 2)
        $(mkExpr "let x = 3 in let y = x + 1 in 45")

    succeedSubstitute 
        $(mkExpr "let x = 3 in let y = z + 1 in 45")
        ("z", litInt 2)
        $(mkExpr "let x = 3 in let y = 2 + 1 in 45")

    succeedSubstitute 
        $(mkExpr "match xs = x => 5")
        ("x", litInt 123)
        $(mkExpr "match xs = x => 5")

    succeedSubstitute 
        $(mkExpr "match xs = x => x")
        ("x", litInt 123)
        $(mkExpr "match xs = x => x")

    succeedSubstitute 
        $(mkExpr "match xs = y => x")
        ("x", litInt 123)
        $(mkExpr "match xs = y => 123")

    succeedSubstitute 
        $(mkExpr "match xs = Cons x xs => x")
        ("x", litInt 123)
        $(mkExpr "match xs = Cons x xs => x")

    succeedSubstitute 
        $(mkExpr "match xs = Cons y xs => x")
        ("x", litInt 123)
        $(mkExpr "match xs = Cons y xs => 123")

    succeedSubstitute 
        $(mkExpr "match x = _ => x")
        ("x", litInt 123)
        $(mkExpr "match 123 = _ => 123")
