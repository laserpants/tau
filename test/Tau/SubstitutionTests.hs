{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.SubstitutionTests where

import Tau.Expr
import Tau.Type
import Tau.Util
import Tau.Util.TH
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
        $(parseExpr "let z = 3 in x")
        ("x", varS "y")
        $(parseExpr "let z = 3 in y")

    succeedSubstitute 
        $(parseExpr "let x = 3 in x + 5")
        ("x", varS "y")
        $(parseExpr "let x = 3 in x + 5")

    succeedSubstitute 
        $(parseExpr "let y = 3 in x + 5")
        ("x", litInt 8)
        $(parseExpr "let y = 3 in 8 + 5")

    succeedSubstitute 
        $(parseExpr "let y = x + 3 in 45")
        ("x", litInt 2)
        $(parseExpr "let y = 2 + 3 in 45")

    succeedSubstitute 
        $(parseExpr "let x = x + 3 in 45")
        ("x", litInt 2)
        $(parseExpr "let x = 2 + 3 in 45")

    succeedSubstitute 
        $(parseExpr "let rec x = x + 3 in 45")
        ("x", litInt 2)
        $(parseExpr "let rec x = x + 3 in 45")

    succeedSubstitute 
        $(parseExpr "let x = 3 in let y = x + 1 in 45")
        ("x", litInt 2)
        $(parseExpr "let x = 3 in let y = x + 1 in 45")

    succeedSubstitute 
        $(parseExpr "let x = 3 in let y = z + 1 in 45")
        ("z", litInt 2)
        $(parseExpr "let x = 3 in let y = 2 + 1 in 45")

    succeedSubstitute 
        $(parseExpr "match xs with x => 5")
        ("x", litInt 123)
        $(parseExpr "match xs with x => 5")

    succeedSubstitute 
        $(parseExpr "match xs with x => x")
        ("x", litInt 123)
        $(parseExpr "match xs with x => x")

    succeedSubstitute 
        $(parseExpr "match xs with | y => x")
        ("x", litInt 123)
        $(parseExpr "match xs with | y => 123")

    succeedSubstitute 
        $(parseExpr "match xs with Cons x xs => x")
        ("x", litInt 123)
        $(parseExpr "match xs with Cons x xs => x")

    succeedSubstitute 
        $(parseExpr "match xs with Cons y xs => x")
        ("x", litInt 123)
        $(parseExpr "match xs with Cons y xs => 123")

    succeedSubstitute 
        $(parseExpr "match x with _ => x")
        ("x", litInt 123)
        $(parseExpr "match 123 with _ => 123")
