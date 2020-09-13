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
        (letS "z" (litInt 3) (varS "y"))

    succeedSubstitute 
        $(mkExpr "let x = 3 in x + 5")
        ("x", varS "y")
        (letS "x" (litInt 3) (addS (varS "x") (litInt 5)))

    succeedSubstitute 
        $(mkExpr "let y = 3 in x + 5")
        ("x", litInt 8)
        (letS "y" (litInt 3) (addS (litInt 8) (litInt 5)))

    succeedSubstitute 
        $(mkExpr "let y = x + 3 in 45")
        ("x", litInt 2)
        (letS "y" (addS (litInt 2) (litInt 3)) (litInt 45))

    succeedSubstitute 
        $(mkExpr "let x = x + 3 in 45")
        ("x", litInt 2)
        (letS "x" (addS (litInt 2) (litInt 3)) (litInt 45))

    succeedSubstitute 
        $(mkExpr "let rec x = x + 3 in 45")
        ("x", litInt 2)
        (recS "x" (addS (varS "x") (litInt 3)) (litInt 45))

    succeedSubstitute 
        $(mkExpr "let x = 3 in let y = x + 1 in 45")
        ("x", litInt 2)
        (letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45)))

    succeedSubstitute 
        $(mkExpr "let x = 3 in let y = z + 1 in 45")
        ("z", litInt 2)
        (letS "x" (litInt 3) (letS "y" (addS (litInt 2) (litInt 1)) (litInt 45)))

    succeedSubstitute 
        $(mkExpr "match xs = x => 5")
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "x", litInt 5)])

    succeedSubstitute 
        $(mkExpr "match xs = x => x")
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "x", varS "x")])

    succeedSubstitute 
        $(mkExpr "match xs = y => x")
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "y", litInt 123)])

    succeedSubstitute 
        $(mkExpr "match xs = Cons x xs => x")
        ("x", litInt 123)
        (matchS (varS "xs") [(conP "Cons" [varP "x", varP "xs"], varS "x")])

    succeedSubstitute 
        $(mkExpr "match xs = Cons y xs => x")
        ("x", litInt 123)
        (matchS (varS "xs") [(conP "Cons" [varP "y", varP "xs"], litInt 123)])

    succeedSubstitute 
        $(mkExpr "match x = _ => x")
        ("x", litInt 123)
        (matchS (litInt 123) [(anyP, litInt 123)])
