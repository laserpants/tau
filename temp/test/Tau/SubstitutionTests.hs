{-# LANGUAGE OverloadedStrings #-}
module Tau.SubstitutionTests where

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
        (letS "z" (litInt 3) (varS "x"))
        ("x", varS "y")
        (letS "z" (litInt 3) (varS "y"))

    succeedSubstitute 
        (letS "x" (litInt 3) (addS (varS "x") (litInt 5)))
        ("x", varS "y")
        (letS "x" (litInt 3) (addS (varS "x") (litInt 5)))

    succeedSubstitute 
        (letS "y" (litInt 3) (addS (varS "x") (litInt 5)))
        ("x", litInt 8)
        (letS "y" (litInt 3) (addS (litInt 8) (litInt 5)))

    succeedSubstitute 
        (letS "y" (addS (varS "x") (litInt 3)) (litInt 45))
        ("x", litInt 2)
        (letS "y" (addS (litInt 2) (litInt 3)) (litInt 45))

    succeedSubstitute 
        (letS "x" (addS (varS "x") (litInt 3)) (litInt 45))
        ("x", litInt 2)
        (letS "x" (addS (litInt 2) (litInt 3)) (litInt 45))

    succeedSubstitute 
        (recS "x" (addS (varS "x") (litInt 3)) (litInt 45))
        ("x", litInt 2)
        (recS "x" (addS (varS "x") (litInt 3)) (litInt 45))

    succeedSubstitute 
        (letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45)))
        ("x", litInt 2)
        (letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45)))

    succeedSubstitute 
        (letS "x" (litInt 3) (letS "y" (addS (varS "z") (litInt 1)) (litInt 45)))
        ("z", litInt 2)
        (letS "x" (litInt 3) (letS "y" (addS (litInt 2) (litInt 1)) (litInt 45)))

    succeedSubstitute 
        (matchS (varS "xs") [(varP "x", litInt 5)])
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "x", litInt 5)])

    succeedSubstitute 
        (matchS (varS "xs") [(varP "x", varS "x")])
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "x", varS "x")])

    succeedSubstitute 
        (matchS (varS "xs") [(varP "y", varS "x")])
        ("x", litInt 123)
        (matchS (varS "xs") [(varP "y", litInt 123)])

    succeedSubstitute 
        (matchS (varS "xs") [(conP "Cons" [varP "x", varP "xs"], varS "x")])
        ("x", litInt 123)
        (matchS (varS "xs") [(conP "Cons" [varP "x", varP "xs"], varS "x")])

    succeedSubstitute 
        (matchS (varS "xs") [(conP "Cons" [varP "y", varP "xs"], varS "x")])
        ("x", litInt 123)
        (matchS (varS "xs") [(conP "Cons" [varP "y", varP "xs"], litInt 123)])

    succeedSubstitute 
        (matchS (varS "x") [(anyP, varS "x")])
        ("x", litInt 123)
        (matchS (litInt 123) [(anyP, litInt 123)])
