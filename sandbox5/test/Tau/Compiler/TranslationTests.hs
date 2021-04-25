{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.TranslationTests where

import Tau.Compiler.Error
import Tau.Compiler.Translation
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Row
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils

succeedSimplifyExpr 
  :: ProgExpr (Maybe (TypeInfo [Error])) 
  -> SimplifiedExpr (Maybe (TypeInfo [Error])) 
  -> SpecWith ()
succeedSimplifyExpr e1 e2 = 
    describe ("The expression " <> prettyText e1) $ do
        it ("✔ simplifies to " <> prettyText e2) $ simplifyExpr e1 == e2

testSimplifyExpr :: SpecWith ()
testSimplifyExpr = do

    describe "Untyped" $ do

        describe "Tuples" $ do

            succeedSimplifyExpr 
                (tupleExpr Nothing [litExpr Nothing (TInt 1), litExpr Nothing (TString "abc")])
                (conExpr Nothing "(,)" [litExpr Nothing (TInt 1), litExpr Nothing (TString "abc")])

        describe "Lists" $ do

            succeedSimplifyExpr 
                (listExpr Nothing [litExpr Nothing (TInt 1), litExpr Nothing (TInt 2), litExpr Nothing (TInt 3)])
                (conExpr Nothing "(::)" [litExpr Nothing (TInt 1), conExpr Nothing "(::)" [litExpr Nothing (TInt 2), conExpr Nothing "(::)" [litExpr Nothing (TInt 3), conExpr Nothing "[]" []]]])

            succeedSimplifyExpr 
                (listExpr Nothing [])
                (conExpr Nothing "[]" [])

        describe "Records" $ do

            succeedSimplifyExpr 
                (recordExpr Nothing (rExt "name" (litExpr Nothing (TString "Bob")) (rExt "id" (litExpr Nothing (TInt 1)) rNil)))
                (conExpr Nothing "#Record" [conExpr Nothing "{id}" [litExpr Nothing (TInt 1), conExpr Nothing "{name}" [litExpr Nothing (TString "Bob"), conExpr Nothing "{}" []]]])

            succeedSimplifyExpr 
                (recordExpr Nothing (rExt "name" (litExpr Nothing (TString "Bob")) (rExt "id" (litExpr Nothing (TInt 1)) (rVar (varExpr Nothing "r")))))
                (conExpr Nothing "#Record" [conExpr Nothing "{id}" [litExpr Nothing (TInt 1), conExpr Nothing "{name}" [litExpr Nothing (TString "Bob"), varExpr Nothing "r"]]])

        describe "Unary operators" $ do

            succeedSimplifyExpr 
                (op1Expr Nothing (ONeg Nothing) (varExpr Nothing "x"))
                (appExpr Nothing [varExpr Nothing "negate", varExpr Nothing "x"])

        describe "Binary operators" $ do

            succeedSimplifyExpr 
                (op2Expr Nothing (OEq Nothing) (varExpr Nothing "x") (varExpr Nothing "y"))
                (appExpr Nothing [varExpr Nothing "(==)", varExpr Nothing "x", varExpr Nothing "y"])


    describe "Typed" $ do

        describe "Tuples" $ do

            succeedSimplifyExpr 
                (tupleExpr (ti (tTuple [tInt, tString])) [litExpr (ti tInt) (TInt 1), litExpr (ti tString) (TString "abc")])
                (conExpr (ti (tTuple [tInt, tString])) "(,)" [litExpr (ti tInt) (TInt 1), litExpr (ti tString) (TString "abc")])

        describe "Lists" $ do

            succeedSimplifyExpr 
                (listExpr (ti (tList tInt)) [litExpr (ti tInt) (TInt 1), litExpr (ti tInt) (TInt 2), litExpr (ti tInt) (TInt 3)])
                (conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 1), conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 2), conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 3), conExpr (ti (tList tInt)) "[]" []]]])

            succeedSimplifyExpr 
                (listExpr (ti (tList _a)) [])
                (conExpr (ti (tList _a)) "[]" [])

        describe "Records" $ do

            succeedSimplifyExpr 
                (recordExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))))) (rExt "name" (litExpr (ti tString) (TString "Bob")) (rExt "id" (litExpr (ti tInt) (TInt 1)) rNil)))
                (conExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))))) "#Record"
                    [conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") tInt) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}")))) "{id}" 
                        [litExpr (ti tInt) (TInt 1),
                            conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))) "{name}"
                               [litExpr (ti tString) (TString "Bob"),
                                   conExpr (ti (tCon kRow "{}")) "{}" []]]])

--            succeedSimplifyExpr 
--                (recordExpr undefined (rExt "name" (litExpr (ti tString) (TString "Bob")) (rExt "id" (litExpr (ti tInt) (TInt 1)) (rVar (varExpr (ti _a) "r")))))
--                (conExpr undefined "#Record" [conExpr undefined "{id}" [litExpr undefined (TInt 1), conExpr undefined "{name}" [litExpr undefined (TString "Bob"), varExpr undefined "r"]]])

        describe "Unary operators" $ do

            succeedSimplifyExpr 
                (op1Expr (ti tInt) (ONeg (ti (tInt `tArr` tInt))) (varExpr (ti tInt) "x"))
                (appExpr (ti tInt) [varExpr (ti (tInt `tArr` tInt)) "negate", varExpr (ti tInt) "x"])


ti ::  t -> Maybe (TypeInfoT [e] t)
ti t = Just (TypeInfo t [] [])
