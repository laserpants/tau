{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.TranslationTests where

import Data.Void
import Tau.Compiler.Error
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tooling
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils

--succeedSimplifyExpr 
--  :: (Eq t, InfoTag t, Typed t)
--  => ProgExpr t
--  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
--  -> SpecWith ()
--succeedSimplifyExpr e1 e2 = 
--    describe ("The expression " <> prettyText e1) $ do
--        it ("✔ simplifies to " <> prettyText e2) $ simplifyExpr2 e1 == e2
--
--testSimplifyExpr :: SpecWith ()
--testSimplifyExpr = do
--
--    describe "Untyped" $ do
--
--        describe "Tuples" $ do
--
--            succeedSimplifyExpr 
--                (tupleExpr () [litExpr () (TInt 1), litExpr () (TString "abc")])
--                (conExpr () "(,)" [litExpr () (TInt 1), litExpr () (TString "abc")])
--
--        describe "Lists" $ do
--
--            succeedSimplifyExpr 
--                (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)])
--                (conExpr () "(::)" [litExpr () (TInt 1), conExpr () "(::)" [litExpr () (TInt 2), conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []]]])
--
--            succeedSimplifyExpr 
--                (listExpr () [])
--                (conExpr () "[]" [])
--
--        describe "Records" $ do
--
--            succeedSimplifyExpr 
--                (recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) rNil)))
--                (conExpr () "#Record" [conExpr () "{id}" [litExpr () (TInt 1), conExpr () "{name}" [litExpr () (TString "Bob"), conExpr () "{}" []]]])
--
--            succeedSimplifyExpr 
--                (recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) (rVar (varExpr () "r")))))
--                (conExpr () "#Record" [conExpr () "{id}" [litExpr () (TInt 1), conExpr () "{name}" [litExpr () (TString "Bob"), varExpr () "r"]]])
--
--        describe "Unary operators" $ do
--
--            succeedSimplifyExpr 
--                (op1Expr () (ONeg ()) (varExpr () "x"))
--                (appExpr () [varExpr () "negate", varExpr () "x"])
--
--        describe "Binary operators" $ do
--
--            succeedSimplifyExpr 
--                (op2Expr () (OEq ()) (varExpr () "x") (varExpr () "y"))
--                (appExpr () [varExpr () "(==)", varExpr () "x", varExpr () "y"])
--
--        describe "Let bindings" $ do
--
--            succeedSimplifyExpr 
--                (letExpr () (BLet () (varPat () "x")) (varExpr () "y") (litExpr () (TInt 5)))
--                (patExpr () [varExpr () "y"] [ClauseA () [varPat () "x"] [] (litExpr () (TInt 5))])
--
--    describe "Typed" $ do
--
--        describe "Tuples" $ do
--
--            succeedSimplifyExpr 
--                (tupleExpr (ti (tTuple [tInt, tString])) [litExpr (ti tInt) (TInt 1), litExpr (ti tString) (TString "abc")])
--                (conExpr (ti (tTuple [tInt, tString])) "(,)" [litExpr (ti tInt) (TInt 1), litExpr (ti tString) (TString "abc")])
--
--        describe "Lists" $ do
--
--            succeedSimplifyExpr 
--                (listExpr (ti (tList tInt)) [litExpr (ti tInt) (TInt 1), litExpr (ti tInt) (TInt 2), litExpr (ti tInt) (TInt 3)])
--                (conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 1), conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 2), conExpr (ti (tList tInt)) "(::)" [litExpr (ti tInt) (TInt 3), conExpr (ti (tList tInt)) "[]" []]]])
--
--            succeedSimplifyExpr 
--                (listExpr (ti (tList _a)) [])
--                (conExpr (ti (tList _a)) "[]" [])
--
--        describe "Records" $ do
--
--            succeedSimplifyExpr 
--                (recordExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))))) (rExt "name" (litExpr (ti tString) (TString "Bob")) (rExt "id" (litExpr (ti tInt) (TInt 1)) rNil)))
--                (conExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))))) "#Record"
--                    [conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") tInt) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}")))) "{id}" 
--                        [litExpr (ti tInt) (TInt 1),
--                            conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tCon kRow "{}"))) "{name}"
--                               [litExpr (ti tString) (TString "Bob"),
--                                   conExpr (ti (tCon kRow "{}")) "{}" []]]])
--
--            succeedSimplifyExpr 
--                (recordExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tVar kRow "a"))))) (rExt "name" (litExpr (ti tString) (TString "Bob")) (rExt "id" (litExpr (ti tInt) (TInt 1)) (rVar (varExpr (ti (tVar kRow "a")) "r")))))
--                (conExpr (ti (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a3")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tVar kRow "a"))))) "#Record" 
--                    [conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") tInt) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tVar kRow "a")))) "{id}" 
--                        [litExpr (ti tInt) (TInt 1), 
--                            conExpr (ti (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") tString) (tVar kRow "a"))) "{name}" 
--                                [litExpr (ti tString) (TString "Bob"), 
--                                    varExpr (ti (tVar kRow "a")) "r"]]])
--
--        describe "Unary operators" $ do
--
--            succeedSimplifyExpr 
--                (op1Expr (ti tInt) (ONeg (ti (tInt `tArr` tInt))) (varExpr (ti tInt) "x"))
--                (appExpr (ti tInt) [varExpr (ti (tInt `tArr` tInt)) "negate", varExpr (ti tInt) "x"])
--
--        describe "Binary operators" $ do
--
--            succeedSimplifyExpr 
--                (op2Expr (ti tBool) (OEq (ti (tInt `tArr` tInt `tArr` tBool))) (varExpr (ti tInt) "x") (varExpr (ti tInt) "y"))
--                (appExpr (ti tBool) [varExpr (ti (tInt `tArr` tInt `tArr` tBool)) "(==)", varExpr (ti tInt) "x", varExpr (ti tInt) "y"])
--
--ti :: Type -> TypeInfo [Error]
--ti t = TypeInfo t [] []
