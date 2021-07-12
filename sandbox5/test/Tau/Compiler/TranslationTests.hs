{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.TranslationTests where

import Control.Monad.Reader
import Data.Maybe
import Data.Void
import Tau.Compiler.Bundle
import Tau.Compiler.Error
import Tau.Compiler.Pipeline.Stage0 
import Tau.Compiler.Pipeline.Stage1 
import Tau.Compiler.Pipeline.Stage2 
import Tau.Compiler.Pipeline.Stage3 
import Tau.Compiler.Pipeline.Stage4 
import Tau.Compiler.Pipeline.Stage5 
import Tau.Compiler.Pipeline.Stage6 
import Tau.Core
import Tau.Eval
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.TestEnv
import Tau.Tooling
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Text as Text
import qualified Tau.Compiler.Pipeline.Stage0 as Stage0
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6
import qualified Tau.Env as Env

--        "{ a = { b = { c = \"d\" } } }.a.b.c"


--succeedSimplifyExpr 
--  :: (Eq t, InfoTag t, Typed t)
--  => ProgExpr t
--  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
--  -> SpecWith ()
--succeedSimplifyExpr e1 e2 = 
--    describe ("The expression " <> prettyPrint e1) $ do
--        it ("✔ simplifies to " <> prettyPrint e2) $ simplifyExpr2 e1 == e2
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

testCompileBundle :: SpecWith ()
testCompileBundle = do

    let expr :: ProgExpr ()
        expr = Fix (EOp2 () (ODot ()) (Fix (EVar () "c")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ECon () "#" [Fix (ERow () "c" (Fix (ELit () (TString "d"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])))))))

    -- { a = { b = { c = "d" } } }.a.b.c
    bundle <- runReaderT (compileBundle expr)
            (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv) 

    let expr1 :: Stage1.TargetExpr (TypeInfoT [Error] (Maybe Type))
        expr1 = Fix (EApp (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "*")) "String")), nodePredicates = []}) [Fix (EVar (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TArr (Fix (TCon (Fix (KCon "*")) "Atom")) (Fix (TArr (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "*")) "String")))))), nodePredicates = []}) "@#getField"),Fix (ELit (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "*")) "Atom")), nodePredicates = []}) (TAtom "c")),Fix (EApp (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))), nodePredicates = []}) [Fix (EVar (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TArr (Fix (TCon (Fix (KCon "*")) "Atom")) (Fix (TArr (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))))))), nodePredicates = []}) "@#getField"),Fix (ELit (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "*")) "Atom")), nodePredicates = []}) (TAtom "b")),Fix (EApp (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))), nodePredicates = []}) [Fix (EVar (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TArr (Fix (TCon (Fix (KCon "*")) "Atom")) (Fix (TArr (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "a" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))))))), nodePredicates = []}) "@#getField"),Fix (ELit (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "*")) "Atom")), nodePredicates = []}) (TAtom "a")),Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "a" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))), nodePredicates = []}) "#" [Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TRow "a" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))), nodePredicates = []}) "{a}" [Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))), nodePredicates = []}) "#" [Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TRow "b" (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))), nodePredicates = []}) "{b}" [Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TApp (Fix (KCon "*")) (Fix (TCon (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "*")))) "#")) (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))))), nodePredicates = []}) "#" [Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TRow "c" (Fix (TCon (Fix (KCon "*")) "String")) (Fix (TCon (Fix (KCon "Row")) "{}")))), nodePredicates = []}) "{c}" [Fix (ELit (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "*")) "String")), nodePredicates = []}) (TString "d")),Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "Row")) "{}")), nodePredicates = []}) "{}" [])])]),Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "Row")) "{}")), nodePredicates = []}) "{}" [])])]),Fix (ECon (TypeInfo {nodeErrors = [], nodeType = Just (Fix (TCon (Fix (KCon "Row")) "{}")), nodePredicates = []}) "{}" [])])])])])])

    let coreExpr_ = Fix (CApp [Fix (CVar "@#getField"),Fix (CLit (TAtom "c")),Fix (CApp [Fix (CVar "@#getField"),Fix (CLit (TAtom "b")),Fix (CApp [Fix (CVar "@#getField"),Fix (CLit (TAtom "a")),Fix (CApp [Fix (CVar "#"),Fix (CApp [Fix (CVar "{a}"),Fix (CApp [Fix (CVar "#"),Fix (CApp [Fix (CVar "{b}"),Fix (CApp [Fix (CVar "#"),Fix (CApp [Fix (CVar "{c}"),Fix (CLit (TString "d")),Fix (CVar "{}")])]),Fix (CVar "{}")])]),Fix (CVar "{}")])])])])])

    let value = Value (TString "d")

    describe (prettyPrint expr) $ do

        it ("✔ Stage #1     : " <> prettyPrint expr1) $ 
            Just expr1 == (stage1Expr bundle)

        it "✔ Core         : ... TODO ..." $ 
            Just coreExpr_ == (coreExpr bundle)

        it ("✔ Evaluates to : " <> Text.pack (show value)) $
            (Just value) == evalExpr coreExpr_ testEvalEnv

    ---------------------------------------------------------------------------
    ---------------------------------------------------------------------------

    --    fix loopList =
    --      (g, ys) =>
    --        match ys with
    --          | x :: xs => g(Cons'(x, xs, loopList(g, xs)))
    --          | []      => g(Nil')
    --      in
    --        let length(xs) =
    --          xs.loopList(fun
    --            | Cons'(_, _, a) => 1 + a
    --            | Nil'           => 0 : Int)
    --          in
    --            let xs = [5] : List Int
    --              in
    --                match xs with
    --                  | x :: _                  
    --                      when(length(xs) <= 3) => x
    --                  | _                       => 0
    --
    let expr :: ProgExpr ()
        expr = (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () (conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]) [Guard [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () (conPat () "Nil'" []) [Guard [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 5)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Guard [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () (anyPat ()) [Guard [] (litExpr () (TInteger 0))] ])))) 

    bundle <- runReaderT (compileBundle expr)
            (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv) 

    --undefined
    pure ()
