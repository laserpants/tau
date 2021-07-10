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
            expr1 == (stage1Expr bundle)

        it "✔ Core         : ... TODO ..." $ 
            coreExpr_ == (coreExpr bundle)

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


testKindEnv :: KindEnv
testKindEnv = Env.fromList
    [ ( "Num" , kArr kTyp kClass )
    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Zero"         , Forall []     [] (tCon kTyp "Nat") )
    , ( "Succ"         , Forall []     [] (tCon kTyp "Nat" `tArr` tCon kTyp "Nat") )
    , ( "Leaf"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Tree") (tGen 0)) )
    , ( "Node"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0)) )

    , ( "Leaf'"        , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )
    , ( "Node'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tGen 1 `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )

    , ( "Nil'"         , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )
    , ( "Cons'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )

    , ( "Foo"          , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    , ( "id"           , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    , ( "(::)"         , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )

    -- TEMP
    , ( "(==)"         , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )

    , ( "testFun1"     , Forall [kTyp] [InClass "Num" 0, InClass "Eq" 0] (tGen 0 `tArr` tBool) )
    , ( "length"       , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )

    , ( "[]"           , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "(+)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "#"            , Forall [kRow] [] (tGen 0 `tArr` tApp kTyp tRecordCon (tGen 0)) )
    , ( "{}"           , Forall [] [] tRowNil )
    , ( "_#"           , Forall [kRow] [] (tApp kTyp (tCon (kArr kRow kTyp) "#") (tGen 0) `tArr` tGen 0) )
    , ( "fromInteger"  , Forall [kTyp] [InClass "Num" 0] (tInteger `tArr` tGen 0) )
    , ( "fn1"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Show"
        -- Interface
      , ( ClassInfo (InClass "Show" "a") []  
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.Show") )
              ]
          , ClassInfo (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b"))) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "TODO") )
              ]
          ]
        )
      )
    , ( "Ord"
        -- Interface
      , ( ClassInfo (InClass "Ord" "a") [] 
            [ ( "(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(>=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            ]
        -- Instances
        , [ ClassInfo (InClass "Ord" tInt) [] 
              [ ( "(>)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)") ) 
              , ( "(<)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)") ) 
              , ( "(>=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>=)") ) 
              , ( "(<=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<=)") ) 
              ]
          ]
        )
      )
    , ( "Eq"
        -- Interface
      , ( ClassInfo (InClass "Eq" "a") [] -- [InClass "Ord" "a"] 
            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Eq" tInt) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)" ) )
            ]
          ]
        )
      )
    , ( "Foo"
        -- Interface
      , ( ClassInfo (InClass "Foo" "a") [] 
            -- [ ( "foo", tInt ) 
            [ ( "foo", tBool ) 
            ]
        -- Instances
        , [ ClassInfo (InClass "Foo" tInt) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 5))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool True))) ) ]
          , ClassInfo (InClass "Foo" tInteger) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 7))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool False))) ) ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo (InClass "Num" "a") [InClass "Eq" "a", InClass "Foo" "a"]
            [ ( "(+)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "(*)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "fromInteger" , tInteger `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , [ ClassInfo (InClass "Num" tInt) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInt) []) "@Int.fromInteger") )
            ]
          , ClassInfo (InClass "Num" tInteger) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(*)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger) []) "@Integer.id") )
            ]
          ]
        )
      )
    ]

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("Zero"     , ( ["Zero", "Succ"], 0 ))
    , ("Succ"     , ( ["Zero", "Succ"], 1 ))
    , ("Leaf"     , ( ["Leaf", "Node"], 0 ))
    , ("Node"     , ( ["Leaf", "Node"], 3 ))
    , ("Leaf'"    , ( ["Leaf'", "Node'"], 0 ))
    , ("Node'"    , ( ["Leaf'", "Node'"], 5 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    , ("#"        , ( ["#"], 1 ))
    , ("{}"       , ( ["{}"], 0 ))
    ]

testEvalEnv :: ValueEnv Eval
testEvalEnv = Env.fromList 
    [ -- ( "(,)" , constructor "(,)" 2 )
      ( "_#"  , fromJust (evalExpr (cLam "?0" (cPat (cVar "?0") [(["#", "?1"], cVar "?1")])) mempty) ) 
    , ( "(.)" , fromJust (evalExpr (cLam "f" (cLam "x" (cApp [cVar "f", cVar "x"]))) mempty) )
--    , ( "fn1" , fromJust (evalExpr (cLam "?0" (cLam "?1" (cApp [cVar "@Integer.(+)", cVar "?0", cVar "?1"]))) mempty) )
    ]
