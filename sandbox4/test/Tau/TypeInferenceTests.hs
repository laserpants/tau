{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeInferenceTests where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Maybe
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.TestEnvs
import Tau.Util
import Tau.Util.Env (Env(..))
import Test.Hspec
import Utils
import qualified Tau.Comp.Type.Substitution as Sub
import qualified Tau.Util.Env as Env

type InferState  = StateT (Substitution, Context)
type InferReader = ReaderT (ClassEnv, TypeEnv)
type InferSupply = SupplyT Name
type InferError  = ExceptT String

runInferState :: StateT (Substitution, Context) m a -> m (a, (Substitution, Context))
runInferState = flip runStateT mempty

runInferReader :: a -> b -> ReaderT (a, b) m r -> m r
runInferReader a b = flip runReaderT (a, b)

runInferSupply :: (Monad m) => SupplyT Name m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInferError :: ExceptT e m a -> m (Either e a)
runInferError = runExceptT

runInferMaybe :: Maybe (Either String a) -> Either String a
runInferMaybe = fromMaybe (Left "error")

type InferStack = InferState (InferReader (InferSupply (InferError Maybe)))

runInfer :: InferStack a -> Either String (a, (Substitution, Context))
runInfer = runInferState
    >>> runInferReader testClassEnv testTypeEnv
    >>> runInferSupply
    >>> runInferError
    >>> runInferMaybe

runTest :: ProgExpr -> Either String Type
runTest expr = do
    (ast, (sub, _)) <- runInfer (infer expr)
    pure (typeOf (apply sub (exprTag ast)))

normalize :: Type -> Type
normalize ty = apply sub ty
  where
    sub = Sub.fromList (zipWith fun (typeVars ty) letters)
    fun (v, k) a = (v, tVar k a :: Type)

succeedInferType :: ProgExpr -> Type -> SpecWith ()
succeedInferType expr expected =
    describe ("The expression : " <> prettyString expr) $
        it ("✔ has type " <> prettyString expected <> "\n") $
            (normalize <$> runTest expr) == Right expected

failInferTypeWithError :: ProgExpr -> String -> SpecWith ()
failInferTypeWithError expr err = 
    describe ("The expression : " <> prettyString expr) $
        it ("✗ fails with error " <> show err <> "\n") $
            runTest expr == Left err


--testExpr1 = letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", varPat () "b"] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () TUnit])

--testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
--
--testExpr3 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (TInt 5)])
--
--testExpr4 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])
--
--testExpr5 = lamExpr () [varPat () "x"] (letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
--
--testExpr6 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))
--
--testExpr7 = appExpr () [varExpr () "lenShow", litExpr () (TInt 555)]
--
--testExpr8 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])
--
--testExpr9 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
--
--testExpr10 = letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () TUnit])
--
--testExpr11 = letExpr () (BLet (varPat () "p")) (conExpr () "(,)" [litExpr () (TInt 5), litExpr () (TInt 1)]) (appExpr () [varExpr () "show", varExpr () "p"])
--
--testExpr12 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]])
--
---- TODO

testTypeInference :: SpecWith ()
testTypeInference = do

    succeedInferType
        (letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", varPat () "b"] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () TUnit]))
        (_a `tArr` tUnit)

    failInferTypeWithError 
        (op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () TUnit))
        "CannotUnify"

    succeedInferType
        (appExpr () [varExpr () "const", litExpr () (TInt 5), litExpr () TUnit])
        tInt

    succeedInferType
        (appExpr () [varExpr () "id", litExpr () (TInt 5)])
        tInt

    succeedInferType
        (varExpr () "id")
        (_a `tArr` _a)

    succeedInferType
        (varExpr () "const")
        (_a `tArr` _b `tArr` _a)

    succeedInferType
        (letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", varPat () "b"] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () TUnit, litExpr () (TInt 5)]))
        tUnit

    succeedInferType
        (letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", anyPat ()] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () TUnit, litExpr () (TInt 5)]))
        tUnit
    
    --TODO

    succeedInferType
        (lamExpr () [varPat () "xs"] (patExpr () [varExpr () "xs"] [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (litExpr () (TInt 1))], Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 2))] ]))
        (tList _a `tArr` tInt)

    succeedInferType
        (appExpr () [lamExpr () [varPat () "xs"] (patExpr () [varExpr () "xs"] [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (litExpr () (TInt 1))], Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 2))] ]), conExpr () "(::)" [litExpr () (TInt 5), conExpr () "[]" []]])
        tInt

    succeedInferType
        (patExpr () [] [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (litExpr () (TInt 1))], Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 2))] ])
        (tList _a `tArr` tInt)

    succeedInferType
        (appExpr () [patExpr () [] [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (litExpr () (TInt 1))], Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 2))] ], conExpr () "(::)" [litExpr () (TInt 5), conExpr () "[]" []]])
        tInt

    succeedInferType
        (patExpr () [conExpr () "(::)" [litExpr () (TInt 5), conExpr () "[]" []]] [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (litExpr () (TInt 1))], Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 2))] ])
        tInt

    succeedInferType
        (letExpr () (BFun "plus" [varPat () "a", varPat () "b"]) 
          (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) 
            (letExpr () (BLet (varPat () "plus5")) (appExpr () [varExpr () "plus", litExpr () (TInt 5)]) 
              (letExpr () (BLet (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x"))
                (appExpr () [appExpr () [varExpr () "id", varExpr () "plus5"], appExpr () [varExpr () "id", litExpr () (TInt 3)]]))))
        tInt

    succeedInferType
        (letExpr () (BFun "plus" [varPat () "a", varPat () "b"]) 
          (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) 
            (letExpr () (BLet (varPat () "plus5")) (appExpr () [varExpr () "plus", litExpr () (TInt 5)]) 
              (letExpr () (BFun "id" [varPat () "x"]) (varExpr () "x") 
                (appExpr () [appExpr () [varExpr () "id", varExpr () "plus5"], appExpr () [varExpr () "id", litExpr () (TInt 3)]]))))
        tInt




----    succeedInferType
----        $(parseExpr "let id = \\x => x in let x = (id, 4) in (fst x snd x) + 1")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "(\\x => match x with 1 => 2 | 2 => 3) 1")
----        $(parseScheme "Int")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons \"a\" Nil with Cons y ys => y + 1")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons 4 ys => \"foo\"")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | 5 => 1")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons \"w\" z => 1")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons z 5 => 1")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match Cons 6 Nil with Cons y ys => y | _ => \"two\"")
----
----    failInferTypeWithError EmptyMatchStatement
----        (matchS (appS [varS "Nil"]) [])
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == True then 1 else 0")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if Cons True Nil == Cons 1 Nil then 1 else 0")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if Cons True Nil == Guard 1 Nil then 1 else 0")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if Cons True Nil == Cons then 1 else 0")
----
----    failInferTypeWithError (UnboundVariable "x")
----        $(parseExpr "let x = x in x")
----
----    failInferTypeWithError (UnboundVariable "f")
----        $(parseExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
----
----    succeedInferType
----        $(parseExpr "let fst = \\match (a, b) => a in fst (1, 2)")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "let fst = \\match (a, b) => a in (1, 2).fst")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "let fst (a, b) = a in fst (1, 2)")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "(\\x y z => x + z)")
----        $(parseScheme "forall a b. a -> b -> a -> a")
----
----    failInferTypeWithError (NameClash "key")
----        $(parseExpr "let key = \\_ => 5 in { key = 5 }.key")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then (1, 2) else (1,2,3)")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then (1, 2) else (1,'a')")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then 1 :: 2 :: [] else False :: []")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "1 :: False :: []")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then { a = 3 } else { a = 3, b = 3 }")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then { a = 3 } else { a = False }")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "if 1 == 1 then { a = 3 } else { b = 3 }")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match { a = 3 } with { a = 3 } => 0 | { a = 4, b = 5 } => 0 | _ => 0")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match { a = 3 } with { a = 3 } => 0 | { b = 4 } => 0 | _ => 0")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        (compileAll $(parseExpr "match (1, 2) with (2, 3) => 0 | (2, 3, 4) => 0 | _ => 0"))
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        (compileAll $(parseExpr "match (1, 2) with (2, 3) => 0 | (\"a\", 3) => 0 | _ => 0"))
----
----    succeedInferType
----        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, c = name } => (x, name) | _ => (0, \"default\")")
----        $(parseScheme "(Int, String)")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, c = name } => (x, x) | _ => (0, \"default\")")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, d = name } => (x, name) | _ => (0, \"default\")")
----
----    failInferTypeWithError (UnboundVariable "x")
----        $(parseExpr "match (100, 1) with (101, 1) => x | _ => 1")
----
----    succeedInferType
----        $(parseExpr "match { stuff = (), user = { name = \"Bob\" } } with { stuff = (), user = { name = name } } => name")
----        $(parseScheme "String")
----
----    succeedInferType
----        $(parseExpr "match { stuff = (), user = { id = 1, name = \"Bob\" } } with { stuff = (), user = { id = _, name = name } } => name")
----        $(parseScheme "String")
----
----    succeedInferType
----        $(parseExpr "match { stuff = (), user = { id = 1, data = { name = \"Bob\", shoeSize = 42 } } } with { stuff = (), user = { id = _, data = { name = name, shoeSize = 42 } } } => name")
----        $(parseScheme "String")
----
----    succeedInferType
----        $(parseExpr "match { stuff = (), user = { id = 1, data = { name = (\"Bob\", \"Doe\"), shoeSize = 42 } } } with { stuff = (), user = { id = _, data = { name = (firstName, _), shoeSize = 42 } } } => firstName")
----        $(parseScheme "String")
----
----    failInferTypeWithError (UnificationError CannotUnify)
----        $(parseExpr "match { a = 5 } with { a = x, b = _ } => 1 | _ => 123")
----
----    succeedInferType
----        $(parseExpr "let fst (a, b) = a in { a = { b = ({ stuff = ['x', 'y'] }, 3) } }.a.b.fst.stuff")
----        $(parseScheme "List Char")
----
----    succeedInferType
----        $(parseExpr "let x = { a = { b = \\() => 123 } } in x.a.b ()")
----        $(parseScheme "Int")
----
----    succeedInferType
----        $(parseExpr "((\\{ x = y } => { z = y }) { x = \"stuff\" }).z")
----        $(parseScheme "String")
----
------    succeedInferType
------        $(parseExpr "{ key = 5 }.key")
------        $(parseScheme "Int")
------
------    succeedInferType
------        $(parseExpr "let obj = { key = 5 } in obj.key")
------        $(parseScheme "Int")
------
------    failInferTypeWithError (UnboundVariable "b")
------        $(parseExpr "{ a = 5 }.b")
------
------    succeedInferType
------        $(parseExpr "{ a = { b = 5 }}.a.b")
------        $(parseScheme "Int")
------
------    succeedInferType
------        $(parseExpr "{ a = { a = \"test\" }}.a.a")
------        $(parseScheme "String")
------
------    failInferTypeWithError (UnboundVariable "a")
------        $(parseExpr "{ a = { b = 3 } }.a.a")
