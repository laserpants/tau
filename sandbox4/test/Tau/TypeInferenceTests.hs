{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeInferenceTests where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Writer
import Data.Maybe
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import Test.Hspec
import Utils
import qualified Tau.Util.Env as Env

--classEnv :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
--classEnv = Env.fromList 
--    [ ( "Num"
--      , ( []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) (fieldSet 
--              [ Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(*)Int")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(-)Int")
--              ]))
--          ] 
--        )
--      )
--    , ( "Show"
--      , ( []
--        , [ Instance [] tInt  (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) [])  (fieldSet [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@showInt")]))
--          , Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  (fieldSet [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")]))
----          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11])
--          , Instance [] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) (fieldSet [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_]))
--          ]
--        )
--      )
--    ]
--  where
--    showPair_ = lamExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "first", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (LString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "second", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])
--
--typeEnv :: TypeEnv
--typeEnv = Env.fromList 
--    [ ( "(==)"     , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
--    , ( "(+)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
--    , ( "(-)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
--    , ( "(*)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
--    , ( "show"     , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
--    , ( "add"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
--    , ( "(,)"      , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1)))
--    , ( "first"    , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 0))
--    , ( "second"   , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 1))
--    , ( "(::)"     , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
--    , ( "[]"       , Forall [kTyp] [] (tList (tGen 0)) )
--    , ( "length"   , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
--    , ( "None"     , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
--    , ( "Some"     , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
--    , ( "@Int.(+)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
--    , ( "@Int.(-)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
--    , ( "@Int.(*)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
--    , ( "const"    , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tGen 0) )
--    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
--    ]
--
----type InferenceStack a =
----    StateT (Substitution, Context) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a
----
----runInfer 
----  :: ClassEnv a 
----  -> TypeEnv 
----  -> InferenceStack a
----  -> Either String (a, (Substitution, Context))
--runInfer classEnv typeEnv = flip runStateT (mempty, mempty)
--    >>> flip runReaderT (classEnv, typeEnv)
--    >>> flip evalSupplyT (numSupply "a")
--    >>> runExceptT
--    >>> fromMaybe (Left "error")
--
----runTest :: Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] -> Either String (Ast NodeInfo)
----runTest expr = do
----    (ast, (sub, _)) <- runInfer classEnv typeEnv (infer expr)
----    pure (mapTags (apply sub) ast)
----
------result :: Expr -> Either e Scheme
------result expr = normalize . generalize mempty [] . fst <$> runTest expr
----
----result = undefined
----
----normalize = undefined
--
----succeedInferType :: Expr t p q r -> Scheme -> SpecWith ()
----succeedInferType expr expected =
----    describe ("The expression : " <> prettyString expr) $
----        it ("✔ has type " <> prettyString expected) $
----            result expr == Right (normalize expected)
--
----failInferTypeWithError :: e -> Expr -> SpecWith ()
----failInferTypeWithError err expr =
----    describe ("The expression : " <> prettyString expr) $
----        it ("✗ fails with error " <> show err) $
----            result expr == Left err
--
--runTestExpr expr = 
--    case runInfer classEnv typeEnv run of
--        Left e ->
--            error e
--        Right (ttree, (_, context)) ->
--            (pretty (typeOf ttree), context)
--  where
--    run = do
--        ast <- infer expr
--        sub <- gets fst
--        pure (mapTags (apply sub) ast)
--
--testExpr1 = letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", varPat () "b"] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () LUnit])
--
--testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
--
--testExpr3 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
--
--testExpr4 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])
--
--testExpr5 = lamExpr () [varPat () "x"] (letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
--
--testExpr6 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))
--
--testExpr7 = appExpr () [varExpr () "lenShow", litExpr () (LInt 555)]
--
--testExpr8 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])
--
--testExpr9 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
--
--testExpr10 = letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () LUnit])
--
--testExpr11 = letExpr () (BLet (varPat () "p")) (conExpr () "(,)" [litExpr () (LInt 5), litExpr () (LInt 1)]) (appExpr () [varExpr () "show", varExpr () "p"])
--
--testExpr12 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]])
--
---- TODO

testTypeInference :: SpecWith ()
testTypeInference = 
    pure ()

--testTypeInference :: SpecWith ()
--testTypeInference = do
--    pure ()
----    succeedInferType
----        $(parseExpr "let const = \\a => \\b => a in const ()")
----        $(parseScheme "forall a. a -> Unit")
--
