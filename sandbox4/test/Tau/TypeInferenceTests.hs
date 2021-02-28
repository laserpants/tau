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
import Test.Hspec
import Utils
import qualified Tau.Util.Env as Env

classEnv :: ClassEnv (Ast NodeInfo)
classEnv = Env.fromList 
    [ ( "Num"
      , ( []
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) (fieldSet 
              [ Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")
              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(*)Int")
              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(-)Int")
              ]))
          ] 
        )
      )
    , ( "Show"
      , ( []
        , [ Instance [] tInt  (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) [])  (fieldSet [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@showInt")]))
          , Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  (fieldSet [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")]))
--          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11])
--          , Instance [] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_])
          ]
        )
      )
    ]

typeEnv :: TypeEnv
typeEnv = Env.fromList 
    [ ( "(==)"     , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
    , ( "(+)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(-)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "show"     , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
    , ( "add"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(,)"      , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1)))
    , ( "first"    , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 0))
    , ( "second"   , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 1))
    , ( "(::)"     , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"       , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "length"   , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
    , ( "None"     , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"     , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
    , ( "@Int.(+)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(-)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(*)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "const"    , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tGen 0) )
    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
    ]

runInfer 
  :: ClassEnv a 
  -> TypeEnv 
  -> StateT Substitution (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 
  -> Either String (a, Substitution)
runInfer e1 e2 = flip runStateT mempty
    >>> flip runReaderT (e1, e2)
    >>> flip evalSupplyT (numSupply "a")
    >>> runExceptT
    >>> fromMaybe (Left "error")

runTest :: Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] -> Either String (Ast NodeInfo)
runTest expr = do
    (ast, sub) <- runInfer classEnv typeEnv (infer expr)
    pure (mapExprTags (apply sub) ast)

--result :: Expr -> Either e Scheme
--result expr = normalize . generalize mempty [] . fst <$> runTest expr

result = undefined

normalize = undefined

--succeedInferType :: Expr t p q r -> Scheme -> SpecWith ()
--succeedInferType expr expected =
--    describe ("The expression : " <> prettyString expr) $
--        it ("✔ has type " <> prettyString expected) $
--            result expr == Right (normalize expected)

--failInferTypeWithError :: e -> Expr -> SpecWith ()
--failInferTypeWithError err expr =
--    describe ("The expression : " <> prettyString expr) $
--        it ("✗ fails with error " <> show err) $
--            result expr == Left err

testExpr1 = letExpr () (BLet (varPat () "const")) (lamExpr () [varPat () "a", varPat () "b"] (varExpr () "a")) (appExpr () [varExpr () "const", litExpr () LUnit])

testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")

--expr2 = letPExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
--expr3 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])
--expr4 = lamExpr () [varPat () "x"] (letPExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
--expr5 = letPExpr () (varPat () "f") (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))
--expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 555)]
--expr7 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])
--expr1 = letPExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")

testTypeInference :: SpecWith ()
testTypeInference = do
    undefined
--    succeedInferType
--        $(parseExpr "let const = \\a => \\b => a in const ()")
--        $(parseScheme "forall a. a -> Unit")

