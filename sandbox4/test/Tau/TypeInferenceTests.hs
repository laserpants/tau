{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeInferenceTests where

import Tau.Comp.Type.Inference
import Tau.Lang.Expr
import Tau.Lang.Type
import Test.Hspec
import Utils
import qualified Tau.Util.Env as Env

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
    ]

--runTest :: Expr -> Either e (Type, [TyClass])
--runTest expr = do
--    (ty, sub, tycls) <- runInferType testTypeEnv expr
--    pure (apply sub ty, apply sub <$> tycls)

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

