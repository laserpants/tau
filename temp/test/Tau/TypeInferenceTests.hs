{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeInferenceTests where

import Tau.Env (Env(..))
import Tau.Expr
import Tau.Type
import Tau.Type.Inference
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testTypeEnv :: Env Scheme
testTypeEnv = Env.fromList
    [ ( "concat"
      , Forall [] []
        (arrT tString (arrT tString tString))
      )
    , ( "show"
      , Forall ["a"] [TyCl "Show" (varT "a")]
        (arrT (varT "a") tString)
      )
    , ( "Nil"
      , Forall ["a"] []
        (appT (conT "List") (varT "a"))
      )
    , ( "Cons"
      , Forall ["a"] []
        (arrT (varT "a") (arrT (arrT (varT "a") tString) (arrT (varT "a") tString)))
      )
    , ( "const"
      , Forall ["a", "b"] []
        (arrT (varT "a") (arrT (varT "b") (varT "a")))
      )
    , ( "foo"
      , Forall ["a"] []
        (arrT (varT "a") (varT "a"))
      )
    , ( "Foo"
      , Forall ["a"] []
        (arrT (varT "a") (appT (conT "List") (varT "a")))
      )
    , ( "Baz"
      , Forall [] []
        tBool
      )
    , ( "Tuple2"
      , Forall ["a", "b"] []
        (arrT (varT "a") (arrT (varT "b") (appT (appT (conT "Tuple2") (varT "a")) (varT "b"))))
      )
    , ( "fst"
      , Forall ["a", "b"] []
        (arrT (appT (appT (conT "Tuple2") (varT "a")) (varT "b")) (varT "a"))
      )
    , ( "snd"
      , Forall ["a", "b"] []
        (arrT (appT (appT (conT "Tuple2") (varT "a")) (varT "b")) (varT "b"))
      )
    , ( "(==)"
      , Forall ["a"] [TyCl "Eq" (varT "a")]
        (arrT (varT "a") (arrT (varT "a") tBool))
      )
    , ( "(+)"
      , Forall ["a"] [TyCl "Num" (varT "a")]
        (arrT (varT "a") (arrT (varT "a") (varT "a")))
      )
    ]

runTest :: Expr -> Either TypeError (Type, [TyClass])
runTest expr = do
    (ty, sub, tycls) <- runInferType testTypeEnv expr
    pure (apply sub ty, apply sub <$> tycls)

succeedInferType :: Expr -> Type -> SpecWith ()
succeedInferType expr expected =
    describe ("The expression : " <> prettyString expr) $
        it ("✔ has type " <> prettyString expected) $
            (fst <$> runTest expr) == Right expected

testTypeInference :: SpecWith ()
testTypeInference = do
    succeedInferType 
        (letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit]))
        (varT "a7" `arrT` tUnit)
        --(Forall ["a"] [] (varT "a" `arrT` tUnit))

    pure ()
