{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeInferenceTests where

import Tau.Env (Env(..))
import Tau.Expr
import Tau.Solver
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
        (arrT (varT "a") (arrT (appT (conT "List") (varT "a")) (appT (conT "List") (varT "a"))))
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
--    , ( "Baz"
--      , Forall [] []
--        tBool
--      )
--    , ( "(==)"
--      , Forall ["a"] [TyCl "Eq" (varT "a")]
--        (arrT (varT "a") (arrT (varT "a") tBool))
--      )
--    , ( "(+)"
--      , Forall ["a"] [TyCl "Num" (varT "a")]
--        (arrT (varT "a") (arrT (varT "a") (varT "a")))
--      )
    ]

runTest :: Expr -> Either TypeError (Type, [TyClass])
runTest expr = do
    (ty, sub, tycls) <- runInferType testTypeEnv expr
    pure (apply sub ty, apply sub <$> tycls)

succeedInferType :: Expr -> Scheme -> SpecWith ()
succeedInferType expr expected =
    describe ("The expression : " <> prettyString expr) $
        it ("✔ has type " <> prettyString expected) $
            got == Right (normalize expected)
  where
    got = normalize . generalize mempty [] . fst <$> runTest expr

testTypeInference :: SpecWith ()
testTypeInference = do
    succeedInferType
        (letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit]))
        (Forall ["a"] [] (varT "a" `arrT` tUnit))

    succeedInferType
        (appS [varS "const", litInt 5, litUnit])
        (Forall [] [] tInt)

    succeedInferType
        (appS [varS "foo", litInt 5])
        (Forall [] [] tInt)

    succeedInferType
        (appS [varS "Foo", litInt 5])
        (Forall [] [] (appT (conT "List") tInt))

    succeedInferType
        (lamS "a" (varS "a"))
        (Forall ["a"] [] (varT "a" `arrT` varT "a"))

    succeedInferType
        (lamS "a" (lamS "b" (varS "a")))
        (Forall ["a", "b"] [] (varT "a" `arrT` (varT "b" `arrT` varT "a")))

    succeedInferType
        (letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5]))
        (Forall [] [] tUnit)

    succeedInferType
        (appS [lamS "xs" (matchS (varS "xs") [ (conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2) ]), appS [varS "Cons", litInt 5, appS [varS "Nil"]]])
        (Forall [] [] tInt)

