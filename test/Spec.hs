{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
import Test.Hspec

import Control.Monad
import Data.Functor.Const
import Data.Functor.Foldable
import Data.List (intersperse, find, delete, nub, elemIndex)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text, pack, unpack)
import Debug.Trace
import Tau.Env (Env(..))
import Tau.Juice
import Tau.Parser
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

main :: IO ()
main =
    hspec $ do
        describe "Eval" testEval
        describe "Infer" testInfer
        describe "Infer Kinds" testInferKinds
        describe "Pattern Check" testPatternCheck
        describe "Unify" testUnify
        describe "Substitute" testSubstitute
        describe "Type Classes" testTypeClasses
        describe "PatternCompile" testPatternCompile
        describe "Parser" testParser

typeInferTestExpr :: Expr
typeInferTestExpr = lamS "a" (appS [varS "concat", appS [varS "show", varS "a"], litString "..."])

typeInferTestExpr2 :: Expr
typeInferTestExpr2 = lamS "a" (lamS "b" (appS [varS "(==)", varS "a", varS "b"]))

listA :: Type
listA = appT (conT "List") (varT "a")

tuple2AB :: Type
tuple2AB = appT (appT (conT "Tuple2") (varT "a")) (varT "b")

testContext :: Env Scheme
testContext = Env (Map.fromList
    [ ("concat" , Forall []         [] (arrT tString (arrT tString tString)))
    , ("show"   , Forall ["a"] [Class "Show" (varT "a")]
                                       (arrT (varT "a") tString))
    , ("Nil"    , Forall ["a"]      [] listA)
    , ("Cons"   , Forall ["a"]      [] (arrT (varT "a") (arrT listA listA)))
    , ("const"  , Forall ["a", "b"] [] (arrT (varT "a") (arrT (varT "b") (varT "a"))))
    , ("foo"    , Forall ["a"]      [] (arrT (varT "a") (varT "a")))
    , ("Foo"    , Forall ["a"]      [] (arrT (varT "a") (appT (conT "List") (varT "a"))))
    , ("Baz"    , Forall []         [] tBool)
    , ("Tuple2" , Forall ["a", "b"] [] (arrT (varT "a") (arrT (varT "b") tuple2AB)))
    , ("fst"    , Forall ["a", "b"] [] (arrT tuple2AB (varT "a")))
    , ("snd"    , Forall ["a", "b"] [] (arrT tuple2AB (varT "b")))
    , ("(==)"   , Forall ["a"] [Class "Eq" (varT "a")] (arrT (varT "a") (arrT (varT "a") tBool)))
    , ("(+)"    , Forall ["a"] [Class "Num" (varT "a")] (arrT (varT "a") (arrT (varT "a") (varT "a"))))
    --, ("(+)"    , Forall [] [] (arrT (conT "Int") (arrT (conT "Int") (conT "Int"))))
    ])

-- ========================
-- ==== TestInferKinds ====
-- ========================

-- State a Int
test010 :: [KindConstraint]
test010 =
  [ (varK "1", arrowK (varK "2") (varK "3"))
  , (varK "3", arrowK starK (varK "4"))
  , (varK "1", arrowK starK (arrowK starK starK))
  ]

-- List a
test020 :: Type
test020 = appT (conT "List") (varT "a")

-- State a Int
test030 :: Type
test030 = appT (appT (conT "State") (varT "a")) (conT "Int")

-- m a
test040 :: Type
test040 = appT (varT "m") (varT "a")

-- List a -> List Int
test050 :: Type
test050 = arrT (appT (conT "List") (varT "a")) (appT (conT "List") (conT "Int"))

-- List
test060 :: Type
test060 = conT "List"

testInferKinds :: SpecWith ()
testInferKinds = do
    kindInferTestSuccess
        (test020, testKindContext) starK "test020"

    kindInferTestSuccess
        (test030, testKindContext) starK "test030"

    kindInferTestSuccess
        (test040, testKindContext) starK "test040"

    kindInferTestSuccess
        (test050, testKindContext) starK "test050"

    kindInferTestSuccess
        (test060, testKindContext) (arrowK starK starK) "test060"

kindInferTestSuccess :: (Type, Env Kind) -> Kind -> Text -> SpecWith ()
kindInferTestSuccess (ty, context) kind name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyType ty

    describeSuccess = unpack $
        "✔ has kind : " <> prettyKind kind

    describeFailure = unpack $
        "Expected kind to be : " <> prettyKind kind

    test = case runInferK (inferKind testKindContext ty) of
        Nothing ->
            expectationFailure describeFailure

        _ ->
            pass

kindInferRunTest :: Env Kind -> Type -> Maybe Kind
kindInferRunTest context ty = runInferK (inferKind testKindContext ty)

testKindContext :: Env Kind
testKindContext = Env (Map.fromList
    [ ("List"  , (arrowK starK starK))
    , ("State" , arrowK starK (arrowK starK starK) )
    ])

-- ===================
-- ==== TestInfer ====
-- ===================

typeInferTest010 :: Expr
typeInferTest010 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit])

typeInferTest011 :: Expr
typeInferTest011 = appS [varS "const", litInt 5, litUnit]

typeInferTest012 :: Expr
typeInferTest012 = appS [varS "foo", litInt 5]

typeInferTest013 :: Expr
typeInferTest013 = appS [varS "Foo", litInt 5]

typeInferTest014 :: Expr
typeInferTest014 = lamS "a" (varS "a")

typeInferTest015 :: Expr
typeInferTest015 = lamS "a" (lamS "b" (varS "a"))

typeInferTest020 :: Expr
typeInferTest020 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5])

typeInferTest030 :: Expr
typeInferTest030 = appS [lamS "xs" (matchS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses =
        [ (conP "Cons" [varP "y", varP "ys"], litInt 1)
        , (conP "Nil" [], litInt 2) ]

-- (\xs -> match xs with | _ => 1) (Cons 5 Nil)
typeInferTest031 :: Expr
typeInferTest031 = appS [lamS "xs" (matchS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (anyP, litInt 1) ]

-- (\xs -> match xs with | x => 1) (Cons 5 Nil)
typeInferTest032 :: Expr
typeInferTest032 = appS [lamS "xs" (matchS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (varP "x", litInt 1) ]

-- (\xs -> match xs with | Cons y ys => 1) (Cons 5 Nil)
typeInferTest033 :: Expr
typeInferTest033 = appS [lamS "xs" (matchS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (conP "Cons" [varP "y", varP "ys"], litInt 1) ]

typeInferTest034 :: Expr
typeInferTest034 = letS "xs" (appS [varS "Baz"]) (matchS (varS "xs") [ (conP "Baz" [], litString "hello")])

typeInferTest040 :: Expr
typeInferTest040 = appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]]

typeInferTest041 :: Expr
typeInferTest041 = appS [varS "Cons", litInt 5]

typeInferTest042 :: Expr
typeInferTest042 = appS [varS "Cons", litInt 5, appS [varS "Nil"]]

typeInferTest043 :: Expr
typeInferTest043 = appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]

typeInferTest044 :: Expr
typeInferTest044 = appS [varS "Cons", litInt 5, appS [varS "Cons", litBool True, appS [varS "Nil"]]]

-- match Cons 5 Nil with | Cons y ys -> y + 1 | Nil -> 0
typeInferTest050 :: Expr
typeInferTest050 = matchS (appS [varS "Cons", litInt 5, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Nil" [], litInt 0)]

-- match Cons "a" Nil with | Cons y ys -> y + 1
typeInferTest053 :: Expr
typeInferTest053 = matchS (appS [varS "Cons", litString "a", appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

-- match Cons 6 Nil with | Cons y ys -> y + 1
typeInferTest054 :: Expr
typeInferTest054 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

typeInferTest055 :: Expr
typeInferTest055 = letS "xs" (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (letS "ys" (appS [varS "Cons", litInt 1, appS [varS "Nil"]]) (litInt 5))

-- match Cons 6 Nil with | Cons y ys -> y + 1 | Cons 4 ys -> 5
typeInferTest056 :: Expr
typeInferTest056 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Cons" [litP (Int 4), varP "ys"], litInt 5)]

-- match Cons 6 Nil with | Cons y ys -> y + 1 | Cons 4 ys -> "foo"
typeInferTest057 :: Expr
typeInferTest057 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (Int 4), varP "ys"], litString "foo") ]

-- match Cons 6 Nil with | Cons y ys -> y + 1 | 5 -> 1
typeInferTest058 :: Expr
typeInferTest058 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (litP (Int 5), litInt 1) ]

-- match Cons 6 Nil with | Cons y ys -> y + 1 | Cons "w" z -> 1
typeInferTest059 :: Expr
typeInferTest059 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (String "w"), varP "z"], litInt 1) ]

-- match Cons 6 Nil with | Cons y ys -> y + 1 | Cons z 5 -> 1
typeInferTest060 :: Expr
typeInferTest060 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [varP "z", litP (Int 5)], litInt 1) ]

-- match Cons 6 Nil with | Cons y ys -> "one" | _ -> "two"
typeInferTest061 :: Expr
typeInferTest061 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], litString "one")
    , (anyP, litString "two") ]

-- match Cons 6 Nil with | Cons y ys -> y | _ -> "two"
typeInferTest062 :: Expr
typeInferTest062 = matchS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], varS "y")
    , (anyP, litString "two") ]

-- match Nil with []
typeInferTest063 :: Expr
typeInferTest063 = matchS (appS [varS "Nil"]) []

-- if 1 == True then 1 else 0
typeInferTest070 :: Expr
typeInferTest070 = ifS (eqS (litInt 1) (litBool True)) (litInt 1) (litInt 0)

-- if Cons True Nil == Cons 1 Nil then 1 else 0
typeInferTest075 :: Expr
typeInferTest075 = ifS (eqS (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (appS [varS "Cons", litInt 1, appS [varS "Nil"]])) (litInt 1) (litInt 0)

typeInferTest080 :: Expr
typeInferTest080 = letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]])))

-- let id = \x -> x in let x = (id, 4) in (fst x) (snd x) + 1
typeInferTest090 :: Expr
typeInferTest090 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1)))

typeInferTest100 :: Expr
typeInferTest100 = letS "x" (varS "x") (varS "x")

typeInferTest110 :: Expr
typeInferTest110 = letS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

typeInferTest115 :: Expr
typeInferTest115 = recS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

typeInferTest130 :: Expr
typeInferTest130 = appS [lamS "x" (matchS (varS "x") [(litP (Int 1), litInt 2), (litP (Int 2), litInt 3)]), litInt 1]

testInfer :: SpecWith ()
testInfer = do
    typeInferTestSuccess
        (typeInferTest010, Env mempty)
        (Forall ["a"] [] (varT "a" `arrT` tUnit))
        "test010"

    typeInferTestFailure
        (typeInferTest010, Env mempty)
        (Forall ["a"] [] (varT "a" `arrT` tInt))
        "test010"

    typeInferTestSuccess
        (typeInferTest011, testContext) (Forall [] [] tInt) "test011"

    typeInferTestFailure
        (typeInferTest011, testContext) (Forall [] [] tBool) "test011"

    typeInferTestSuccess
        (typeInferTest012, testContext) (Forall [] [] tInt) "test012"

    typeInferTestSuccess
        (typeInferTest013, testContext) (Forall [] [] (appT (conT "List") tInt)) "test013"

    typeInferTestFailure
        (typeInferTest013, testContext) (Forall [] [] (appT (conT "List") (varT "a"))) "test013"

    typeInferTestSuccess
        (typeInferTest014, Env mempty) (Forall ["a"] [] (varT "a" `arrT` varT "a")) "test014"

    typeInferTestSuccess
        (typeInferTest015, Env mempty) (Forall ["a", "b"] [] (varT "a" `arrT` (varT "b" `arrT` varT "a"))) "test015"

    typeInferTestFailure
        (typeInferTest015, Env mempty) (Forall ["a", "b"] [] (varT "a" `arrT` (varT "b" `arrT` varT "b"))) "test015"

    typeInferTestFailure
        (typeInferTest015, Env mempty) (Forall ["a", "b"] [] (varT "b" `arrT` (varT "b" `arrT` varT "a"))) "test015"

    typeInferTestSuccess
        (typeInferTest020, testContext) (Forall [] [] tUnit) "test020"

    typeInferTestSuccess
        (typeInferTest030, testContext) (Forall [] [] tInt) "test030"

    typeInferTestSuccess
        (typeInferTest031, testContext) (Forall [] [] tInt) "test031"

    typeInferTestSuccess
        (typeInferTest032, testContext) (Forall [] [] tInt) "test032"

    typeInferTestSuccess
        (typeInferTest033, testContext) (Forall [] [] tInt) "test033"

    typeInferTestSuccess
        (typeInferTest034, testContext) (Forall [] [] tString) "test034"

    typeInferTestFailWithError
        (typeInferTest053, testContext) CannotUnify "test053"

    typeInferTestSuccess
        (typeInferTest054, testContext) (Forall [] [] tInt) "test054"

    typeInferTestSuccess
        (typeInferTest055, testContext) (Forall [] [] tInt) "test055"

    typeInferTestSuccess
        (typeInferTest056, testContext) (Forall [] [] tInt) "test056"

    typeInferTestFailWithError
        (typeInferTest057, testContext) CannotUnify "test057"

    typeInferTestFailWithError
        (typeInferTest058, testContext) CannotUnify "test058"

    typeInferTestFailWithError
        (typeInferTest059, testContext) CannotUnify "test059"

    typeInferTestFailWithError
        (typeInferTest060, testContext) CannotUnify "test060"

    typeInferTestSuccess
        (typeInferTest061, testContext) (Forall [] [] tString) "test061"

    typeInferTestFailWithError
        (typeInferTest062, testContext) CannotUnify "test062"

    typeInferTestFailWithError
        (typeInferTest063, testContext) EmptyMatchStatement "test063"

    typeInferTestFailWithError
        (typeInferTest070, testContext) CannotUnify "test070"

    typeInferTestFailWithError
        (typeInferTest075, testContext) CannotUnify "test075"

    typeInferTestSuccess
        (typeInferTest080, testContext) (Forall [] [] tInt) "test080"

    typeInferTestSuccess
        (typeInferTest090, testContext) (Forall [] [] tInt) "test090"

    typeInferTestFailWithError
        (typeInferTest100, testContext) (UnboundVariable "x") "test100"

    typeInferTestFailWithError
        (typeInferTest110, testContext) (UnboundVariable "f") "test110"

    typeInferTestSuccess
        (typeInferTest115, testContext) (Forall [] [] tInt) "test115"

    typeInferTestSuccess
        (typeInferTest130, testContext) (Forall [] [] tInt) "test130"

typeInferTestSuccess :: (Expr, Env Scheme) -> Scheme -> Text -> SpecWith ()
typeInferTestSuccess (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = unpack $
        "✔ has type : "
            <> prettyScheme ty

    describeFailure = unpack $
        "Expected type to be identical to : "
            <> prettyScheme ty
            <> " (up to isomorphism)"

    test = case typeInferRunTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            pass

        t ->
            expectationFailure describeFailure

typeInferTestFailure :: (Expr, Env Scheme) -> Scheme -> Text -> SpecWith ()
typeInferTestFailure (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = unpack $
        "✗ does not have type : "
            <> prettyScheme ty

    describeFailure = unpack $
        "Expected type NOT to be identical to : "
            <> prettyScheme ty

    test = case typeInferRunTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            expectationFailure describeFailure

        _ ->
            pass

typeInferTestFailWithError :: (Expr, Env Scheme) -> TypeError -> Text -> SpecWith ()
typeInferTestFailWithError (expr, context) err name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = "✗ fails with error " <> show err

    test = case typeInferRunTest context expr of
        Left e | err == e ->
            pass

        _ ->
            expectationFailure ("Expected test to fail with error " <> show err)

typeInferRunTest :: Env Scheme -> Expr -> Either TypeError Scheme
typeInferRunTest context expr = getAnnotation <$> runInfer (inferType context expr)

-- ==========================
-- ==== TestPatternCheck ====
-- ==========================

patternCheckTestConstructors :: ConstructorEnv
patternCheckTestConstructors = constructorEnv
    [ ("Nil",  ["Nil", "Cons"])
    , ("Cons", ["Nil", "Cons"])
    ]

patternCheckTest010 :: [Pattern]
patternCheckTest010 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    , conP "Cons" [varP "z", varP "zs"]
    ]
    -- True

patternCheckTest020 :: [Pattern]
patternCheckTest020 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    , conP "Cons" [varP "z", conP "Nil" []]
    ]

patternCheckTest030 :: [Pattern]
patternCheckTest030 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    ]
    -- False

patternCheckTest040 :: [Pattern]
patternCheckTest040 =
    [ conP "Nil" []
    ]
    -- False

patternCheckTest050 :: [Pattern]
patternCheckTest050 =
    [ anyP
    ]
    -- True

patternCheckTest060 :: [Pattern]
patternCheckTest060 =
    [ conP "Cons" [varP "x", varP "ys"]
    , conP "Nil" []
    ]
    -- True

patternCheckTest070 :: [Pattern]
patternCheckTest070 =
    [ conP "Cons" [varP "x", varP "ys"]
    , varP "x"
    ]
    -- True

patternCheckTest080 :: ([Pattern], Pattern)
patternCheckTest080 =
    ( [ conP "Cons" [varP "x", varP "ys"]
      , varP "x" ]
    , conP "Nil" [] )
    -- False

patternCheckTest090 :: ([Pattern], Pattern)
patternCheckTest090 =
    ( [ conP "Cons" [varP "x", varP "ys"]
      , varP "x"
      , conP "Nil" [] ]
    , conP "Nil" [] )
    -- False

patternCheckTest100 :: ([Pattern], Pattern)
patternCheckTest100 =
    ( [ conP "Cons" [varP "x", varP "ys"] ]
    , conP "Nil" [] )
    -- True

patternCheckTest110 :: [Pattern]
patternCheckTest110 =
    [ litP (Int 5)
    , varP "x"
    ]

patternCheckTest120 :: [Pattern]
patternCheckTest120 =
    [ litP (Int 5)
    , litP (Int 4)
    ]

patternCheckTest130 :: [Pattern]
patternCheckTest130 =
    [ litP (Bool True)
    , litP (Bool False)
    ]

patternCheckTest135 :: [Pattern]
patternCheckTest135 =
    [ litP (Bool True)
    , anyP
    ]

patternCheckTest140 :: [Pattern]
patternCheckTest140 =
    [ litP (Bool True)
    ]

patternCheckTest150 :: [Pattern]
patternCheckTest150 =
    [ litP Unit
    ]

patternCheckTest160 :: [Pattern]
patternCheckTest160 =
    [ litP (String "x")
    , litP (String "y")
    ]

patternCheckTest170 :: [Pattern]
patternCheckTest170 =
    [ litP (String "x")
    , litP (String "y")
    , anyP
    ]

testPatternCheck :: SpecWith ()
testPatternCheck = do
    patternCheckTestIsExhaustive  patternCheckTest010 "test010"
    patternCheckTestIsExhaustive  patternCheckTest020 "test020"
    patternCheckTestNotExhaustive patternCheckTest030 "test030"
    patternCheckTestNotExhaustive patternCheckTest040 "test040"
    patternCheckTestIsExhaustive  patternCheckTest050 "test050"
    patternCheckTestIsExhaustive  patternCheckTest060 "test060"
    patternCheckTestIsExhaustive  patternCheckTest070 "test070"
    patternCheckTestNotUseful     patternCheckTest080 "test080"
    patternCheckTestNotUseful     patternCheckTest090 "test090"
    patternCheckTestIsUseful      patternCheckTest100 "test100"
    patternCheckTestIsExhaustive  patternCheckTest110 "test110"
    patternCheckTestNotExhaustive patternCheckTest120 "test120"
    patternCheckTestIsExhaustive  patternCheckTest130 "test130"
    patternCheckTestIsExhaustive  patternCheckTest135 "test135"
    patternCheckTestNotExhaustive patternCheckTest140 "test140"
    patternCheckTestIsExhaustive  patternCheckTest150 "test150"
    patternCheckTestNotExhaustive patternCheckTest160 "test160"
    patternCheckTestIsExhaustive  patternCheckTest170 "test170"

patternCheckTestIsExhaustive :: [Pattern] -> Text -> SpecWith ()
patternCheckTestIsExhaustive pttrns name =
    describe description (it describeSuccess patternCheckTest)
  where
    description = unpack $
        name <> ": " <> prettyPatterns pttrns

    describeSuccess = unpack "✔ is exhaustive"

    describeFailure = unpack
        "Expected exhaustive check to return True"

    patternCheckTest =
        if patternCheckRunExhaustiveTest pttrns
            then pass
            else expectationFailure describeFailure

patternCheckTestNotExhaustive :: [Pattern] -> Text -> SpecWith ()
patternCheckTestNotExhaustive pttrns name =
    describe description (it describeSuccess patternCheckTest)
  where
    description = unpack $
        name <> ": " <> prettyPatterns pttrns

    describeSuccess = unpack "✗ is NOT exhaustive"

    describeFailure = unpack
        "Expected exhaustive check to return False"

    patternCheckTest =
        if patternCheckRunExhaustiveTest pttrns
            then expectationFailure describeFailure
            else pass

patternCheckRunExhaustiveTest :: [Pattern] -> Bool
patternCheckRunExhaustiveTest pttrns = runPatternCheck (exhaustive pttrns) patternCheckTestConstructors

patternCheckTestNotUseful :: ([Pattern], Pattern) -> Text -> SpecWith ()
patternCheckTestNotUseful pair name =
    describe description (it describeSuccess patternCheckTest)
  where
    description = unpack (name <> ": " <> prettyPatterns (fst pair))

    describeSuccess = unpack $
        "✗ clause " <> prettyPattern (snd pair)
                    <> " is NOT useful"

    describeFailure = unpack
        "Expected useful check to return False"

    patternCheckTest =
        if patternCheckRunInUsefulTest pair
            then expectationFailure describeFailure
            else pass

patternCheckTestIsUseful :: ([Pattern], Pattern) -> Text -> SpecWith ()
patternCheckTestIsUseful pair name =
    describe description (it describeSuccess patternCheckTest)
  where
    description = unpack (name <> ": " <> prettyPatterns (fst pair))

    describeSuccess = unpack $
        "✔ clause " <> prettyPattern (snd pair)
                    <> " is useful"

    describeFailure = unpack
        "Expected useful check to return True"

    patternCheckTest =
        if patternCheckRunInUsefulTest pair
            then pass
            else expectationFailure describeFailure

patternCheckRunInUsefulTest :: ([Pattern], Pattern) -> Bool
patternCheckRunInUsefulTest (ps, p) =
    runPatternCheck (uncurry useful (fmap (:[]) ps, [p])) patternCheckTestConstructors

-- ==================
-- ==== TestEval ====
-- ==================

-- \a -> \b -> a
evalTest000 :: Expr
evalTest000 = lamS "a" (lamS "b" (varS "a"))

-- let const = \a -> \b -> a in const ()
-- <<function>>
evalTest010 :: Expr
evalTest010 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit])

-- let const = \a -> \b -> a in const () 5
-- ()
evalTest020 :: Expr
evalTest020 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5])

-- (\xs -> case xs of { Cons y ys -> 1; Nil -> 2 }) (Cons 5 Nil)
-- 1
evalTest030 :: Expr
evalTest030 = appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]

-- (\xs -> case xs of { Cons y ys -> 1; Nil -> 2 }) Nil
-- 2
evalTest040 :: Expr
evalTest040 = appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]]

-- let plus = \a -> \b -> a + b in let plus5 = plus 5 in let id = \x -> x in (id plus5) (id 3)
-- 8
evalTest050 :: Expr
evalTest050 = letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]])))

-- let id = \x -> x in let x = (id, 4) in (fst x) (snd x) + 1
-- 5
evalTest060 :: Expr
evalTest060 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1)))

-- let id = \x -> x in let x = (id, 4) in (fst x)
-- <<function>>
evalTest070 :: Expr
evalTest070 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (appS [varS "fst", varS "x"]))

evalTest080 :: Expr
evalTest080 = letS "x" (varS "x") (varS "x")

evalTest110 :: Expr
evalTest110 = letS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

evalTest115 :: Expr
evalTest115 = recS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

evalTest120 :: Expr
evalTest120 = varS "hello"

evalTest130 :: Expr
evalTest130 = compileAll $ appS [lamS "x" (matchS (varS "x") [(litP (Int 1), litInt 2), (litP (Int 2), litInt 3)]), litInt 1]

evalTest140 :: Expr
evalTest140 = letS "f" (lamS "n" (ifS (eqS (varS "n") (litInt 0)) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

evalTest150 :: Expr
evalTest150 = recS "f" (lamS "n" (ifS (eqS (varS "n") (litInt 0)) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5])

testEval :: SpecWith ()
testEval = do
    evalTestIsFunction evalTest000               "test000"
    evalTestIsFunction evalTest010               "test010"
    evalTestEvalsTo (evalTest020, Value Unit)    "test020"
    evalTestEvalsTo (evalTest030, Value (Int 1)) "test030"
    evalTestEvalsTo (evalTest040, Value (Int 2)) "test040"
    evalTestEvalsTo (evalTest050, Value (Int 8)) "test050"
    evalTestEvalsTo (evalTest060, Value (Int 5)) "test060"
    evalTestIsFunction evalTest070               "test070"
    evalTestFailsWithError (evalTest080, UnboundIdentifier "x") "test080"
    evalTestFailsWithError (evalTest110, UnboundIdentifier "f") "test110"
    evalTestEvalsTo (evalTest115, Value (Int 120)) "test115"
    evalTestFailsWithError (evalTest120, UnboundIdentifier "hello") "test120"
    evalTestEvalsTo (evalTest130, Value (Int 2)) "test130"
    evalTestFailsWithError (evalTest140, UnboundIdentifier "f") "test140"
    evalTestEvalsTo (evalTest150, Value (Int 120)) "test150"

evalTestFailsWithError :: (Expr, EvalError) -> Name -> SpecWith ()
evalTestFailsWithError (expr, err) name =
    describe description (it describeSuccess evalTest)
  where
    description = unpack $ name <> ": " <> prettyExpr expr

    describeSuccess = unpack "✗ fails with error " <> show err

    evalTest = case evalRunTest expr of
        Left err' | err' == err ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right{} ->
            expectationFailure ("Expected evaluation to fail with " <> show err)

evalTestIsFunction :: Expr -> Text -> SpecWith ()
evalTestIsFunction expr name =
    describe description (it describeSuccess evalTest)
  where
    description = unpack $ name <> ": " <> prettyExpr expr

    describeSuccess = unpack "✔ is a function"

    evalTest = case evalRunTest expr of
        Right Closure{} ->
            pass

        Right result ->
            expectationFailure $ unpack ("Unexpected result: " <> prettyValue result)

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

evalTestEvalsTo :: (Expr, Value Eval) -> Text -> SpecWith ()
evalTestEvalsTo (expr, val) name =
    describe description (it describeSuccess evalTest)
  where
    description = unpack $ name <> ": " <> prettyExpr expr

    describeSuccess = unpack $ "✔ evaluates to " <> prettyValue val

    evalTest = case (evalRunTest expr, val) of
        (Left err, _) ->
            expectationFailure ("Unexpected error: " <> show err)

        (Right (Value v1), Value v2) | v1 == v2 ->
            pass

        (Right result, _) ->
            expectationFailure $ unpack ("Unexpected result: " <> prettyValue result)

evalE :: Expr -> Value Eval
evalE expr = result where Right result = evalExpr expr mempty

evalTestEnv :: EvalEnv Eval
evalTestEnv = Env.fromList
    [ ("Cons"   , dataCon "Cons" 2)
    , ("Nil"    , dataCon "Nil" 0)
    , ("Tuple2" , dataCon "Tuple2" 2)
                  -- \p -> case p of Tuple2 a b => a
    , ("fst"    , evalE (lamS "p" (matchS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "a")])))
                  -- \p -> case p of Tuple2 a b => b
    , ("snd"    , evalE (lamS "p" (matchS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "b")])))
    ]

evalRunTest :: Expr -> Either EvalError (Value Eval)
evalRunTest = flip evalExpr evalTestEnv

-- =========================
-- ==== TestUnification ====
-- =========================

uniTest010 :: (Type, Type)
uniTest010 =
    ( arrT (varT "a") (varT "b")                     -- a -> b
    , arrT tInt tInt                                 -- Int -> Int
    )

uniTest020 :: (Type, Type)
uniTest020 =
    ( arrT (varT "a") (varT "a")                     -- a -> a
    , arrT tInt tBool                                -- Int -> Bool
    )

uniTest030 :: (Type, Type)
uniTest030 =
    ( arrT (varT "a") (varT "a")                     -- a -> a
    , arrT tInt tInt                                 -- Int -> Int
    )

uniTest040 :: (Type, Type)
uniTest040 =
    ( arrT (varT "a") (arrT (varT "b") (varT "a"))   -- a -> (b -> a)
    , arrT (varT "a") (arrT tInt (varT "a"))         -- a -> (Int -> a)
    )

uniTest041 :: (Type, Type)
uniTest041 =
    ( arrT (varT "a") (arrT (varT "b") (varT "a"))   -- a -> (b -> a)
    , arrT (varT "a") (arrT tInt (varT "b"))         -- a -> (Int -> b)
    )

uniTest042 :: (Type, Type)
uniTest042 =
    ( arrT (varT "a") (arrT (varT "b") (varT "a"))   -- a -> (b -> a)
    , arrT tInt (arrT tInt tBool)                    -- Int -> (Int -> Bool)
    )

uniTest050 :: (Type, Type)
uniTest050 =
    ( appT (conT "List") (varT "a")                  -- List a
    , appT (conT "List") tInt                        -- List Int
    )

uniTest060 :: (Type, Type)
uniTest060 =
    ( appT (conT "List") (varT "a")                  -- List a
    , tInt                                           -- Int
    )

testUnify :: SpecWith ()
testUnify = do
    uniTestSuccess uniTest010 "test010"
    uniTestFailure uniTest020 "test020"
    uniTestSuccess uniTest030 "test030"
    uniTestSuccess uniTest040 "test040"
    uniTestSuccess uniTest041 "test041"
    uniTestFailure uniTest042 "test042"
    uniTestSuccess uniTest050 "test050"
    uniTestFailure uniTest060 "test060"

shouldUnify :: (Type, Type) -> Expectation
shouldUnify (t1, t2) =
    case runInfer (unify t1 t2) of
        Left{} ->
            expectationFailure "Unification failed"

        Right sub ->
            if apply sub t1 == apply sub t2 then
                pass

            else
                expectationFailure "Substitution does not yield equal types"

shouldFailToUnify :: (Type, Type) -> Expectation
shouldFailToUnify (t1, t2) =
    case runInfer (unify t1 t2) of
        Left{} ->
            pass

        Right{} ->
            expectationFailure "Expected unification to fail"

describeUniTest
    :: ((Type, Type) -> Expectation)
    -> String
    -> (Type, Type)
    -> Text
    -> SpecWith ()
describeUniTest test outcome (t1, t2) name =
    describe description $
        it outcome $ test (t1, t2)
  where
    description = unpack $
        name <> ": The types \n"
             <> "    " <> prettyType t1
             <> "\n    - and -\n    " <> prettyType t2

uniTestSuccess, uniTestFailure :: (Type, Type) -> Text -> SpecWith ()
uniTestSuccess = describeUniTest shouldUnify "✔ should unify"
uniTestFailure = describeUniTest shouldFailToUnify "✗ should not unify"

-- ========================
-- ==== TestSubstitute ====
-- ========================

-- let x = 3 in x [x := y]  ==>  let x = 3 in x
substTest000 =
    ( letS "x" (litInt 3) (varS "x")
    , ("x", varS "y")
    , letS "x" (litInt 3) (varS "x") )

-- let z = 3 in x [x := y]  ==>  let z = 3 in y
substTest010 =
    ( letS "z" (litInt 3) (varS "x")
    , ("x", varS "y")
    , letS "z" (litInt 3) (varS "y") )

-- let x = 3 in x + 5 [x := y]  ==>  let x = 3 in x + 5
substTest020 =
    ( letS "x" (litInt 3) (addS (varS "x") (litInt 5))
    , ("x", varS "y")
    , letS "x" (litInt 3) (addS (varS "x") (litInt 5)) )

-- let y = 3 in x + 5 [x := 8]  ==>  let y = 3 in 8 + 5
substTest030 =
    ( letS "y" (litInt 3) (addS (varS "x") (litInt 5))
    , ("x", litInt 8)
    , letS "y" (litInt 3) (addS (litInt 8) (litInt 5)) )

-- let y = x + 3 in 45 [x := 2]  ==>  let y = 2 + 3 in 45
substTest040 =
    ( letS "y" (addS (varS "x") (litInt 3)) (litInt 45)
    , ("x", litInt 2)
    , letS "y" (addS (litInt 2) (litInt 3)) (litInt 45) )

-- let x = x + 3 in 45 [x := 2]  ==>  let x = x + 3 in 45
substTest050 =
    ( letS "x" (addS (varS "x") (litInt 3)) (litInt 45)
    , ("x", litInt 2)
    , letS "x" (addS (varS "x") (litInt 3)) (litInt 45) )

-- let x = 3 in let y = x + 1 in 45 [x := 2]  ==>  let x = 3 in let y = x + 1 in 45
substTest060 =
    ( letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45))
    , ("x", litInt 2)
    , letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45)) )

-- let x = 3 in let y = z + 1 in 45 [z := 2]  ==>  let x = 3 in let y = 2 + 1 in 45
substTest070 =
    ( letS "x" (litInt 3) (letS "y" (addS (varS "z") (litInt 1)) (litInt 45))
    , ("z", litInt 2)
    , letS "x" (litInt 3) (letS "y" (addS (litInt 2) (litInt 1)) (litInt 45)) )

-- case xs of { x => 5 } [ x := 123 ]
substTest080 =
    ( matchS (varS "xs") [(varP "x", litInt 5)]
    , ("x", litInt 123)
    , matchS (varS "xs") [(varP "x", litInt 5)] )

-- case xs of { x => x } [ x := 123 ]
substTest085 =
    ( matchS (varS "xs") [(varP "x", varS "x")]
    , ("x", litInt 123)
    , matchS (varS "xs") [(varP "x", varS "x")] )

-- case xs of { y => x } [ x := 123 ]
substTest090 =
    ( matchS (varS "xs") [(varP "y", varS "x")]
    , ("x", litInt 123)
    , matchS (varS "xs") [(varP "y", litInt 123)] )

-- case xs of { Cons x xs => x } [ x := 123 ]
substTest100 =
    ( matchS (varS "xs") [(conP "Cons" [varP "x", varP "xs"], varS "x")]
    , ("x", litInt 123)
    , matchS (varS "xs") [(conP "Cons" [varP "x", varP "xs"], varS "x")] )

-- case xs of { Cons y xs => x } [ x := 123 ]
substTest110 =
    ( matchS (varS "xs") [(conP "Cons" [varP "y", varP "xs"], varS "x")]
    , ("x", litInt 123)
    , matchS (varS "xs") [(conP "Cons" [varP "y", varP "xs"], litInt 123)] )

-- case x of { _ => x } [ x := 123 ]
substTest120 =
    ( matchS (varS "x") [(anyP, varS "x")]
    , ("x", litInt 123)
    , matchS (litInt 123) [(anyP, litInt 123)] )

testSubstitute :: SpecWith ()
testSubstitute = do
    testSubst substTest010 "test010"
    testSubst substTest020 "test020"
    testSubst substTest030 "test030"
    testSubst substTest040 "test040"
    testSubst substTest050 "test050"
    testSubst substTest060 "test060"
    testSubst substTest070 "test070"
    testSubst substTest080 "test080"
    testSubst substTest085 "test085"
    testSubst substTest090 "test090"
    testSubst substTest100 "test100"
    testSubst substTest110 "test110"
    testSubst substTest120 "test120"

testSubst :: (Expr, (Name, Expr), Expr) -> Text -> SpecWith ()
testSubst (body, (var, expr), expected) name =
    describe description (it describeSuccess test)
  where
    description = unpack
        ( name <> ": "
               <> prettyExpr body
               <> " [ "
               <> var <> " := " <> prettyExpr expr
               <> " ]" )

    describeSuccess = unpack
        ( "✔ Got: " <> prettyExpr result )

    describeFailure = unpack
        ( "Expected: " <> prettyExpr expected <>
             "\nGot: " <> prettyExpr result )

    result = substituteExpr var expr body

    test =
        if result == expected then pass else expectationFailure describeFailure

-- =============================
-- ==== TestPatternCompiler ====
-- =============================

patternCompilerTestExpr1 :: Expr
patternCompilerTestExpr1 =
    lamS "xs" (matchS (varS "xs")
        -- Cons 5 Nil => "one"
        [ (conP "Cons" [litP (Int 5), conP "Nil" []], litString "one")
        -- Cons x (Cons 3 ys) => "two"
        , (conP "Cons" [varP "x", conP "Cons" [litP (Int 3), varP "ys"]], litString "two")
        -- Cons 2 ys => "three"
        , (conP "Cons" [litP (Int 2), varP "ys"], litString "three")
        -- Cons x Nil => "four"
        , (conP "Cons" [varP "x", conP "Nil" []], litString "four")
        -- Cons y (Cons z (Cons a as)) => "five"
        , (conP "Cons" [varP "y", conP "Cons" [varP "z", conP "Cons" [varP "a", varP "as"]]], litString "five")
        -- xs => "six"
        , (varP "xs", litString "six")
        ])

patternCompilerTestExpr2 :: Expr
patternCompilerTestExpr2 =
    lamS "xs" (matchS (varS "xs")
        -- Cons 5 Nil => #1
        [ (conP "Cons" [litP (Int 5), conP "Nil" []], litString "#1")
        -- Cons x (Cons x xs) => #2
        , (conP "Cons" [varP "x", conP "Cons" [varP "x", varP "xs"]], litString "#2")
        -- Cons y (Cons z Nil) => #3
        , (conP "Cons" [varP "y", conP "Cons" [varP "z", conP "Nil" []]], litString "#3")
        ])

patternCompilerTestExpr3 :: Expr
patternCompilerTestExpr3 =
    lamS "xs" (matchS (varS "xs")
        -- Just 1 => 1
        [ (conP "Just" [litP (Int 1)], litInt 1)
        -- Just 2 => 2
        , (conP "Just" [litP (Int 2)], litInt 2)
        -- Nothing -> 3
        , (conP "Nothing" [], litInt 3)
        ])

patternCompilerTestEnv :: EvalEnv Eval
patternCompilerTestEnv = Env.fromList
    [ ("Cons", dataCon "Cons" 2)
    , ("Nil", dataCon "Nil" 0)
    , ("Just", dataCon "Just" 1)
    , ("Nothing", dataCon "Nothing" 0)
    ]

patternCompilerTest010 :: (Expr, Expr, Value Eval)
patternCompilerTest010 =
    ( patternCompilerTestExpr1
    -- Cons 5 Nil
    , appS [varS "Cons", litInt 5, appS [varS "Nil"]]
    , Value (String "one") )

patternCompilerTest020 :: (Expr, Expr, Value Eval)
patternCompilerTest020 =
    ( patternCompilerTestExpr1
    -- Cons 5 (Cons 4 Nil)
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]
    , Value (String "six") )

patternCompilerTest030 :: (Expr, Expr, Value Eval)
patternCompilerTest030 =
    ( patternCompilerTestExpr1
    -- Cons 2 (Cons 4 Nil)
    , appS [varS "Cons", litInt 2, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]
    , Value (String "three") )

patternCompilerTest040 :: (Expr, Expr, Value Eval)
patternCompilerTest040 =
    ( patternCompilerTestExpr1
    -- Cons 2 Nil
    , appS [varS "Cons", litInt 2, appS [varS "Nil"]]
    , Value (String "three") )

patternCompilerTest050 :: (Expr, Expr, Value Eval)
patternCompilerTest050 =
    ( patternCompilerTestExpr1
    -- Nil
    , appS [varS "Nil"]
    , Value (String "six") )

patternCompilerTest060 :: (Expr, Expr, Value Eval)
patternCompilerTest060 =
    ( patternCompilerTestExpr1
    -- Cons 3 Nil
    , appS [varS "Cons", litInt 3, appS [varS "Nil"]]
    , Value (String "four") )

patternCompilerTest070 :: (Expr, Expr, Value Eval)
patternCompilerTest070 =
    ( patternCompilerTestExpr1
    -- Cons 5 (Cons 4 (Cons 3 Nil))
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Cons", litInt 3, varS "Nil"]]]
    , Value (String "five") )

patternCompilerTest080 :: (Expr, Expr, Value Eval)
patternCompilerTest080 =
    ( patternCompilerTestExpr2
    -- Cons 5 (Cons 3 Nil)
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 3, appS [varS "Nil"]]]
    , Value (String "#2") )

patternCompilerTest090 :: (Expr, Expr, Value Eval)
patternCompilerTest090 =
    ( patternCompilerTestExpr3
    -- Just 4
    , appS [varS "Just", litInt 4]
    , Value (Int 1) )

patternCompilerTest100 :: (Expr, Expr, Value Eval)
patternCompilerTest100 =
    ( patternCompilerTestExpr3
    -- Just 1
    , appS [varS "Just", litInt 1]
    , Value (Int 1) )

patternCompilerTest110 :: (Expr, Expr, Value Eval)
patternCompilerTest110 =
    ( patternCompilerTestExpr3
    -- Nil
    , appS [varS "Nil"]
    , Value (Int 1) )

testPatternCompile :: SpecWith ()
testPatternCompile = do
    patternCompilerTestSuccess patternCompilerTest010 "test010"
    patternCompilerTestSuccess patternCompilerTest020 "test020"
    patternCompilerTestSuccess patternCompilerTest030 "test030"
    patternCompilerTestSuccess patternCompilerTest040 "test040"
    patternCompilerTestSuccess patternCompilerTest050 "test050"
    patternCompilerTestSuccess patternCompilerTest060 "test060"
    patternCompilerTestSuccess patternCompilerTest070 "test070"
    patternCompilerTestSuccess patternCompilerTest080 "test080"
    patternCompilerTestFailure patternCompilerTest090 "test090"
    patternCompilerTestSuccess patternCompilerTest100 "test100"
    patternCompilerTestFailure patternCompilerTest110 "test110"

patternCompilerTestSuccess :: (Expr, Expr, Value Eval) -> Text -> SpecWith ()
patternCompilerTestSuccess (expr1, expr2, expected) name =
    describe description (it describeSuccess patternCompilerTest)
  where
    description = unpack
        ( name <> ": ("
               <> prettyExpr expr1
               <> prettyExpr expr2 )

    describeSuccess =
        unpack ("✔ evaluates to " <> prettyValue expected)

    patternCompilerTest = case evalExpr (appS [compileAll expr1, expr2]) patternCompilerTestEnv of
        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right result ->
            if expected == result
                then pass
                else expectationFailure $ unpack
                        ( "Expected: " <> prettyValue expected <>
                             "\nGot: " <> prettyValue result )

patternCompilerTestFailure :: (Expr, Expr, Value Eval) -> Text -> SpecWith ()
patternCompilerTestFailure (expr1, expr2, expected) name =
    describe description (it describeSuccess patternCompilerTest)
  where
    description = unpack
        ( name <> ": ("
               <> prettyExpr expr1
               <> prettyExpr expr2 )

    describeSuccess =
        unpack "✗ failed to evaluate with RuntimeError"

    patternCompilerTest = case evalExpr (appS [compileAll expr1, expr2]) patternCompilerTestEnv of
        Left RuntimeError ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right{} ->
            expectationFailure "Expected evaluation to fail"

-- =========================
-- ==== TestTypeClasses ====
-- =========================

-- (\s -> \a -> case s of { Show f => f a }) (Show id) "hello"
-- "hello" : String
tclcsTest000 :: Expr
tclcsTest000 = appS [lamS "s" (lamS "a" (matchS (varS "s") [(conP "Show" [varP "f"], appS [varS "f", varS "a"])])), appS [varS "Show", varS "id"], litString "hello"]

-- (\s -> \a -> case s of { Show f => f a }) (Show (\x -> if x then "True" else "False")) False
-- "False" : String
tclcsTest010 :: Expr
tclcsTest010 = appS [lamS "s" (lamS "a" (matchS (varS "s") [(conP "Show" [varP "f"], appS [varS "f", varS "a"])])), appS [varS "Show", lamS "x" (ifS (varS "x") (litString "True") (litString "False"))], litBool False]

-- let rec map = \f -> \xs -> match xs with | Nil -> Nil | Cons x1 xs1 -> Cons (f x1) (map f xs1) in map (\x -> x == 0)
tclcsTest020 :: Expr
tclcsTest020 = recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], appS [varS "Nil"]), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (appS [varS "map", lamS "x" (eqS (varS "x") (litInt 0))])

-- let rec map = \f -> \xs -> match xs with | Nil -> Nil | Cons x1 xs1 -> Cons (f x1) (map f xs1) in map (\x -> x == x)
tclcsTest021 :: Expr
tclcsTest021 = recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], appS [varS "Nil"]), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (appS [varS "map", lamS "x" (eqS (varS "x") (varS "x"))])

-- let f = \a -> \b -> a + b in f
tclcsTest025 :: Expr
tclcsTest025 =  letS "f" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (varS "f")

-- \x -> let xs = Cons x Nil in show xs
tclcsTest030 :: Expr
tclcsTest030 =  lamS "x" (letS "xs" (appS [varS "Cons", varS "x", appS [varS "Nil"]]) (appS [varS "show", varS "xs"]))


--typeInferRunTest testContext tclcsTest020

--tclcsTestContext :: Context
--tclcsTestContext = Context (Map.fromList
--    [ ("Show" , Forall ["a"] [] (ArrT (ArrT (VarT "a") tString) (AppT (ConT "Show") (VarT "a"))))
--    , ("id"   , Forall ["a"] [] (ArrT (VarT "a") (VarT "a")))
--    ])

testTypeClasses :: SpecWith ()
testTypeClasses = do
    testTclcsHasType "test000" (tclcsTest000, Forall [] [] tString)
    testTclcsEvalsTo "test000" (tclcsTest000, Value (String "hello"))
    testTclcsHasType "test010" (tclcsTest010, Forall [] [] tString)
    testTclcsEvalsTo "test010" (tclcsTest010, Value (String "False"))
    testSolveExprType "test020" (tclcsTest020, arrT (appT (conT "List") (conT "Int")) (appT (conT "List") (conT "Bool")), [Class "Eq" (conT "Int")])
    testSolveExprType "test021" (tclcsTest021, arrT (appT (conT "List") (varT "a35")) (appT (conT "List") (conT "Bool")), [Class "Eq" (varT "a35")])
    testSolveExprType "test025" (tclcsTest025, arrT (varT "a8") (arrT (varT "a8") (varT "a8")), [Class "Num" (varT "a8")])
    testSolveExprType "test030" (tclcsTest030, arrT (varT "a11") (conT "String"), [Class "Show" (appT (conT "List") (varT "a11"))])

testSolveExprType :: Text -> (Expr, Type, [Class]) -> SpecWith ()
testSolveExprType name (expr, ty, clcs) =
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> prettyExpr expr

    describeSuccess = unpack $ "✔ OK"

    test = case runInfer (solveExprType testContext expr) of
        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right (tree, sub, clcs') -> do
            let ty' = apply sub (getAnnotation tree) -- generalize mempty (apply sub $ getAnnotation tree)
             in do
                   --traceShowM (generalize mempty ty)
                   --traceShowM ty'
                   --traceShowM clcs
                   --traceShowM clcs'
                   if ty == ty' && clcs == clcs'
                       then pass
                       else expectationFailure "failed"

testTclcsEvalsTo :: Text -> (Expr, Value Eval) -> SpecWith ()
testTclcsEvalsTo name (expr, val) =
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> prettyExpr expr

    describeSuccess = unpack $ "✔ evaluates to " <> prettyValue val

    test = case (tclcsRunTest expr, val) of
        (Left err, _) ->
            expectationFailure ("Unexpected error: " <> show err)

        (Right (Value v1), Value v2) | v1 == v2 ->
            pass

        (Right result, _) ->
            expectationFailure $ unpack ("Unexpected result: " <> prettyValue result)

tclcsTestEnv :: EvalEnv Eval
tclcsTestEnv = Env.fromList
    [ ("Show" , dataCon "Show" 1)
    , ("id"   , evalE (lamS "x" (varS "x")))
    ]

tclcsRunTest :: Expr -> Either EvalError (Value Eval)
tclcsRunTest = flip evalExpr tclcsTestEnv

testTclcsHasType :: Name -> (Expr, Scheme) -> SpecWith ()
testTclcsHasType name (expr, ty) =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = unpack $
        "✔ has type : " <> prettyScheme ty

    describeFailure = unpack $
        "Expected type to be identical to : "
            <> prettyScheme ty
            <> " (up to isomorphism)"

    test = case typeInferRunTest tclcsTestContext expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            pass

        _ ->
            expectationFailure describeFailure

tclcsTestContext :: Env Scheme
tclcsTestContext = Env (Map.fromList
    [ ("Show" , Forall ["a"] [] (arrT (arrT (varT "a") tString) (appT (conT "Show") (varT "a"))))
    , ("id"   , Forall ["a"] [] (arrT (varT "a") (varT "a")))
    ])

-- ====================
-- ==== TestParser ====
-- ====================

parserTest000 :: String
parserTest000 = "4.3"

parserTest005 :: String
parserTest005 = "4"

parserTest010 :: String
parserTest010 = "let x = 3 in x"

parserTest020 :: String
parserTest020 = "f x"

parserTest030 :: String
parserTest030 = "x"

parserTest040 :: String
parserTest040 = "f (g y)"

parserTest050 :: String
parserTest050 = "f g h i"

parserTest060 :: String
parserTest060 = "()"

parserTest070 :: String
parserTest070 = "(())"

parserTest080 :: String
parserTest080 = "match n with | 1 -> True | 2 -> False"

parserTest090 :: String
parserTest090 = "let rec map = \\f -> \\xs -> match xs with | Nil -> Nil | Cons x1 xs1 -> Cons (f x1) (map f xs1) in map"

parserTest100 :: String
parserTest100 = "let rec map = \\f -> \\xs -> match xs with | Nil -> Nil | Cons x1 xs1 -> Cons (f x1) (map f xs1) in map (\\x -> x == 0)"

parserTest110 :: String
parserTest110 = "let str = \"hello\" in str"

parserTest120 :: String
parserTest120 = "\"hello\" == \"what\""

parserTest130 :: String
parserTest130 = "\"hello\""

parserTest140 :: String
parserTest140 = "'a' == 'b'"

parserTest150 :: String
parserTest150 = "let chr = 'a' in chr == chr"

testParser :: SpecWith ()
testParser = do
    testParsesTo "test000" (parserTest000, litFloat 4.3)
    testParsesTo "test005" (parserTest005, litInt 4)
    testParsesTo "test010" (parserTest010, letS "x" (litInt 3) (varS "x"))
    testParsesTo "test020" (parserTest020, appS [varS "f", varS "x"])
    testParsesTo "test030" (parserTest030, varS "x")
    testParsesTo "test040" (parserTest040, appS [varS "f", appS [varS "g", varS "y"]])
    testParsesTo "test050" (parserTest050, appS (varS <$> ["f", "g", "h", "i"]))
    testParsesTo "test060" (parserTest060, litUnit)
    testParsesTo "test070" (parserTest070, litUnit)
    testParsesTo "test080" (parserTest080, matchS (varS "n") [(litP (Int 1), litS (Bool True)), (litP (Int 2), litS (Bool False))])
    testParsesTo "test090" (parserTest090, recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], appS [varS "Nil"]), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (varS "map"))
    testParsesTo "test100" (parserTest100, recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], appS [varS "Nil"]), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (appS [varS "map", lamS "x" (eqS (varS "x") (litInt 0))]))
    testParsesTo "test110" (parserTest110, letS "str" (litString "hello") (varS "str"))
    testParsesTo "test120" (parserTest120, eqS (litString "hello") (litString "what"))
    testParsesTo "test130" (parserTest130, litString "hello")
    testParsesTo "test140" (parserTest140, eqS (litChar 'a') (litChar 'b'))
    testParsesTo "test150" (parserTest150, letS "chr" (litChar 'a') (eqS (varS "chr") (varS "chr")))

testParsesTo :: Name -> (String, Expr) -> SpecWith ()
testParsesTo name (input, expr) =
    describe description (it describeSuccess test)
  where
    description :: String
    description = unpack $ name <> ": " <> pack input

    describeSuccess = unpack $
        "✔ parses to : " <> prettyExpr expr

    test = case parseExpr (pack input) of
        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right result | result == expr ->
            pass

        Right result ->
            expectationFailure $ unpack ("Unexpected result: " <> pack (show result))

-- ========================
-- ==== Test utilities ====
-- ========================

pass :: Expectation
pass = pure ()

prettyKind :: Kind -> Text
prettyKind (Fix StarK)          = "*"
prettyKind (Fix (ArrowK k1 k2)) = prettyKind k1 <> " -> " <> prettyKind k2
prettyKind (Fix (VarK name))    = name

data TypeRep
    = ConRep Name
    | VarRep Int
    | ArrRep TypeRep TypeRep
    | AppRep TypeRep TypeRep
  deriving (Show, Eq)

canonical :: Scheme -> Scheme
canonical (Forall vars clcs ty) =
    Forall names (apply sub clcs) (apply sub ty)
  where
    names = take (length vars) (enumFrom 1 >>= fmap pack . flip replicateM ['a'..'z'])
    sub = Substitution $ Map.fromList $ zip vars (varT <$> names)

isoTypes :: Scheme -> Scheme -> Bool
isoTypes t u = canonical t == canonical u

prettyScheme :: Scheme -> Text
prettyScheme (Forall vars clcs ty) =
    quantifiedVars <> constraints <> prettyType ty
  where
    quantifiedVars
        | null vars = ""
        | otherwise = "forall " <> Text.concat (intersperse " " vars) <> ". "
    constraints
        | null clcs = ""
        | otherwise = Text.concat (intersperse ", " $ prettyClcs <$> clcs) <> " => "

prettyClcs :: Class -> Text
prettyClcs (Class name ty) = name <> " " <> prettyType ty

prettyType :: Type -> Text
prettyType = \case
    Fix (ConT name)  -> name
    Fix (VarT name)  -> name
    Fix (AppT t1 t2) -> prettyType t1 <> " " <> prettyType t2
    Fix (ArrT t1 t2) -> prettyType t1 <> " -> " <> prettyType t2

prettyExpr :: Expr -> Text
prettyExpr = cata alg
  where
    alg :: Algebra ExprF Text
    alg = \case
        VarS name ->
            name

        LamS name a ->
            "("  <>
            "\\" <> name
                 <> " -> "
                 <> a
                 <> ")"

        AppS exprs ->
            foldl1 (\f x -> "(" <> f <> " " <> x <> ")") exprs

        LitS Unit ->
            "()"

        LitS (Bool bool) ->
            pack (show bool)

        LitS (Int n) ->
            pack (show n)

        LitS (Integer n) ->
            pack (show n)

        LitS (Float r) ->
            pack (show r)

        LitS (Char c) ->
            pack (show c)

        LitS (String str) ->
            pack (show str)

        LetS name expr body ->
            "let " <> name <> " = " <> expr <> " in " <> body

        RecS name expr body ->
            "let rec " <> name <> " = " <> expr <> " in " <> body

        IfS cond true false ->
            "("  <> "if " <> cond <> " then " <> true <> " else " <> false <> ")"

        MatchS expr [] ->
            "match [] with"

        MatchS expr clss ->
            "match " <> expr <> " with | " <> Text.concat (intersperse " | " $ prettyClause <$> clss)

        OpS ops ->
            prettyOp ops

        AnnS expr ty ->
            "TODO"

        ErrS ->
            "<<error>>"

prettyOp :: OpF Text -> Text
prettyOp (AddS a b) = a <> " + " <> b
prettyOp (SubS a b) = a <> " - " <> b
prettyOp (MulS a b) = a <> " * " <> b
prettyOp (EqS a b)  = a <> " == " <> b
prettyOp (LtS a b)  = a <> " < " <> b
prettyOp (GtS a b)  = a <> " > " <> b
prettyOp (NegS a)   = "-" <> a
prettyOp (NotS a)   = "not " <> a

prettyClause :: (Pattern, Text) -> Text
prettyClause (p, e) = prettyPattern p <> " -> " <> e

prettyPattern :: Pattern -> Text
prettyPattern = trim . cata alg where
    trim = dropPrefix . dropSuffix . Text.dropWhileEnd (== ' ')
    alg (VarP name)    = name <> " "
    alg (ConP name []) = name <> " "
    alg (ConP name ps) = "(" <> name <> " " <> Text.dropEnd 1 (Text.concat ps) <> ") "
    alg (LitP p)       = prettyPrim p <> " "
    alg AnyP           = "_ "

prettyPatterns :: [Pattern] -> Text
prettyPatterns = Text.concat . intersperse "\n    - " . (:) "" . map prettyPattern

prettyPrim :: Prim -> Text
prettyPrim Unit        = "()"
prettyPrim (Bool b)    = pack (show b)
prettyPrim (Float r)   = pack (show r)
prettyPrim (Char c)    = pack (show c)
prettyPrim (Int n)     = pack (show n)
prettyPrim (Integer n) = pack (show n)
prettyPrim (String s)  = "\"" <> s <> "\""

prettyValue :: Value m -> Text
prettyValue (Value p)        = prettyPrim p
prettyValue (Data name args) = name <> " " <> Text.concat (intersperse " " (prettyValue <$> args))
prettyValue Closure{}        = "<<function>>"

dropPrefix :: Text -> Text
dropPrefix txt = fromMaybe txt $ Text.stripPrefix "(" txt

dropSuffix :: Text -> Text
dropSuffix txt = fromMaybe txt $ Text.stripSuffix ")" txt
