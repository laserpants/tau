{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.TestPatternCheck where

import Data.Text (Text, pack, unpack)
import Tau.Pattern
import Test.Hspec
import Utils
import qualified Utils.Pretty as Pretty

testConstructors :: Lookup
testConstructors = lookupFromList
    [ ("Nil", ["Nil", "Cons"])
    , ("Cons", ["Nil", "Cons"])
    ]
    -- True

test010 :: [Pattern]
test010 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    , conP "Cons" [varP "z", varP "zs"]
    ]
    -- True

test020 :: [Pattern]
test020 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    , conP "Cons" [varP "z", conP "Nil" []]
    ]

test030 :: [Pattern]
test030 =
    [ conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]]
    , conP "Nil" []
    ]
    -- False

test040 :: [Pattern]
test040 =
    [ conP "Nil" []
    ]
    -- False

test050 :: [Pattern]
test050 =
    [ anyP
    ]
    -- True

test060 :: [Pattern]
test060 =
    [ conP "Cons" [varP "x", varP "ys"]
    , conP "Nil" []
    ]
    -- True

test070 :: [Pattern]
test070 =
    [ conP "Cons" [varP "x", varP "ys"]
    , varP "x"
    ]
    -- True

test080 :: ([Pattern], Pattern)
test080 =
    ( [ conP "Cons" [varP "x", varP "ys"]
      , varP "x" ]
    , conP "Nil" [] )
    -- False

test090 :: ([Pattern], Pattern)
test090 =
    ( [ conP "Cons" [varP "x", varP "ys"]
      , varP "x"
      , conP "Nil" [] ]
    , conP "Nil" [] )
    -- False

test100 :: ([Pattern], Pattern)
test100 =
    ( [ conP "Cons" [varP "x", varP "ys"] ]
    , conP "Nil" [] )
    -- True

testPatternCheck :: SpecWith ()
testPatternCheck = do
    testIsExhaustive  test010 "test010"
    testIsExhaustive  test020 "test020"
    testNotExhaustive test030 "test030"
    testNotExhaustive test040 "test040"
    testIsExhaustive  test050 "test050"
    testIsExhaustive  test060 "test060"
    testIsExhaustive  test070 "test070"
    testNotUseful     test080 "test080"
    testNotUseful     test090 "test090"
    testIsUseful      test100 "test100"

testIsExhaustive :: [Pattern] -> Text -> SpecWith ()
testIsExhaustive pttrns name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.patterns pttrns

    describeSuccess = unpack "✔ is exhaustive"

    describeFailure = unpack
        "Expected exhaustive check to return True"

    test = case runExhaustiveTest pttrns of
        Right True ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        _ ->
            expectationFailure describeFailure

testNotExhaustive :: [Pattern] -> Text -> SpecWith ()
testNotExhaustive pttrns name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.patterns pttrns

    describeSuccess = unpack "✗ is NOT exhaustive"

    describeFailure = unpack
        "Expected exhaustive check to return False"

    test = case runExhaustiveTest pttrns of
        Right False ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        _ ->
            expectationFailure describeFailure

runExhaustiveTest :: [Pattern] -> Either PatternCheckError Bool
runExhaustiveTest pttrns = runPatternCheck (exhaustive pttrns) testConstructors

testNotUseful :: ([Pattern], Pattern) -> Text -> SpecWith ()
testNotUseful pair name =
    describe description (it describeSuccess test)
  where
    description = unpack (name <> ": " <> Pretty.patterns (fst pair))

    describeSuccess = unpack $
        "✗ clause " <> Pretty._pattern (snd pair)
                    <> " is NOT useful"

    describeFailure = unpack
        "Expected useful check to return False"

    test = case runIsUsefulTest pair of
        Right False ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        _ ->
            expectationFailure describeFailure

testIsUseful :: ([Pattern], Pattern) -> Text -> SpecWith ()
testIsUseful pair name =
    describe description (it describeSuccess test)
  where
    description = unpack (name <> ": " <> Pretty.patterns (fst pair))

    describeSuccess = unpack $
        "✔ clause " <> Pretty._pattern (snd pair)
                    <> " is useful"

    describeFailure = unpack
        "Expected useful check to return True"

    test = case runIsUsefulTest pair of
        Right True ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        _ ->
            expectationFailure describeFailure

runIsUsefulTest :: ([Pattern], Pattern) -> Either PatternCheckError Bool
runIsUsefulTest (ps, p) =
    runPatternCheck (uncurry useful (map (:[]) ps, [p])) testConstructors
