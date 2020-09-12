{-# LANGUAGE OverloadedStrings #-}
module Tau.KindInferenceTests where

import Tau.Env
import Tau.Kind.Inference
import Tau.Type
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testKindEnv :: Env Kind
testKindEnv = Env.fromList
    [ ("List"  , arrK starK starK)
    , ("State" , arrK starK (arrK starK starK))
    , ("Monad" , arrK starK starK)
    ]

succeedInferKind :: Type -> Kind -> SpecWith ()
succeedInferKind ty expected =
    describe ("The type : " <> prettyString ty) $
        it ("✔ has kind " <> prettyString expected) $
            runInferKind testKindEnv ty == Right expected

testKindInference :: SpecWith ()
testKindInference = do
    succeedInferKind
        (appT (conT "List") (varT "a"))
        starK

    succeedInferKind
        (appT (appT (conT "State") (varT "a")) (conT "Int"))
        starK

-- TODO
--    succeedInferKind
--        (appT (varT "m") (varT "a"))
--        starK

    succeedInferKind
        (arrT (appT (conT "List") (varT "a")) (appT (conT "List") (conT "Int")))
        starK

    succeedInferKind
        (conT "List") 
        (arrK starK starK)
