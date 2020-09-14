{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.KindInferenceTests where

import TH
import Tau.Env
import Tau.Kind.Inference
import Tau.Type
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testKindEnv :: Env Kind
testKindEnv = Env.fromList
    [ ( "List"  , $(mkKind "* -> *") )
    , ( "State" , $(mkKind "* -> * -> *") )
    , ( "Monad" , $(mkKind "* -> *") )
    ]

succeedInferKind :: Type -> Kind -> SpecWith ()
succeedInferKind ty expected =
    describe ("The type : " <> prettyString ty) $
        it ("✔ has kind " <> prettyString expected) $
            runInferKind testKindEnv ty == Right expected

testKindInference :: SpecWith ()
testKindInference = do
    succeedInferKind
        $(mkType "List a")
        $(mkKind "*")

    succeedInferKind
        $(mkType "State a Int")
        $(mkKind "*")

-- TODO
--    succeedInferKind
--        (appT (varT "m") (varT "a"))
--        starK

    succeedInferKind
        $(mkType "List a -> List Int")
        $(mkKind "*")

    succeedInferKind
        $(mkType "List")
        $(mkKind "* -> *")
