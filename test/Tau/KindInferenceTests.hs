{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.KindInferenceTests where

import Tau.Env
import Tau.Kind.Inference
import Tau.Type
import Tau.Util.TH
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testKindEnv :: Env Kind
testKindEnv = Env.fromList
    [ ( "List"  , $(parseKind "* -> *") )
    , ( "State" , $(parseKind "* -> * -> *") )
    , ( "Monad" , $(parseKind "* -> *") )
    ]

succeedInferKind :: Type -> Kind -> SpecWith ()
succeedInferKind ty expected =
    describe ("The type : " <> prettyString ty) $
        it ("✔ has kind " <> prettyString expected) $
            runInferKind testKindEnv ty == Right expected

testKindInference :: SpecWith ()
testKindInference = do
    succeedInferKind
        $(parseType "List a")
        $(parseKind "*")

    succeedInferKind
        $(parseType "State a Int")
        $(parseKind "*")

-- TODO
--    succeedInferKind
--        (appT (varT "m") (varT "a"))
--        starK

    succeedInferKind
        $(parseType "List a -> List Int")
        $(parseKind "*")

    succeedInferKind
        $(parseType "List")
        $(parseKind "* -> *")
