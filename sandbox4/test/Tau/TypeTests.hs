{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeTests where

import Tau.Lang.Type
import Test.Hspec
import Utils

typesAreEqual :: Type -> Type -> SpecWith ()
typesAreEqual t1 t2 = 
    describe "The two types" $ do
        it "✔ are the same\n" 
            (t1 == t2)

testTypes :: SpecWith ()
testTypes = do

    typesAreEqual
        (tRecord [("name", tString), ("id", tInt)] :: Type)
        (tApp (tApp (tCon kFun2 "{id,name}") tInt) tString)

    typesAreEqual
        (tRecord [("name", tString), ("id", tInt)] :: Type)
        (tRecord [("id", tInt), ("name", tString)] :: Type)

    typesAreEqual
        (tTuple [tInt, tString])
        (tApp (tApp (tCon kFun2 "(,)") tInt) tString)

