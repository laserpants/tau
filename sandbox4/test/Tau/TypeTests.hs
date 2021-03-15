{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeTests where

import Tau.Lang.Type
import Test.Hspec
import Utils

typesEqual :: Type -> Type -> SpecWith ()
typesEqual t1 t2 = 
    describe "The two types" $ do
        it "✔ are the same\n" 
            (t1 == t2)

testTypes :: SpecWith ()
testTypes = do

    typesEqual
        (tRecord [("name", tString), ("id", tInt)] :: Type)
        (tApp (tApp (tCon (kTyp `kArr` kTyp `kArr` kTyp) "{id,name}") tInt) tString)

    typesEqual
        (tRecord [("name", tString), ("id", tInt)] :: Type)
        (tRecord [("id", tInt), ("name", tString)] :: Type)

