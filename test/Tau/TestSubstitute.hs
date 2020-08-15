{-# LANGUAGE OverloadedStrings #-}
module Tau.TestSubstitute where

import Data.Text (Text, unpack)
import Tau.Ast
import Tau.Core
import Tau.Substitution
import Test.Hspec
import Utils
import qualified Utils.Pretty as Pretty

-- let x = 3 in x [x := y]  ==>  let x = 3 in x
test000 = 
    ( letS "x" (litInt 3) (varS "x")
    , ("x", varS "y")
    , letS "x" (litInt 3) (varS "x") )

-- let z = 3 in x [x := y]  ==>  let z = 3 in y
test010 = 
    ( letS "z" (litInt 3) (varS "x")
    , ("x", varS "y")
    , letS "z" (litInt 3) (varS "y") )

-- let x = 3 in x + 5 [x := y]  ==>  let x = 3 in x + 5
test020 = 
    ( letS "x" (litInt 3) (addS (varS "x") (litInt 5))
    , ("x", varS "y")
    , letS "x" (litInt 3) (addS (varS "x") (litInt 5)) )

-- let y = 3 in x + 5 [x := 8]  ==>  let y = 3 in 8 + 5
test030 = 
    ( letS "y" (litInt 3) (addS (varS "x") (litInt 5))
    , ("x", litInt 8)
    , letS "y" (litInt 3) (addS (litInt 8) (litInt 5)) )

-- let y = x + 3 in 45 [x := 2]  ==>  let y = 2 + 3 in 45
test040 = 
    ( letS "y" (addS (varS "x") (litInt 3)) (litInt 45)
    , ("x", litInt 2)
    , letS "y" (addS (litInt 2) (litInt 3)) (litInt 45) )

-- let x = x + 3 in 45 [x := 2]  ==>  let x = x + 3 in 45
test050 = 
    ( letS "x" (addS (varS "x") (litInt 3)) (litInt 45)
    , ("x", litInt 2)
    , letS "x" (addS (varS "x") (litInt 3)) (litInt 45) )

-- let x = 3 in let y = x + 1 in 45 [x := 2]  ==>  let x = 3 in let y = x + 1 in 45
test060 = 
    ( letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45))
    , ("x", litInt 2)
    , letS "x" (litInt 3) (letS "y" (addS (varS "x") (litInt 1)) (litInt 45)) )

-- let x = 3 in let y = z + 1 in 45 [z := 2]  ==>  let x = 3 in let y = 2 + 1 in 45
test070 = 
    ( letS "x" (litInt 3) (letS "y" (addS (varS "z") (litInt 1)) (litInt 45))
    , ("z", litInt 2)
    , letS "x" (litInt 3) (letS "y" (addS (litInt 2) (litInt 1)) (litInt 45)) )

testSubstitute :: SpecWith ()
testSubstitute = do
    testSubst test010 "test010"
    testSubst test020 "test020"
    testSubst test030 "test030"
    testSubst test040 "test040"
    testSubst test050 "test050"
    testSubst test060 "test060"
    testSubst test070 "test070"

testSubst :: (Expr, (Name, Expr), Expr) -> Text -> SpecWith ()
testSubst (body, (var, expr), expected) name =
    describe description (it describeSuccess test)
  where 
    description = unpack 
        ( name <> ": " 
               <> Pretty.expr body 
               <> " [ " 
               <> var <> " := " <> Pretty.expr expr 
               <> " ]" )

    describeSuccess = unpack
        ( "✔ Got: " <> Pretty.expr result )

    describeFailure = unpack 
        ( "Expected: " <> Pretty.expr expected <> 
             "\nGot: " <> Pretty.expr result )

    result = substitute var expr body

    test = 
        if result == expected then pass else expectationFailure describeFailure
