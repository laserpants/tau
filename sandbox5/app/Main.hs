{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Writer
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Compiler.Typecheck
import Tau.Compiler.Unification
import Tau.Core
import Tau.Env
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Tau.Env as Env

--test3 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
--  where
--    r1 = tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow)
--    r2 = tRowExtend "id" tString (tRowExtend "name" tInt tEmptyRow)
--
--test4 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
--  where
--    r1 = tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow)
--    r2 = tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow)
--
--test5 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
--  where
--    r1 = tRowExtend "x" tInt (tVar kRow "r")
--    r2 = tRowExtend "x" tInt (tVar kRow "r")
--
--test6 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
--
--r1 = tRowExtend "x" tInt (tVar kRow "r")
--r2 = tRowExtend "y" tInt (tVar kRow "r")
--
--
--pattern1 = recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)) 
--
----pattern1 = conPat () "Foo" [litPat () (TBool True), litPat () (TInt 5)]
----pattern1 = conPat () "Done" [litPat () (TInt 5), litPat () (TInt 5)]
----pattern1 = conPat () "Some" [litPat () (TInt 5), litPat () (TInt 5)]
----pattern1 = listPat () [litPat () (TBool True), litPat () TUnit]
----pattern1 = listPat () [litPat () (TBool True), litPat () (TInt 5)]
----pattern1 = asPat () "someX" (conPat () "Some" [varPat () "x"])
----pattern1 = (conPat () "Some" [varPat () "x"])
--
--test1 :: IO ()
--test1 = 
--    case runInfer mempty testClassEnv testTypeEnv testConstructorEnv (runWriterT (inferPattern pattern1)) of
--        Left e -> error (show e)
--        Right ((pat, vars), sub, context) -> do
--            let TypeInfo{..} = patternTag (apply sub pat)
--                vars' = apply sub <$$> vars
--                sub1 = normalize nodeType
--                xx1 = apply sub1 nodeType
--                xx2 = apply sub1 nodePredicates
--                xx3 = apply sub1 <$$> vars'
--              in do
--                  print sub
--                  print ">>>>"
--                  print nodeType 
--                  print nodePredicates
--                  print vars'
--                  print ">>>>"
--                  print xx1
--                  print xx2
--                  print xx3
--                  pure ()

main :: IO ()
main = print "Main"

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Foo"    , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Show"
        -- Interface
      , ( ClassInfo [] (InClass "Show" "a") 
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo [] (InClass "Show" tInt)
              [ ( "show", Ast (varExpr (TypeInfo (tInt `tArr` tString) []) "@Int.Show") )
              ]
          , ClassInfo [] (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b")))
              [ ( "show", Ast (varExpr (TypeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "TODO") )
              ]
          ]
        )
      )
    , ( "Ord"
        -- Interface
      , ( ClassInfo [] (InClass "Ord" "a") 
            [ ( "(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(>=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            ]
        -- Instances
        , []
        )
      )
    , ( "Eq"
        -- Interface
      , ( ClassInfo [InClass "Ord" "a"] (InClass "Eq" "a")
            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo [] (InClass "Eq" tInt)
            [ ( "(==)", Ast (varExpr (TypeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)" ) )
            ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo [] (InClass "Num" "a")
            [ 
            ]
        -- Instances
        , [ ClassInfo [] (InClass "Num" tInt)
            []
        ]
        )
      )
    ]

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    ]
