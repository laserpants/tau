{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Tau.Compiler.TypecheckTests where

import Control.Monad.Writer
import Tau.Compiler.Substitution
import Tau.Compiler.Typecheck
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tool
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Tau.Compiler.Substitution as Sub
import qualified Tau.Env as Env

-- traceShow (apply sub1 nodeType, apply sub1 nodePredicates, apply sub1 <$$> vars)
succeedInferPattern :: ProgPattern t -> Type -> [Predicate] -> [(Name, Type)] -> SpecWith ()
succeedInferPattern pat ty ps vs = do
    case runInfer mempty testClassEnv testTypeEnv (runWriterT (inferPattern pat)) of
        Left e -> error e
        Right ((pat, vars), (sub, context)) -> do
            describe ("The pattern " <> prettyText pat) $
                it ("has type: " <> prettyText ty <> ", class constraints: " <> prettyText vars <> ", variables: " <> prettyText vs <> ", etc.") $
                    let TypeInfo{..} = patternTag (apply sub pat)
                        sub1 = normalize nodeType
                     in apply sub1 nodeType == ty
                            && apply sub1 nodePredicates == ps
                            && (apply sub1 <$$> vars) == vs

testInferPattern :: SpecWith ()
testInferPattern = do

    succeedInferPattern 
        (varPat () "x") 
        (tVar kTyp "a") 
        [] 
        [("x", tVar kTyp "a")]

    succeedInferPattern 
        (litPat () (TBool True))
        tBool
        [] 
        []

    succeedInferPattern 
        (litPat () (TInt 5))
        (tVar kTyp "a")
        [InClass "Num" _a] 
        []

    succeedInferPattern 
        (conPat () "Some" [varPat () "x"])
        (tApp (tCon kFun "Option") _a)
        [] 
        [("x", _a)]

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
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
    ]
