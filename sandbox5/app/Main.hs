{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Writer
import Tau.Compiler.Substitution
import Tau.Compiler.Typecheck
import Tau.Compiler.Unification
import Tau.Core
import Tau.Env
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Type
import qualified Tau.Env as Env

main = print "Main"

myTestClassEnv :: ClassEnv
myTestClassEnv = Env.fromList
    [ ( "Show"
      , ( ClassInfo [] (InClass "Show" "a") 
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo [] (InClass "Show" tInt) 
              [ ( "show", undefined :: Ast TypeInfo ) 
              ]
          , ClassInfo [] (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b"))) 
              [ ( "show", undefined :: Ast TypeInfo ) 
              ]
          ]
        )
      )
    , ( "Eq"
      , ( ClassInfo [] (InClass "Eq" "a") 
            []
        -- Instances
        , []
        )
      )
    , ( "Eq"
      , ( ClassInfo [InClass "Ord" "a"] (InClass "Eq" "a") 
            []
        -- Instances
        , []
        )
      )
    ]

myTestTypeEnv = Env.fromList
    [ ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
    ]

testPattern1 = varPat () "x"

myTest1 = runInfer mempty mempty mempty (runWriterT (inferPattern testPattern1))

testPattern2 = litPat () (TBool True)

myTest2 = runInfer mempty mempty mempty (runWriterT (inferPattern testPattern2))

testPattern3 = litPat () (TInt 5 )

myTest3 = runInfer mempty mempty mempty (runWriterT (inferPattern testPattern3))

testPattern4 = conPat () "Some" [varPat () "x"]

myTest4 = apply sub pat
  where
    Right ((pat, _), (sub, context)) = runInfer mempty mempty myTestTypeEnv (runWriterT (inferPattern testPattern4))
