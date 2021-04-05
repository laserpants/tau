{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Tau.Compiler.TypecheckTests where

import Control.Monad.Writer
import Data.Either (isLeft, isRight)
import Data.List (nub)
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Compiler.Typecheck
import Tau.Compiler.Unification
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Set.Monad as Set
import qualified Tau.Compiler.Substitution as Sub
import qualified Tau.Env as Env

runInferWithEnvs :: (Monoid t) => InferStack t a -> Either (InferError t) (a, TypeSubstitution, Context)
runInferWithEnvs = runInfer mempty testClassEnv testTypeEnv testConstructorEnv

failInferPattern :: (Show t, Monoid t) => Text -> ProgPattern t -> (Error -> Bool) -> SpecWith ()
failInferPattern expl pat isExpected = do
    describe ("The pattern " <> prettyText pat) $
        case runInferWithEnvs (runWriterT (inferPattern pat)) of
            Left (InferError _ _ err _) -> 
                it ("✗ is not well-typed: (" <> expl <> ")") $ isExpected err
            Right{} -> 
                error "was expected to fail"

succeedInferPattern :: (Show t, Monoid t) => ProgPattern t -> Type -> [Predicate] -> [(Name, Type)] -> SpecWith ()
succeedInferPattern pat ty ps vs = do
    case runInferWithEnvs (runWriterT (inferPattern pat)) of
        Left e -> error (show e)
        Right ((pat, vars), sub, context) -> do
            describe ("The pattern " <> prettyText pat) $
                it ("has type: " <> prettyText ty <> ", class constraints: " 
                                 <> prettyText ps <> ", variables: " 
                                 <> prettyText vs <> ", etc.") $
                    let TypeInfo{..} = patternTag (apply sub pat)
                        sub1 = normalize nodeType
                        vars' = apply sub <$$> vars
                     in let result = unify (apply sub1 nodeType) ty :: Either UnificationError TypeSubstitution
                         in isRight result 
                             && apply sub1 (nub nodePredicates) == ps
                             && Set.fromList (apply sub1 <$$> vars') == Set.fromList vs

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

    succeedInferPattern 
        (conPat () "Some" [litPat () (TInt 5)])
        (tApp (tCon kFun "Option") _a)
        [InClass "Num" _a] 
        []

    -- As-patterns
    succeedInferPattern 
        (asPat () "someX" (conPat () "Some" [varPat () "x"]))
        (tApp (tCon kFun "Option") _a)
        [] 
        [("x", _a), ("someX", tApp (tCon kFun "Option") _a)]

    succeedInferPattern 
        (asPat () "asSomeX" (asPat () "someX" (conPat () "Some" [varPat () "x"])))
        (tApp (tCon kFun "Option") _a)
        [] 
        [("x", _a), ("someX", tApp (tCon kFun "Option") _a), ("asSomeX", tApp (tCon kFun "Option") _a)]

    -- Or-patterns
    succeedInferPattern 
        (orPat () (conPat () "Some" [litPat () (TInt 1)]) (conPat () "Some" [litPat () (TInt 2)]))
        (tApp (tCon kFun "Option") _a)
        [InClass "Num" _a] 
        []

    -- Wildcard patterns
    succeedInferPattern 
        (anyPat ())
        _a
        [] 
        []

    -- Tuple patterns
    succeedInferPattern 
        (tuplePat () [litPat () (TBool True), varPat () "x"])
        (tTuple [tBool, _a])
        [] 
        [("x", _a)]

    -- List patterns
    succeedInferPattern 
        (listPat () [litPat () (TBool True), litPat () (TBool False)])
        (tList tBool)
        [] 
        []

    succeedInferPattern 
        (listPat () [litPat () (TBool True), varPat () "x"])
        (tList tBool)
        [] 
        [("x", tBool)]

    -- Record pattern

    succeedInferPattern 
        (recordPat2 () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)))
        (tRecord (rowToType (rExt "id" _a (rExt "name" _b rNil))))
        [] 
        [("id", _a), ("name", _b)]

    -- Failures

    failInferPattern "List type unification fails"
        (listPat () [litPat () (TBool True), litPat () (TInt 5)])
        (\case { ListPatternTypeUnficationError -> True; _ -> False })

    failInferPattern "List type unification fails"
        (listPat () [litPat () (TBool True), litPat () TUnit])
        (\case { ListPatternTypeUnficationError -> True; _ -> False })

    failInferPattern "Constructor arity doesn't match given arguments"
        (conPat () "Some" [litPat () (TInt 5), litPat () (TInt 5)])
        (== ConstructorPatternArityMismatch "Some" 1 2)

    failInferPattern "No such data constructor"
        (conPat () "Done" [litPat () (TInt 5)])
        (== NoDataConstructor "Done")

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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
