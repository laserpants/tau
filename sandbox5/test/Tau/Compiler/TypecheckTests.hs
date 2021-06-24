{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.TypecheckTests where

import Control.Monad.Identity
import Data.Either (isLeft, isRight)
import Data.Maybe
import Tau.Compiler.Substitute
import Tau.Compiler.Typecheck
import Tau.Compiler.Unify
import Tau.Core
import Tau.Eval
import Tau.Pretty
import Tau.Lang
import Tau.Prog
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Tau.Env as Env

runInferStack :: InferStack Identity a -> (a, Substitution Type, Substitution Kind, Context)
runInferStack = runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv 

succeedInferExpr :: ProgExpr () -> Type -> SpecWith ()
succeedInferExpr expr ty = -- ps errs =
    describe ("The inferred type of the expression " <> prettyText expr) $ do
        it ("✔ is unifiable with " <> prettyText ty) $
            isRight r
  where
    (Ast e, typeSub, kindSub, context) = runInferStack (inferAstType (Ast expr))
    e1 = applyBoth (typeSub, kindSub) e
    t1 = typeOf e1
    r = runUnify (unifyTypes t1 ty)

succeedInferPattern :: ProgPattern () -> Type -> SpecWith ()
succeedInferPattern pat ty = -- ps errs =
    describe ("The inferred type of the pattern " <> prettyText pat) $ do
        it ("✔ is unifiable with " <> prettyText ty) $
            isRight r
  where
    ((p, _), typeSub, kindSub, context) = runInferStack (inferPatternType pat)
    e1 = applyBoth (typeSub, kindSub) p
    t1 = typeOf e1
    r = runUnify (unifyTypes t1 ty)

testKindEnv :: KindEnv
testKindEnv = Env.fromList
    [ ( "Num" , kArr kTyp kClass )
    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Foo"          , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    , ( "id"           , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    , ( "(::)"         , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"           , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "(+)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "#"            , Forall [kRow] [] (tGen 0 `tArr` tApp kTyp tRecordCon (tGen 0)) )
    , ( "{}"           , Forall [] [] tRowNil )
    , ( "_#"           , Forall [kRow] [] (tApp kTyp (tCon (kArr kRow kTyp) "#") (tGen 0) `tArr` tGen 0) )
    , ( "fromInteger"  , Forall [kTyp] [InClass "Num" 0] (tInteger `tArr` tGen 0) )
    , ( "fn1"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Show"
        -- Interface
      , ( ClassInfo (InClass "Show" "a") []  
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.Show") )
              ]
          , ClassInfo (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b"))) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "TODO") )
              ]
          ]
        )
      )
    , ( "Ord"
        -- Interface
      , ( ClassInfo (InClass "Ord" "a") [] 
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
      , ( ClassInfo (InClass "Eq" "a") [InClass "Ord" "a"] 
            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Eq" tInt) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)" ) )
            ]
          ]
        )
      )
    , ( "Foo"
        -- Interface
      , ( ClassInfo (InClass "Foo" "a") [] 
            -- [ ( "foo", tInt ) 
            [ ( "foo", tBool ) 
            ]
        -- Instances
        , [ ClassInfo (InClass "Foo" tInt) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 5))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool True))) ) ]
          , ClassInfo (InClass "Foo" tInteger) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 7))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool False))) ) ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo (InClass "Num" "a") [InClass "Foo" "a"]
            [ ( "(+)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "fromInteger" , tInteger `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , [ ClassInfo (InClass "Num" tInt) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInt) []) "@Int.fromInteger") )
            ]
          , ClassInfo (InClass "Num" tInteger) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(+)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger) []) "@Integer.id") )
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
    , ("#"        , ( ["#"], 1 ))
    , ("{}"       , ( ["{}"], 0 ))
    ]

testEvalEnv :: ValueEnv Eval
testEvalEnv = Env.fromList 
    [ -- ( "(,)" , constructor "(,)" 2 )
      ( "_#"  , fromJust (evalExpr (cLam "?0" (cPat (cVar "?0") [(["#", "?1"], cVar "?1")])) mempty) ) 
    , ( "(.)" , fromJust (evalExpr (cLam "f" (cLam "x" (cApp [cVar "f", cVar "x"]))) mempty) )
--    , ( "fn1" , fromJust (evalExpr (cLam "?0" (cLam "?1" (cApp [cVar "@Integer.(+)", cVar "?0", cVar "?1"]))) mempty) )
    ]

--import Control.Monad.Writer
--import Data.Either (isLeft, isRight)
--import Data.List (nub)
--import Data.Map.Strict (Map)
--import Data.Maybe (fromJust)
--import Data.Set.Monad (Set)
--import Tau.Compiler.Error
--import Tau.Compiler.Substitution
--import Tau.Compiler.Typecheck
--import Tau.Compiler.Unification
--import Tau.Env (Env(..))
--import Tau.Lang
--import Tau.Pretty
--import Tau.Prog
--import Tau.Row
--import Tau.Tooling
--import Tau.Type
--import Test.Hspec hiding (describe, it)
--import Utils
--import qualified Data.Map.Strict as Map
--import qualified Data.Set.Monad as Set
--import qualified Tau.Compiler.Substitution as Sub
--import qualified Tau.Env as Env
--
----instance Substitutable Context Void where
----    apply sub ctx = undefined
----      where
----        y :: Map Type (Set Name)
----        y = Map.mapKeys (apply sub . tVar kTyp) x
----        (Env x) = ctx
--
--succeedInferExpr expr ty ps errs = do
--    describe "xxx" $ do
--        it "yyy" $ do
--            let 
--                    TypeInfo{..} = exprTag (apply sub e)
--                    sub1 = normalizer (typeVars nodeType)
--              in 
--                  traceShow context $
----                traceShow info $
----                    traceShow (apply sub1 nodeType) $
----                        traceShow (apply sub1 (nub nodePredicates)) $
--
--                      apply sub1 nodeType ==  ty
--                           && apply sub1 (nub nodePredicates) == ps
--                           && nodeErrors == errs
--  where
--    (e, sub, context) = runInferWithEnvs (inferExpr expr)
--
--succeedInferPattern pat ty ps vs = do
--    describe "xxx" $ do
--        it "yyy" $ do
--            let 
--                    TypeInfo{..} = patternTag (apply sub p)
--                    sub1 = normalizer (typeVars nodeType)
--                    vars' = apply sub <$$> vars
--              in traceShow nodeErrors $
--                    apply sub1 nodeType ==  ty
--                           && apply sub1 (nub nodePredicates) == ps
--                           && Set.fromList (apply sub1 <$$> vars') == Set.fromList vs
--  where
--    ((p, vars), sub, context) = runInferWithEnvs (inferPattern pat)
--
--runInferWithEnvs :: InferStack Maybe a -> (a, TypeSubstitution, Context)
--runInferWithEnvs = fromJust . runInfer mempty testClassEnv testTypeEnv testConstructorEnv
--
------runInferWithEnvs :: (Monoid t) => InferStack t a -> Either (InferError t) (a, TypeSubstitution, Context)
----runInferWithEnvs = undefined -- runInfer mempty testClassEnv testTypeEnv testConstructorEnv
----
------failInferPattern :: (Show t, Monoid t) => Text -> ProgPattern t -> (Error -> Bool) -> SpecWith ()
----failInferPattern expl pat isExpected = undefined -- do
------    describe ("The pattern " <> prettyText pat) $
------        case runInferWithEnvs (runWriterT (inferPattern pat)) of
------            Left (InferError _ _ err _) -> 
------                it ("✗ is not well-typed: (" <> expl <> ")") $ isExpected err
------            Right{} -> 
------                error "was expected to fail"
----
------succeedInferPattern :: (Show t, Monoid t) => ProgPattern t -> Type -> [Predicate] -> [(Name, Type)] -> SpecWith ()
----succeedInferPattern pat ty ps vs = do
----    undefined
------    case runInferWithEnvs (runWriterT (inferPattern pat)) of
------        Left e -> error (show e)
------        Right ((pat, vars), sub, context) -> do
------            describe ("The pattern " <> prettyText pat) $
------                it ("has type: " <> prettyText ty <> ", class constraints: " 
------                                 <> prettyText ps <> ", variables: " 
------                                 <> prettyText vs <> ", etc.") $
------                    let TypeInfo{..} = patternTag (apply sub pat)
------                        sub1 = normalizer nodeType
------                        vars' = apply sub <$$> vars
------                     in -- result = unify (apply sub1 nodeType) ty :: Either UnificationError TypeSubstitution
------                           -- in isRight result 
------                        apply sub1 nodeType ==  ty
------                             && apply sub1 (nub nodePredicates) == ps
------                             && Set.fromList (apply sub1 <$$> vars') == Set.fromList vs
--
--testInferPattern :: SpecWith ()
--testInferPattern = do
--
--    succeedInferPattern 
--        (varPat () "x") 
--        (tVar kTyp "a") 
--        [] 
--        [("x", tVar kTyp "a")]
--
--    succeedInferPattern 
--        (litPat () (TBool True))
--        tBool
--        [] 
--        []
--
--    succeedInferPattern 
--        (litPat () (TInt 5))
--        (tVar kTyp "a")
--        [InClass "Num" _a] 
--        []
--
--    succeedInferPattern 
--        (conPat () "Some" [varPat () "x"])
--        (tApp (tCon kFun "Option") _a)
--        [] 
--        [("x", _a)]
--
--    succeedInferPattern 
--        (conPat () "Some" [litPat () (TInt 5)])
--        (tApp (tCon kFun "Option") _a)
--        [InClass "Num" _a] 
--        []
--
--    succeedInferPattern 
--        (conPat () "Some" [litPat () (TBool True)])
--        (tApp (tCon kFun "Option") tBool)
--        [] 
--        []
--
--    -- As-patterns
--    succeedInferPattern 
--        (asPat () "someX" (conPat () "Some" [varPat () "x"]))
--        (tApp (tCon kFun "Option") _a)
--        [] 
--        [("x", _a), ("someX", tApp (tCon kFun "Option") _a)]
--
--    succeedInferPattern 
--        (asPat () "asSomeX" (asPat () "someX" (conPat () "Some" [varPat () "x"])))
--        (tApp (tCon kFun "Option") _a)
--        [] 
--        [("x", _a), ("someX", tApp (tCon kFun "Option") _a), ("asSomeX", tApp (tCon kFun "Option") _a)]
--
--    -- Or-patterns
--    succeedInferPattern 
--        (orPat () (conPat () "Some" [litPat () (TInt 1)]) (conPat () "Some" [litPat () (TInt 2)]))
--        (tApp (tCon kFun "Option") _a)
--        [InClass "Num" _a] 
--        []
--
--    -- Wildcard patterns
--    succeedInferPattern 
--        (anyPat ())
--        _a
--        [] 
--        []
--
--    -- Tuple patterns
--    succeedInferPattern 
--        (tuplePat () [litPat () (TBool True), varPat () "x"])
--        (tTuple [tBool, _a])
--        [] 
--        [("x", _a)]
--
--    -- List patterns
--    succeedInferPattern 
--        (listPat () [litPat () (TBool True), litPat () (TBool False)])
--        (tList tBool)
--        [] 
--        []
--
--    succeedInferPattern 
--        (listPat () [litPat () (TBool True), varPat () "x"])
--        (tList tBool)
--        [] 
--        [("x", tBool)]
--
--    -- Record pattern
--
--    succeedInferPattern 
--        (recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)))
--        (tRecord (rowToType (rExt "id" _a (rExt "name" _b rNil))))
--        [] 
--        [("id", _a), ("name", _b)]
--
--    succeedInferPattern 
--        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") rNil)))
--        (tRecord (rowToType (rExt "id" _a (rExt "name" _b rNil))))
--        [] 
--        [("id", _a), ("name", _b)]
--
----    succeedInferPattern 
----        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") (rVar "r"))))
----        (tRecord (rowToType (rExt "id" _a (rExt "name" _b (rVar "c")))))
----        [] 
----        [("id", _a), ("name", _b)]
--
--    -- Failures
--
----    succeedInferPattern 
----        (listPat () [litPat () (TBool True), litPat () (TInt 5)])
----        _a
----        []
----        []
----
------    failInferPattern "List type unification fails"
------        (listPat () [litPat () (TBool True), litPat () TUnit])
------        (\case { ListPatternTypeUnficationError -> True; _ -> False })
------
------    failInferPattern "Constructor arity doesn't match given arguments"
------        (conPat () "Some" [litPat () (TInt 5), litPat () (TInt 5)])
------        (== ConstructorPatternArityMismatch "Some" 1 2)
------
------    failInferPattern "No such data constructor"
------        (conPat () "Done" [litPat () (TInt 5)])
------        (== NoDataConstructor "Done")
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testInferExprType :: SpecWith ()
testInferExprType = do

    succeedInferExpr
        (varExpr () "x") 
        (tVar kTyp "a") 

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TInt 5)])
        (tVar kTyp "a") 
--        (HasPredicates [InClass "Num" "a"])

    succeedInferExpr
        (appExpr () [varExpr () "id", annExpr tInt (litExpr () (TInteger 5))])
        tInt

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TBool True)])
        tBool

    succeedInferExpr
        (varExpr () "id")
        (tVar kTyp "a" `tArr` tVar kTyp "a") 

    succeedInferExpr
        (conExpr () "(::)" [litExpr () (TBool True), conExpr () "[]" []])
        (tList tBool)

    succeedInferExpr
        (listExpr () [litExpr () (TBool True)])
        (tList tBool)

    succeedInferExpr
        -- let x = () in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () TUnit) (varExpr () "x"))
        tUnit

    succeedInferExpr
        -- let x = 5 in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () (TInteger 5)) (varExpr () "x"))
        (tVar kTyp "a") 
--        (HasPredicates [InClass "Num" "a"])

    succeedInferExpr
        (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
        tInt

    succeedInferExpr
        (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
        tInt

    -- { a = (), b = 2 }.a
    succeedInferExpr
        (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
        tUnit

    -- let c = (_ => True) in { a = (), b = 2 }.c
    succeedInferExpr
        (letExpr () (BPat () (varPat () "c"))
            (lamExpr () [anyPat ()] (litExpr () (TBool True)))
            (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
        tBool

    -- let c(_) = True in { a = (), b = 2 }.c
    succeedInferExpr
        (letExpr () (BFun () "c" [anyPat ()])
            (litExpr () (TBool True))
            (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
        tBool

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
        tInt

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (varExpr () "f"))
        (tVar kTyp "a" `tArr` tVar kTyp "a")

    succeedInferExpr
        (funExpr () [ Clause () (conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]) [Guard [] (litExpr () (TBool True))] , Clause () (conPat () "[]" []) [Guard [] (litExpr () (TBool True))] , Clause () (conPat () "(::)" [varPat () "z", varPat () "zs"]) [Guard [] (litExpr () (TBool True))] ])
        (tList (tVar kTyp "a") `tArr` tBool)


testInferRecordExpr :: SpecWith ()
testInferRecordExpr = do

    -- let f(z) = { a = 1 : Int | z } in f({ b = 2 }) 
    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
        -- { a : Int, b : Int }
        (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

    -- ((z) => { a = 1 : Int | z })({ b = 2 : Int })
    succeedInferExpr
        (appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))), recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])
        (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

    -- (z) => { a = 1 : Int | z }
    succeedInferExpr
        (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))))
        (tRecord (tVar kRow "r") `tArr` tRecord (tRow "a" tInt (tVar kRow "r")))

    -- ({ a = a | z }) => z
    succeedInferExpr
        (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"))
        -- { a : a | r } -> { r }
        (tRecord (tRow "a" (tVar kTyp "a") (tVar kRow "r")) `tArr` tRecord (tVar kRow "r"))

    -- (({ a = a | z }) => z)({ a = 1 })
    succeedInferExpr
        (appExpr () 
            [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
            , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) ])
        -- {}
        (tRecord (tCon kRow "{}"))

    -- (({ a = a | z }) => z)({ a = 1, b = 2, d = 3 })
    succeedInferExpr
        (appExpr () 
            [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
            , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) 
                            (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) 
                            (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) 
                            (conExpr () "{}" [])))) ])
        (tRecord (tRow "b" tInt (tRow "d" tInt tRowNil)))

    succeedInferExpr
        (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () (conPat () "Some" [varPat () "y"]) [ Guard [] (varExpr () "y") ] , Clause () (conPat () "None" []) [ Guard [] (varExpr () "val") ] ]) (varExpr () "withDefault"))
        (tVar kTyp "a" `tArr` tApp kTyp (tCon kFun "Option") (tVar kTyp "a") `tArr` tVar kTyp "a")



testInferPatternType :: SpecWith ()
testInferPatternType = do

    succeedInferPattern 
        (varPat () "x") 
        (tVar kTyp "a") 
        -- (HasVariable "x" (tVar kTyp "a"))
--        [("x", tVar kTyp "a")]

    succeedInferPattern 
        (litPat () (TBool True))
        tBool

    succeedInferPattern 
        (litPat () (TInt 5))
        (tVar kTyp "a")
--        [InClass "Num" _a] 

    succeedInferPattern 
        (conPat () "Some" [varPat () "x"])
        (tApp kTyp (tCon kFun "Option") (tVar kTyp "a"))

    succeedInferPattern 
        (conPat () "Some" [litPat () (TInt 5)])
        (tApp kTyp (tCon kFun "Option") (tVar kTyp "a"))
--        [InClass "Num" _a] 

    succeedInferPattern 
        (conPat () "Some" [annPat tInt (litPat () (TInteger 5))])
        (tApp kTyp (tCon kFun "Option") tInt)

    succeedInferPattern 
        (asPat () "someX" (conPat () "Some" [varPat () "x"]))
        (tApp kTyp (tCon kFun "Option") (tVar kTyp "a"))
--        [InClass "Num" _a] 


--    succeedInferExpr
--        (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x"))
--        _a
--        [] -- InClass "Num" (tVar kTyp "a")] 
--        []
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testTypeEnv :: TypeEnv
--testTypeEnv = Env.fromList
--    [ ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
--    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
--    , ( "Foo"    , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
--    , ( "id"     , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
--    , ( "(::)"   , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
--    , ( "[]"     , Forall [kTyp] [] (tList (tGen 0)) )
--    ]
--
--testClassEnv :: ClassEnv
--testClassEnv = Env.fromList
--    [ ( "Show"
--        -- Interface
--      , ( ClassInfo [] (InClass "Show" "a") 
--            [ ( "show", tVar kTyp "a" `tArr` tString )
--            ]
--        -- Instances
--        , [ ClassInfo [] (InClass "Show" tInt)
--              [ ( "show", Ast (varExpr (TypeInfo (tInt `tArr` tString) [] ()) "@Int.Show") )
--              ]
--          , ClassInfo [] (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b")))
--              [ ( "show", Ast (varExpr (TypeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) [] ()) "TODO") )
--              ]
--          ]
--        )
--      )
--    , ( "Ord"
--        -- Interface
--      , ( ClassInfo [] (InClass "Ord" "a") 
--            [ ( "(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
--            , ( "(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
--            , ( "(>=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
--            , ( "(<=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
--            ]
--        -- Instances
--        , []
--        )
--      )
--    , ( "Eq"
--        -- Interface
--      , ( ClassInfo [InClass "Ord" "a"] (InClass "Eq" "a")
--            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
--            ]
--        -- Instances
--        , [ ClassInfo [] (InClass "Eq" tInt)
--              [ ( "(==)", Ast (varExpr (TypeInfo (tInt `tArr` tInt `tArr` tBool) [] ()) "@Int.(==)" ) )
--              ]
--          ]
--        )
--      )
--    , ( "Num"
--        -- Interface
--      , ( ClassInfo [] (InClass "Num" "a") 
--            [ ( "(+)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
--            ]
--        -- Instances
--        , []
--        )
--      )
--    ]
--
--testConstructorEnv :: ConstructorEnv
--testConstructorEnv = constructorEnv
--    [ ("Some"     , ( ["Some", "None"], 1 ))
--    , ("None"     , ( ["Some", "None"], 0 ))
--    , ("[]"       , ( ["[]", "(::)"], 0 ))
--    , ("(::)"     , ( ["[]", "(::)"], 2 ))
--    , ("(,)"      , ( ["(,)"], 2 ))
--    , ("Foo"      , ( ["Foo"], 2 ))
--    ]
