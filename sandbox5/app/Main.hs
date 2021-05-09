{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Main where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Maybe (fromJust)
import Data.Text (unpack)
import Data.Tree.View (showTree)
import Tau.Compiler.Error
import Tau.Compiler.Substitute
import Tau.Compiler.Translate
import Tau.Compiler.Typecheck
import Tau.Compiler.Unify
import Tau.Core
import Tau.Eval
import Tau.Env
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Tool
import Tau.Type
import qualified Tau.Compiler.Substitute as Sub
import qualified Tau.Env as Env

---- ----test3 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
---- ----  where
---- ----    r1 = tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow)
---- ----    r2 = tRowExtend "id" tString (tRowExtend "name" tInt tEmptyRow)
---- ----
---- ----test4 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
---- ----  where
---- ----    r1 = tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow)
---- ----    r2 = tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow)
---- ----
---- ----test5 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
---- ----  where
---- ----    r1 = tRowExtend "x" tInt (tVar kRow "r")
---- ----    r2 = tRowExtend "x" tInt (tVar kRow "r")
---- ----
---- ----test6 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
---- ----
---- ----r1 = tRowExtend "x" tInt (tVar kRow "r")
---- ----r2 = tRowExtend "y" tInt (tVar kRow "r")
---- ----
---- ----
---- ----pattern1 = recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)) 
---- ----
---- ------pattern1 = conPat () "Foo" [litPat () (TBool True), litPat () (TInt 5)]
---- ------pattern1 = conPat () "Done" [litPat () (TInt 5), litPat () (TInt 5)]
---- ------pattern1 = conPat () "Some" [litPat () (TInt 5), litPat () (TInt 5)]
---- ------pattern1 = listPat () [litPat () (TBool True), litPat () TUnit]
---- ------pattern1 = listPat () [litPat () (TBool True), litPat () (TInt 5)]
---- ------pattern1 = asPat () "someX" (conPat () "Some" [varPat () "x"])
---- ------pattern1 = (conPat () "Some" [varPat () "x"])
---- --
---- ----pattern1 = recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil))
---- ----pattern1 = recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") rNil))
---- --
---- --pattern1 = tuplePat () [litPat () (TString "foo"), litPat () (TBool True)]
---- --
---- --test1 :: IO ()
---- --test1 = 
---- --    case runInfer mempty testClassEnv testTypeEnv testConstructorEnv (runWriterT (inferPattern pattern1)) of
---- --        Left e -> error (show e)
---- --        Right ((pat, vars), sub, context) -> do
---- --            let TypeInfo{..} = patternTag (apply sub pat)
---- --                vars' = apply sub <$$> vars
---- --                sub1 = normalizer nodeType
---- --                xx1 = apply sub1 nodeType
---- --                xx2 = apply sub1 nodePredicates
---- --                xx3 = apply sub1 <$$> vars'
---- --              in do
---- --                  print (apply sub (typeOf pat))
---- --                  --print (normalize (apply sub (typeOf pat)))
---- --                  --print sub
---- --                  --print ">>>>"
---- --                  --print nodeType 
---- --                  --print nodePredicates
---- --                  --print vars'
---- --                  --print ">>>>"
---- --                  --print xx1
---- --                  --print xx2
---- --                  --print xx3
---- --                  pure ()
---- --
---- --expr1 = funExpr () 
---- --    [ Clause [ varPat () "x" ] [ Guard [] (litExpr () (TInt 1)) ] 
---- --    ]
---- --
---- --test2 :: IO ()
---- --test2 = 
---- --    case runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExpr expr1) of
---- --        Left e -> error (show e)
---- --        Right (expr, sub, context) -> do
---- --            print (expr, sub, context)
---- --            print "..."
---- --            print (apply sub expr)
---- --            print "///"
---- --            print context
---- --            --let TypeInfo{..} = exprTag (apply sub expr)
---- --            --    sub1 = normalizer nodeType
---- --            --    xx1 = apply sub1 nodeType
---- --            --    xx2 = apply sub1 nodePredicates
---- --            --  in do
---- --            --    --  print (normalize (apply sub (typeOf pat)))
---- --            --    --  print sub
---- --            --    --  print ">>>>"
---- --            --    print nodeType 
---- --            --    print nodePredicates
---- --            --    --  print vars'
---- --            --    print ">>>>"
---- --            --    print (pretty xx1)
---- --            --    print (pretty xx2)
---- --            --    pure ()
---- 
---- 
---- -- fun | x => 5
---- --test1 :: (ProgExpr (TypeInfo [Error]), TypeSubstitution, Context)
---- test1 = do
----     print "----------"
---- --    print (apply sub x)
---- --    print z
---- 
----     let xxx = unpack . renderDoc <$> zz
----     putStrLn (showTree xxx)
---- 
---- --    print (pretty (normalized (apply sub x)))
----     print "=========="
----   where
---- 
----     zz = simplifiedExprTree z
----     z = fromJust (evalSupply (simplifyExpr y) (nameSupply "a"))
----     y = getAst (apply sub x)
----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
----     e = inferAst (Ast (funExpr () [ Clause () [varPat () "x"] [Guard [] (litExpr () (TInt 5))] ]))

normalized :: Ast (TypeInfo e) -> Ast (TypeInfo e)
normalized ast = apply (normalizer (astTypeVars ast)) ast 

---- --test2 = do
---- --    print "----------"
---- --    print (apply sub p)
---- --    print "=========="
---- --    print (apply sub <$$> vars)
---- --    print "=========="
---- --  where
---- --    ((p, vars), sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferPattern (conPat () "Some" [varPat () "x"])
---- --
---- --
---- --test3 = do
---- --    print "----------"
---- --    print (apply sub p)
---- --    print "=========="
---- --    print (apply sub <$$> vars)
---- --    print "=========="
---- --    print sub
---- --    print "=========="
---- --  where
---- --    ((p, vars), sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferPattern (listPat () [litPat () (TBool True), varPat () "x"])
---- --
---- --
---- --test4 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (normalized (apply sub x)))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
---- --
---- --
---- --
---- --test5 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (normalized (apply sub x)))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (conExpr () "(::)" [litExpr () (TBool True), conExpr () "[]" []]))
---- --
---- --
---- --
---- --test6 = do
---- --    print "----------"
---- ----    print (apply sub x)
---- --    print (pretty (normalized (apply sub x)))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst
---- --        (Ast (appExpr () 
---- --            [ funExpr () [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
---- --                [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3)), op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1))
---- --                , Guard [] (litExpr () (TInt 1))
---- --                ] ]
---- --            , conExpr () "Some" [litExpr () TUnit] ]))
---- --
---- --
---- --test66 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (funExpr () [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
---- --        [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
---- --        , Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 2)) 
---- --        , Guard [] (litExpr () (TInt 3)) 
---- --        ] ]))
---- --
---- --test67 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    --
---- --    let Ast e1 = typeOf <$> apply sub x
---- --    let e2 = simplifyExpr e1
---- --    print (e2)
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (patExpr () [varExpr () "xs"] [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
---- --        [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
---- --        , Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 2)) 
---- --        , Guard [] (litExpr () (TInt 3)) 
---- --        ] ]))
---- --
---- --
---- --
---- --
---- ----test66 :: ProgExpr ()
---- ----test66 = funExpr () 
---- ----    [ Clause () [conPat () "Some" [litPat () (TBool True)], conPat () "Some" [litPat () (TBool True)] ] [Guard [] (litExpr () (TInt 1))] 
---- ----    , Clause () [conPat () "Some" [litPat () (TBool True)] ] [Guard [op2Expr () (litExpr () (TInt 4)) (litExpr () (TInt 4))] (litExpr () (TInt 1))] 
---- ----    ]
---- --
---- --
---- --test7 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
---- --
---- --
---- --test8 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print ctx
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
---- --
---- --
---- --test9 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print ctx
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (op2Expr () (OEq ()) (litExpr () (TInt 1)) (litExpr () (TInt 1))))
---- --
---- --
---- --test10 =
---- --    Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x"))
---- --
---- --
---- --test11 =
---- --    Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (varExpr () "x"))
---- --
---- --
---- --test12 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print ctx
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () (TInt 1), litExpr () (TInt 1)])))
---- --
---- --
---- --test14 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print ctx
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
---- --
---- --
---- --test15 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    print ctx
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TBool True)]))
---- 
--
----test16 = do
----    print "x"
----    --print (pretty (apply sub x))
----
----    --let Ast e1 = typeOf <$> apply sub x
----    let Ast e1 = const () <$> apply sub x
----    let e2 = evalSupply (simplifyExpr e1) (nameSupply "a")
----    print e2
--
----   where
----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv b)
----     b = inferAst (Ast e)
----     --c = apply sub x
----     --d = simplifyExpr c
---- --    print (apply sub x)
----     --
---- 
----     e :: ProgExpr ()
----     e = letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit, litExpr () TUnit])
---- 
---- 
---- test17 = do
----     print "y"
----     let Ast e1 = typeOf <$> apply sub x
----     let e2 = fromJust (evalSupply (simplifyExpr e1) (nameSupply "a"))
----     let fff = simplifiedExprTree e2
----     let xxx = unpack . renderDoc <$> fff
----     putStrLn (showTree xxx)
----     print (e2)
---- 
----   where
----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv b)
----     b = inferAst (Ast e)
---- 
----     e :: ProgExpr ()
----     e = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) rNil :: Row (ProgExpr ())))
---- --    e = listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]
---- 
---- --    e = tupleExpr () [litExpr () (TInt 1), litExpr () (TString "Bob")]
---- 
---- test18 = desugarRow exprTag conExpr (rExt "name" (litExpr tString (TString "Bob")) (rExt "id" (litExpr tInt (TInt 1)) rNil :: Row (ProgExpr Type)))
---- 
---- test19 = desugarRow exprTag conExpr (rNil :: Row (ProgExpr Type))
---- 
---- test20 = desugarRow exprTag conExpr (rExt "id" (litExpr tInt (TInt 1)) rNil :: Row (ProgExpr Type))
---- 
---- test21 = desugarRow exprTag conExpr (rVar (varExpr (tCon kRow "a") "r") :: Row (ProgExpr Type))
---- 
---- --test16 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (apply sub x))
---- --    let (Ast e) = typeOf <$> apply sub x
---- --        e1 = translateRecords e
---- --    print e1
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    --e = inferAst (Ast (recordExpr () (rExt "name" (litExpr () (TInt 1)) ((rExt "name" (litExpr () (TString "Foo")) (rExt "id" (litExpr () (TInt 123)) rNil :: Row (ProgExpr ())))))))
---- --    e = inferAst (Ast (recordExpr () (rExt "id" (litExpr () (TInt 1)) rNil :: Row (ProgExpr ()))))
--
--test123 = do
--    print sub
--    print y
--  where
--    Ast y = apply sub x
--    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
--    e = inferAst (Ast (e1 :: ProgExpr ()))
--    --e1 = op1Expr () (ONeg ()) (varExpr () "x")
--    --e1 = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) rNil))
--    --e1 = (op2Expr () (OEq ()) (varExpr () "x") (varExpr () "y"))
--    e1 = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) (rVar (varExpr () "r"))))
--
--
--test456 = simplifyExpr2 (lamExpr (ti (tInt `tArr` tInt `tArr` tString)) [varPat (ti tInt) "p", varPat (ti tInt) "q"] (litExpr (ti tString) (TString "abc")))
----     let fff = simplifiedExprTree e2
--
------test456_ = simplifyExpr2 (lamExpr () [varPat () "p"] (litExpr () (TString "abc")))
----
------test456 = simplifyExpr2 (lamExpr (ti (tInt `tArr` tString)) [varPat (ti tInt) "p"] (litExpr (ti tString) (TString "abc")))
----
----xxx123 :: Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> SimplifiedExpr t
----xxx123 = cata $ \case
----    EVar    t var        -> varExpr t var
----    ECon    t con es     -> conExpr t con es
----    ELit    t prim       -> litExpr t prim
----    EApp    t es         -> appExpr t es
----    EFix    t name e1 e2 -> fixExpr t name e1 e2
----    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
----    EPat    t es cs      -> patExpr t es undefined
----    ELam    t ps e       -> lamExpr t ps e
--
--
--ti :: Type -> TypeInfo [Error]
--ti t = TypeInfo t [] []

test1 = do -- case fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExprType expr1)) of
    print "----------"
    print (apply sub a)
    print "=========="
--    Left e -> error (show e)
--    Right (expr, sub, context) -> do
--        print (expr, sub, context)
--        print "..."
--        print (apply sub expr)
  where
    (a, sub, _, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv expr)
    expr = inferAst (Ast (varExpr () "x"))


mapAst :: (a -> b) -> ProgExpr a -> ProgExpr b
mapAst f e = zz
  where
    xx = Ast e
    yy = fmap f xx
    zz = getAst yy


test2 = do -- case fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExprType expr1)) of
    print "----------"
    print (apply sub2 (apply sub a))
    print "----------"
    putStrLn (showTree h)
    print "=========="
    print xx
    print "=========="
    putStrLn (showTree zz)
--    Left e -> error (show e)
--    Right (expr, sub, context) -> do
--        print (expr, sub, context)
--        print "..."
--        print (apply sub expr)
  where
--    e :: ProgExpr (TypeInfo [Error])
--    e = getAst (apply sub a)

    h = unpack . renderDoc <$> g
    g = exprTree (getAst ee)

    f :: Ast Type
    f = typeOf <$> (apply sub a)

    ee :: Ast (TypeInfo [Error])
    ee = (apply sub a)

    eee :: Ast (TypeInfoT [Error] (Maybe Type))
    eee = fmap (fmap Just) ee

    --xx = simplifyExpr yyyy -- (getAst ee)
    --xx = simplifyExpr (getAst ee)
    xx :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
    xx = stage1 (getAst eee)

--    yyyy = mapAst (const ()) (getAst ee)

    yy = exprTree xx
    zz = unpack . renderDoc <$> yy

    (a, sub, sub2, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv expr)
--    expr = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))

--    expr = inferAst (Ast (varExpr () "(+)"))

--    expr = inferAst (Ast (litExpr () (TInt 5)))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))

--    expr = inferAst (Ast (letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")))

--    expr = inferAst (Ast (letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])))

--    expr = inferAst (Ast (varExpr () "(::)"))

--    expr = inferAst (Ast (appExpr () [varExpr () "(::)", litExpr () (TInt 5), conExpr () "[]" []]))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (varExpr () "id") (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TString "foo")], appExpr () [varExpr () "id", litExpr () (TInt 1)]])))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))))

--    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr ()  [varExpr () "f", litExpr () (TInt 1)])))

--    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")))

--    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (varExpr () "f")))

--    expr = inferAst (Ast (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "y")))

--    expr = inferAst (Ast (funExpr () [ Clause () [varPat () "x"] [Guard [] (litExpr () (TBool True))] ]))

--    expr = inferAst (Ast (funExpr () [ Clause () [conPat () "Some" [varPat () "x"]] [Guard [] (litExpr () (TBool True))] ]))


    expr = inferAst (Ast (letExpr () (BLet () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TInt 5)], appExpr () [varExpr () "id", litExpr () (TBool True)]])))

--    expr = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4)]))


test3 = u :: Either UnificationError (Substitution Type, Substitution Kind)
  where
--    u = unifyTypes (tVar (kVar "k1") "a1") tInt

--    u = unifyTypes (tVar kTyp "a1") tInt
--    u = unifyTypes (tVar kTyp "a1") (tVar kTyp "a1" `tArr` tVar kTyp "a1")

    u = unifyTypes (tVar (kArr (kVar "k1") (kVar "k1")) "a1") (tVar (kVar "k1") "a1")

---- --test4 = do
---- --    print "----------"
---- --    print (apply sub x)
---- --    print (pretty (normalized (apply sub x)))
---- --    print "=========="
---- --  where
---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
---- --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))

--abc123 :: (MonadError UnificationError m) => m ()
--abc123 = do
--    sub <- unifyTypes tInt tInt
--    let x = apply sub (tVar kTyp "a")
--    pure ()

main :: IO ()
main = print "Main"

testKindEnv :: KindEnv
testKindEnv = Env.fromList
    [ ( "Num" , kArr kTyp kClass )
    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"   , Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Foo"    , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    , ( "id"     , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    , ( "(::)"   , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"     , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "(+)"    , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
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
              [ ( "show", Ast (varExpr (TypeInfo (tInt `tArr` tString) [] ()) "@Int.Show") )
              ]
          , ClassInfo [] (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b")))
              [ ( "show", Ast (varExpr (TypeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) [] ()) "TODO") )
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
            [ ( "(==)", Ast (varExpr (TypeInfo (tInt `tArr` tInt `tArr` tBool) [] ()) "@Int.(==)" ) )
            ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo [] (InClass "Num" "a") 
            [ ( "(+)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , []
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

--foz1 = case \x -> 1 of
--    f -> f ()
--
