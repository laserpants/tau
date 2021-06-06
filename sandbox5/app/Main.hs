{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
module Main where

import System.Environment 
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Aeson
import Data.Maybe (fromJust)
import Data.Text (unpack)
import Data.Tree.View (showTree)
import Tau.Compiler.Pipeline
import Tau.Compiler.Pipeline.Stage1
import Tau.Compiler.Pipeline.Stage2
import Tau.Compiler.Pipeline.Stage3
import Tau.Compiler.Pipeline.Stage4
import Tau.Compiler.Pipeline.Stage5
import Tau.Compiler.Pipeline.Stage6
import Tau.Parser
import Tau.Compiler.Error
import Tau.Compiler.Substitute
import Tau.Serialize
--import Tau.Compiler.Translate
import Tau.Compiler.Typecheck
import Tau.Compiler.Unify
import Tau.Core
import Tau.Env
import Tau.Eval
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tool
import Tau.Type
import Text.Megaparsec
import qualified Tau.Compiler.Substitute as Sub
import qualified Tau.Env as Env
import qualified Data.ByteString.Lazy as LBS

import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6


instance Typed (Maybe Type) where
    typeOf (Just t) = t
    typeOf Nothing  = tVar (kVar "k") "a"

--------------------------
--------------------------
--------------------------

data TypeFocus
    = TAppLeft  Kind Type
    | TAppRight Kind Type
    | TArrLeft  Type
    | TArrRight Type
    deriving (Show, Eq)

type TypeZipper = (Type, [TypeFocus])

tAppLeft :: TypeZipper -> Maybe TypeZipper
tAppLeft (Fix (TApp k l r), fs) = Just (l, TAppLeft k r:fs)
tAppLeft _ = Nothing

tAppRight :: TypeZipper -> Maybe TypeZipper
tAppRight (Fix (TApp k l r), fs) = Just (r, TAppRight k l:fs)
tAppRight _ = Nothing

tAppUp :: TypeZipper -> Maybe TypeZipper
tAppUp (t, TAppLeft  k r:fs) = Just (tApp k t r, fs)
tAppUp (t, TAppRight k l:fs) = Just (tApp k l t, fs)
tAppUp _ = Nothing

tArrLeft :: TypeZipper -> Maybe TypeZipper
tArrLeft (Fix (TArr l r), fs) = Just (l, TArrLeft r:fs)
tArrLeft _ = Nothing

tArrRight :: TypeZipper -> Maybe TypeZipper
tArrRight (Fix (TArr l r), fs) = Just (r, TArrRight l:fs)
tArrRight _ = Nothing

tArrUp :: TypeZipper -> Maybe TypeZipper
tArrUp (t, TArrLeft  r:fs) = Just (tArr t r, fs)
tArrUp (t, TArrRight l:fs) = Just (tArr l t, fs)
tArrUp _ = Nothing

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


--mapAst :: (a -> b) -> ProgExpr a -> ProgExpr b
mapAst f e = zz
  where
    xx = Ast e
    yy = fmap f xx
    zz = getAst yy


evalEnv2 = Env.fromList 
    [ -- ( "(,)" , constructor "(,)" 2 )
    ]

--test2 = do -- case fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExprType expr1)) of
--    print "----------"
--    print (apply sub2 (apply sub a))
--    print "----------"
--    putStrLn (showTree h)
--    print "=========="
--    print xx
--    print "=========="
--    putStrLn (showTree zz)
--    print "=========="
--    putStrLn (showTree zz2)
--    print "=========="
--    putStrLn (showTree zz22)
--    print "=========="
--    putStrLn (showTree zz222)
----    print "=========="
----    print xx222
----    print "=========="
----    print xx2
----    print "=========="
----    print xx22
----    print "=========="
----    print xx222
----    print "=========="
--    --putStrLn (showTree zz22)
--    --print "=========="
----    print xx3
----    print "=========="
----    print (evalExpr xx3 evalEnv2)
----    print "=========="
--    --putStrLn (showTree zz123)
----    Left e -> error (show e)
----    Right (expr, sub, context) -> do
----        print (expr, sub, context)
----        print "..."
----        print (apply sub expr)
--  where
----    e :: ProgExpr (TypeInfo [Error])
----    e = getAst (apply sub a)
--
--    h = unpack . renderDoc <$> g
--    g = exprTree (getAst ee)
--
--    f :: Ast Type
--    f = typeOf <$> (apply sub a)
--
--    ee :: Ast (TypeInfo [Error])
--    ee = apply sub a
--
--    eee :: Ast (TypeInfoT [Error] (Maybe Type))
--    eee = fmap (fmap Just) ee
--
--    --xx = simplifyExpr yyyy -- (getAst ee)
--    --xx = simplifyExpr (getAst ee)
----    xx :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
--    xx = stage1 (getAst eee)
--
----    xx2 :: Stage3Expr (TypeInfoT [Error] (Maybe Type))
--    xx2 = stage3 xx
--
--    xx22 :: Stage4Expr (TypeInfoT [Error] (Maybe Type))
--    xx22 = stage4 xx2
--
--    xx22_ :: Stage5Expr (Maybe Type)
--    xx22_ = foo5 nodeType xx22
--
--    xx222 :: Stage6Expr (Maybe Type)
--    xx222 = fromJust $ evalSupply (stage6 xx22_) (nameSupply "$")
--
--    xx3 :: Core
--    xx3 = undefined -- runIdentity (toCore xx2)
--
--    xx123 :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
--    xx123 = fromJust (evalSupply (runReaderT (evalStateT (compileClasses xx) []) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)) (nameSupply ""))
--
----    yyyy = mapAst (const ()) (getAst ee)
--
--    yy = exprTree xx
--    zz = unpack . renderDoc <$> yy
--
--    yy2 = exprTree xx2
--    zz2 = unpack . renderDoc <$> yy2
--
--    yy22 = exprTree xx22
--    zz22 = unpack . renderDoc <$> yy22
--
--    yy222 = exprTree3 xx222
--    zz222 = unpack . renderDoc <$> yy222
--
--    yy123 = exprTree xx123
--    zz123 = unpack . renderDoc <$> yy123
--
--    (a, sub, sub2, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv expr)
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



--    expr = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4)]))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (appExpr () [varExpr () "id", litExpr () (TInt 5)])))

--    expr = inferAst (Ast (lamExpr () [varPat () "a", varPat () "b"] (appExpr () [varExpr () "(,)", varExpr () "a", varExpr () "b"])))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TInt 5)], appExpr () [varExpr () "id", litExpr () (TBool True)]])))

--    expr = inferAst (Ast (patExpr () [litExpr () (TInt 5)] [Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]]))

--    expr = inferAst (Ast (patExpr () [litExpr () (TInt 4)] 
--             [ Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]
--             , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
--             ]))

--    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] [Clause () [anyPat ()] [Guard [] (litExpr () (TInt 1))]])))

--    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
--        [ Clause () [varPat () "y"] [Guard [] (litExpr () (TInt 1))] 
--        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
--        ])))

test555, test556 :: Type
--test555 = Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{a}")) (Fix (TVar (Fix (KCon "*")) "a5")))) (Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{b}")) (Fix (TArr (Fix (TVar (Fix (KVar "k10")) "a11")) (Fix (TVar (Fix (KVar "k10")) "a11")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))

test555 = tRowExtend "b" tInt (tRowExtend "a" tString (tRowExtend "c" tBool tRowNil))

test556 = tRowExtend "b" tInt (tRowExtend "a" tString (tRowExtend "c" tBool (tVar kRow "x")))

--test555 = Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{b}")) (Fix (TCon (Fix (KCon "*")) "Int")))) (Fix (TCon (Fix (KCon "Row")) "{}")))

test123 expr = do
    let xx = toRep (getAst ee)
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData2.json" (encode xx)
    let xx1 = toRep ef
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData3.json" (encode xx1)
    let xx2 = toRep eh
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData4.json" (encode xx2)
    let xx3 = toRep ei
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData5.json" (encode xx3)
    let xx4 = toRep ej
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData6.json" (encode xx4)
    let xx5 = toRep ek
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData7.json" (encode xx5)
    let xx6 = toRep el
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData8.json" (encode xx6)
    let xx7 = toRep em
    print "***********"
    print "***********"
    print "***********"
    print xx7
    LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData9.json" (encode xx7)
--    print a
--    putStrLn "---------------"
--    print ee
--    putStrLn "---------------"
--    print ef
--    putStrLn "---------------"
    putStrLn "---------------"
    putStrLn (showTree h)
    putStrLn "---------------"
    putStrLn (showTree h1)
    putStrLn "---------------"
    putStrLn (showTree h3)
    putStrLn "---------------"
    putStrLn (showTree h31)
    putStrLn "---------------"
    putStrLn (showTree h32)
    putStrLn "---------------"
    putStrLn (showTree h4)
    putStrLn "---------------"
    print el
    putStrLn "---------------"
    print em
    putStrLn "---------------"
--    print eh

--    putStrLn "---------------"
----    xx2
  where
    ee :: Ast (TypeInfo [Error])
    ee = apply sub2 (apply sub a)

    eee :: Ast (TypeInfoT [Error] (Maybe Type))
    eee = fmap (fmap Just) ee

    ef = Stage1.translate (getAst eee)

    eg = Stage2.translate ef

    eh :: Stage2.WorkingExpr (Maybe Type)
    eh = fromJust (evalSupply (runReaderT (evalStateT eg []) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)) (numSupply "a"))

    ei = fromJust (evalSupply (Stage3.translate eh) (numSupply "#"))

    ej = Stage4.translate ei

    ek = fromJust (evalSupply (Stage5.translate ej) (numSupply "a"))

    el = runIdentity (Stage6.translate ek)

    em = evalExpr el evalEnv2

    h3 = unpack . renderDoc <$> g3
    g3 = exprTree eh

    h31 = unpack . renderDoc <$> g31
    g31 = exprTree ei

    h32 = unpack . renderDoc <$> g32
    g32 = exprTree ej

--    xx :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
--    xx = Stage1.translate (getAst eee)

    h4 = unpack . renderDoc <$> g4
    g4 = exprTree3 ek

--    xx22_ :: Stage5Expr (Maybe Type)
--    xx22_ = foo5 nodeType ek

    h1 = unpack . renderDoc <$> g1
    g1 = exprTree ef
--
    h = unpack . renderDoc <$> g
    g = exprTree (getAst ee)
--
--    xx2 :: Stage3Expr (Maybe Type)
--    xx2 = Stage3.translate (mapExpr2 nodeType xx)

    (a, sub, sub2, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv prog)

    prog = inferAst (Ast expr)

--    expr :: ProgExpr ()
--    --expr = lamExpr () [varPat () "x", varPat () "y"] (appExpr () [varExpr () "(+)", varExpr () "x", varExpr () "y"])

--    expr :: ProgExpr ()
    --expr = op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () (TInt 2))

--    expr = letExpr () (BLet () (varPat () "v")) (op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () (TInt 2))) ((op2Expr () (OAdd ()) (varExpr () "v") (litExpr () (TInt 2))))

--    expr = litExpr () (TInt 2)

--    expr = varExpr () "(+)"

--    expr = litExpr () (TInt 5)

--    expr = rowExpr () "name" (litExpr () (TString "Bob")) (Just (rowExpr () "id" (litExpr () (TInt 5)) Nothing))

--    expr = 
--        letExpr () (BLet () (varPat () "r")) (rowExpr () "isAdmin" (litExpr () (TBool True)) Nothing)
--        (rowExpr () "name" (litExpr () (TString "Bob")) (Just (rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (varExpr () "r")))))

--    expr = 
--        patExpr () [ litExpr () (TInt 5) ] 
--            [ Clause () [ litPat () (TInt 3) ] [ Guard [] (litExpr () (TBool True)) ]
--            , Clause () [ litPat () (TInt 5) ] [ Guard [] (litExpr () (TBool False)) ]
--            ]
--
--    expr = 
--        patExpr () ( conExpr () "Some" [litExpr () (TBool True)] ) 
--            [ Clause () ( conPat () "Some" [litPat () (TBool True)] ) [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ]
--            , Clause () ( conPat () "Some" [litPat () (TBool False)] ) [ Guard [] (litExpr () (TInt 2)) ]
--            ]
--

--    expr = 
--        funExpr () 
--            [ Clause () [ recordPat () (rowPat () "name" (varPat () "a") Nothing) ] [Guard [] (litExpr () (TBool True))]
--            ]

--    expr = Fix (EAnn tInt (litExpr () (TInt 5)))

--    expr = Fix (ERow () [("a", litExpr () (TInt 5)), ("b", lamExpr () [varPat () "x"] (varExpr () "x"))])

--w    expr = patExpr () [ rowExpr () [("name", litExpr () (TString "Bob"))] ] 
--        [ Clause () [ rowPat () [("name", varPat () "a")] ] [ Guard [] (varExpr () "a") ] ]

    -- match { id = 1, name = "Bob" } with
    --   | { name = a } => a
    --
    --   | { name = a | _ } => a
    --
    --expr = patExpr () [ rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (rowExpr () "name" (litExpr () (TString "Bob")) Nothing)) ] 
----    expr = patExpr () [ rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (rowExpr () "name" (litExpr () (TString "Bob")) Nothing)) ] 
------            [ Clause () [ rowPat () "name" (varPat () "a") Nothing ] [ Guard [] (varExpr () "a") ] ]
----            [ Clause () [ rowPat () "name" (varPat () "a") (Just (anyPat ())) ] [ Guard [] (varExpr () "a") ] ]

--    expr = patExpr () [ rowExpr () [("name", litExpr () (TString "Bob")), ("id", litExpr () (TBool True))] ] 
--        [ Clause () [rowPat () [("id", varPat () "b"), ("name", varPat () "a")]] [Guard [] (varExpr () "b")] ]

--    expr = Fix (ERow () [("a", litExpr () (TInt 5)), ("b", varExpr () "b")])

    -- match { name = "Bob", id = True } with
    --   | { id = b, name = a } => b

--    expr = letExpr () (BLet () (varPat () "x")) (rowExpr () [("id", litExpr () (TBool True))]) (rowExpr () [("name", litExpr () (TString "Bob")), ("*", varExpr () "x")])

--Guard [] (litExpr () (TInt 123))

--    expr = letExpr () (BLet () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")

--    expr = letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")

--    expr = letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])

--    expr = appExpr () 
--        [ letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])
--        , recordExpr () (rowCons () "fromInteger" (lamExpr () [varPat () "x"] (litExpr () (TInt 55))) (conExpr () "{}" [])) 
--        ]

--    expr = recordExpr () (rowCons () "fromInteger" (lamExpr () [varPat () "x"] (litExpr () (TInt 55))) (conExpr () "{}" [])) 

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



--    expr = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4)]))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (appExpr () [varExpr () "id", litExpr () (TInt 5)])))

--    expr = inferAst (Ast (lamExpr () [varPat () "a", varPat () "b"] (appExpr () [varExpr () "(,)", varExpr () "a", varExpr () "b"])))

--    expr = inferAst (Ast (letExpr () (BLet () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TInt 5)], appExpr () [varExpr () "id", litExpr () (TBool True)]])))

--    expr = inferAst (Ast (patExpr () [litExpr () (TInt 5)] [Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]]))

--    expr = inferAst (Ast (patExpr () [litExpr () (TInt 4)] 
--             [ Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]
--             , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
--             ]))

--    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] [Clause () [anyPat ()] [Guard [] (litExpr () (TInt 1))]])))

--    -- (\x => match x with | Some y => 1) (Some True)
--    expr = appExpr () [lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
--        [ Clause () [conPat () "Some" [varPat () "y"]] [Guard [] (annExpr tInt (litExpr () (TInt 1)))] 
--        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
--        ]), conExpr () "Some" [litExpr () (TBool True)]]

--    -- (\x => match x with | Some y => 1) None
--    expr = appExpr () [lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
--        [ Clause () [conPat () "Some" [varPat () "y"]] [Guard [] (annExpr tInt (litExpr () (TInt 1)))] 
--        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
--        ]), conExpr () "None" []]



--test557 :: Either UnificationError (Substitution Type, Substitution Kind)
--test557 = unifyTypes 
--    (tRowExtend "name" tString (tVar kRow "r"))
--    (tRowExtend "name" tString (tRowExtend "id" tInt))


test554 :: Either UnificationError (Substitution Type, Substitution Kind)
test554 = unifyTypes 
    (tRowExtend "name" tString (tVar kRow "r"))
    -- { name : String | r }
    (tRowExtend "id" tInt (tRowExtend "name" tString (tVar kRow "q")))
    -- { name : String | { id : Int } | q }

test557 :: Either UnificationError (Substitution Type, Substitution Kind)
test557 = unifyTypes 
    (tRowExtend "name" tString (tVar kRow "r"))
    -- { name : String | r }
    (tRowExtend "name" tString (tRowExtend "id" tInt (tVar kRow "q")))
    -- { name : String | { id : Int } | q }

test558 :: Either UnificationError (Substitution Type, Substitution Kind)
test558 = unifyTypes 
    (tRowExtend "name" tString (tVar kRow "r"))
    -- { name : String | r }
    (tRowExtend "name" tString (tRowExtend "id" tInt tRowNil))
    -- { name : String | { id : Int } | {} }

test559 :: Either UnificationError (Substitution Type, Substitution Kind)
test559 = unifyTypes 
    (tRowExtend "id" tInt (tRowExtend "name" tString tRowNil))
    -- { id : Int | { name : String | {} } }
    (tRowExtend "name" tString (tRowExtend "id" tInt tRowNil))
    -- { name : String | { id : Int | {} } }

mapExpr2 :: (t -> u) -> WorkingExpr t -> WorkingExpr u
mapExpr2 f = cata $ \case
    EVar    t var          -> varExpr    (f t) var
    EApp    t es           -> appExpr    (f t) es
    EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
    ELam    t ps e         -> lamExpr    (f t) (mapPattern <$> ps) e
    EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
    EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
    ELet    t bind e1 e2   -> letExpr    (f t) (mapBind bind) e1 e2
  where
    mapBind = \case
        BLet    t p        -> BLet       (f t) (mapPattern p)
        BFun    t name ps  -> BFun       (f t) name (mapPattern <$> ps)

    mapClause = \case
        SimplifiedClause t ps g -> SimplifiedClause (f t) (mapPattern <$> ps) g

    mapPattern = cata $ \case
        PVar    t var      -> varPat     (f t) var
        PCon    t con ps   -> conPat     (f t) con ps
        PLit    t prim     -> litPat     (f t) prim
        PAs     t as p     -> asPat      (f t) as p
        POr     t p q      -> orPat      (f t) p q
        PAny    t          -> anyPat     (f t)
        PTuple  t ps       -> tuplePat   (f t) ps
        PList   t ps       -> listPat    (f t) ps
        PRow    t lab p q  -> rowPat     (f t) lab p q
--            PRecord t row        -> recordPat  (f t) row


--foo5 :: (t -> u) -> Stage5.TargetExpr t -> Stage5.TargetExpr u
--foo5 f = cata $ \case
--    EVar    t var          -> varExpr    (f t) var
--    ECon    t con es       -> conExpr    (f t) con es
--    ELit    t prim         -> litExpr    (f t) prim
--    EApp    t es           -> appExpr    (f t) es
--    EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
--    ELam    t ps e         -> lamExpr    (f t) ps e
--    EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
--    EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
--  where
--    mapClause = \case
--        SimplifiedClause t ps g
--                           -> SimplifiedClause (f t) (mapPattern <$> ps) g
--    mapPattern = cata $ \case
--        PVar    t var      -> varPat     (f t) var
--        PCon    t con ps   -> conPat     (f t) con ps
--        PLit    t prim     -> litPat     (f t) prim
--        PAs     t as p     -> asPat      (f t) as p
--        POr     t p q      -> orPat      (f t) p q
--        PAny    t          -> anyPat     (f t)


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
main = do
    --[a] <- getArgs
    --let a = "let f | Some(x) => x | None => 0 in f(Some(5))" -- f(Some(5))" 
    --let a = "let f | Some(x) => x | None => 0 : Int in f(Some(123))" -- f(Some(5))" 
    --let a = "let f | Some(x) => x | None => 0 : Int in Some(123).f" -- f(Some(5))" 
    --let a = "let f(val) | Some(x) => x | None => val : Int in Some(123).f(5)" -- f(Some(5))" 
    --let a = "let f(val) | Some(x) => x | None => val : Int in None.f(5)" -- f(Some(5))" 
    let a = "let f({ name = n | a }) = n in f({ name = \"Bob\", id = 1 : Int })" -- f(Some(5))" 
    --let a = "let b = { wat = \"not\" } in { a = True | b }" -- f(Some(5))" 
    --let a = "let f({ name = n | a }) = a in f({ name = \"Bob\", id = 1 : Int })" -- f(Some(5))" 
    case doParse (pack a) of
        Right e -> test123 e
  where
    doParse a = runParser exprParser "" a
-- print "Main"

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
    , ( "#"      , Forall [kRow] [] (tGen 0 `tArr` tApp kTyp tRecordCon (tGen 0)) )
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
    , ( "Num"
        -- Interface
      , ( ClassInfo (InClass "Num" "a") [] 
            [ ( "(+)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , [ ClassInfo (InClass "Num" tInt) [] 
            [ ( "fromInteger", Ast (varExpr (TypeInfo () (tInteger `tArr` tInt) []) "@Int.fromInteger") )
            ]
          ]
        )
      )
    ]

--        , [ ClassInfo (InClass "Show" tInt) [] 
--              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.Show") )
--              ]

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    , ("#"        , ( ["#"], 1 ))
    ]

--foz1 = case \x -> 1 of
--    f -> f ()
--
