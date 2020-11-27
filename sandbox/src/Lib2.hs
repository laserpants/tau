{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
module Lib2 where

import Debug.Trace
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Type
import Tau.Type.Inference
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

----
----
----
----
----
--
---- ---- 
---- ---- 
---- ---- 
--
--typeEx1 = tapp 
--    (tarr (tapp (tcon star "c1") (tvar star "t1")) (tapp (tcon star "c2") (tvar star "t2"))) 
--    (tarr (tapp (tcon star "c3") (tvar star "t3")) (tapp (tcon star "c4") (tvar star "t4"))) 
--
--flatten :: Type -> [Type]
--flatten = cata alg where
--    alg :: TypeF [Type] -> [Type]
--    alg (TApp t u) = zipWith tapp t u -- t <> u -- t <> u -- concat (transpose [t, u])
--    alg (TArr t u) = zipWith tarr t u -- t <> u -- concat (transpose [t, u])
--    alg (TBound n) = [tbound n]
--    alg (TVar k n) = [tvar k n]
--    alg (TCon k n) = [tcon k n]
--
----
----
----
--
----
----
----
--
----testExpr1 :: Expr () Pattern
--testExpr1 = elet (rvar "f") (elam (rvar "x") (eapp [evar "(+)", evar "x", eapp [evar "f", evar "x"]])) (evar "f")
--
----testExpr2 :: Expr () Pattern
--testExpr2 = elet (rvar "x") (elit (LInt 5)) (evar "x")
----
----testExpr3 :: Expr () Pattern
--testExpr3 = elet (rvar "f") (evar "(==)") (eapp [evar "f", elit (LInt 5), elit (LInt 3)])
----
----testExpr4 :: Expr () Pattern
--testExpr4 = elet (rvar "g") (elam (rvar "x") (eapp [evar "show", eapp [evar "(,)", evar "x", eapp [evar "length", evar "x"]]])) (evar "g")
----
----testExpr5 :: Expr () Pattern
--testExpr5 = elam (rvar "xs") (eapp [evar "length", evar "xs"])
----
----testExpr6 :: Expr () Pattern
--testExpr6 = elam (rvar "x") (elam (rvar "y") (eapp [evar "show", eapp [evar "(,)", evar "x", evar "y"]]))
----
----testEnv :: Env Scheme
--testEnv = Env $ Map.fromList 
--    [ ("(+)", Forall [star] ([TyClass "Num" (tbound 0)] :=> (tbound 0 `tarr` tbound 0 `tarr` tbound 0)))
--    , ("(==)", Forall [star] ([TyClass "Eq" (tbound 0)] :=> (tbound 0 `tarr` tbound 0 `tarr` tBool)))
--    , ("(,)", Forall [star, star] ([] :=> (tbound 0 `tarr` tbound 1 `tarr` (tapp (tapp (tcon (karr star (karr star star)) "(,)") (tbound 0)) (tbound 1)))))
--    , ("show", Forall [star] ([TyClass "Show" (tbound 0)] :=> (tbound 0 `tarr` (tcon star "String"))))
--    , ("length", Forall [star] ([] :=> ((tapp (tcon (karr star star) "List") (tbound 0)) `tarr` tInt)))
--    ]
--
----testClassEnv :: ClassEnv
--testClassEnv = 
--    ( env
--    , [] 
--    )
--  where
--    env :: Env ClassInfo
--    env = Env.fromList 
--        [ ( "Show"
--          , ( []
--            , [ [] 
--                  :=> TyClass "Show" tInt
--
--              , [TyClass "Show" (tvar star "a")] 
--                  :=> TyClass "Show" (tapp (tcon (karr star star) "List") (tvar star "a"))
--
--              , [TyClass "Show" (tvar star "a"), TyClass "Show" (tvar star "b")] 
--                  :=> TyClass "Show" (tapp (tapp (tcon (karr star (karr star star)) "(,)") (tvar star "a")) (tvar star "b"))
--              ]
--            )
--          )
--        ]
--
--test1 = runInfer test
--  where 
--    test = do
--        (expr, as, cs) <- infer testExpr1
--        let cs1 = [Explicit s t | m :>: s <- as, (n, t) <- Env.toList testEnv, m == n]
--        (sub, ps) <- solve (cs <> cs1)
--        pure (apply sub expr, apply sub ps)
--
--test3 = runInfer test
--  where 
--    test = do
--        (expr, as, cs) <- infer testExpr3
--        let cs1 = [Explicit s t | m :>: s <- as, (n, t) <- Env.toList testEnv, m == n]
--        (sub, ps) <- solve (cs <> cs1)
--        pure (apply sub expr, apply sub ps)
--
--test4 = runInfer test
--  where 
--    test = do
--        (expr, as, cs) <- infer testExpr4
--        let cs1 = [Explicit s t | m :>: s <- as, (n, t) <- Env.toList testEnv, m == n]
--        (sub, ps) <- solve (cs <> cs1)
--        pure (apply sub expr, apply sub ps)
--        --pure (apply sub ps)
--
--test5 = runInfer test
--  where 
--    test = do
--        (expr, as, cs) <- infer testExpr5
--        let cs1 = [Explicit s t | m :>: s <- as, (n, t) <- Env.toList testEnv, m == n]
--        (sub, ps) <- solve (cs <> cs1)
--        pure (apply sub expr, apply sub ps)
--
--test6 = runInfer test
--  where 
--    test = do
--        (expr, as, cs) <- infer testExpr6
--        let cs1 = [Explicit s t | m :>: s <- as, (n, t) <- Env.toList testEnv, m == n]
--        (sub, ps) <- solve (cs <> cs1)
--        pure (apply sub expr, apply sub ps)
--
--
--
--
--
--
----
--
----
--
--
------ -- -- instantiate :: (MonadSupply Name m) => Scheme -> m (Qualified Type)
------ -- -- instantiate = undefined
------ -- -- 
------ -- -- infer 
------ -- --   :: (MonadSupply Name m) 
------ -- --   => Expr Pattern 
------ -- --   -> m (Qualified Type, [TypeAssumption], [Constraint])
------ -- -- infer = cata $ \case
------ -- --     EVar var -> do
------ -- --         name <- supply
------ -- --         let t = [] :=> tvar name star
------ -- -- 
------ -- --         traceShowM ("var = " <> var <> " : " <> show t)
------ -- -- 
------ -- --         pure (t, [var :>: t], [])
------ -- -- 
------ -- --     ELit LUnit{} -> pure ([] :=> tUnit, [], [])
------ -- --     ELit LBool{} -> pure ([] :=> tBool, [], [])
------ -- --     ELit LInt{}  -> pure ([] :=> tInt, [], [])
------ -- -- 
------ -- --     ECon name scheme -> do
------ -- --         t <- instantiate scheme
------ -- --         pure (t, [name :>: t], [])
------ -- -- 
------ -- --     EApp exprs ->
------ -- --         foldl1 inferApp exprs
------ -- -- 
------ -- --     ELet pat e1 e2 -> do
------ -- --         ts <- inferPattern pat
------ -- -- 
------ -- --         traceShowM ts
------ -- -- 
------ -- --         (t1, as1, cs1) <- e1 -- infer (as, cs) e1
------ -- --         (ccx :=> t2, as2, cs2) <- e2 -- infer (as <> as1, cs <> cs1) e2
------ -- --         let (cs3, ccs) = unzip 
------ -- -- [((s, t), cc1 <> cc2) | (v :>: (cc1 :=> s)) <- ts, (w :>: (cc2 :=> t)) <- as1 <> as2, v == w]
------ -- -- 
------ -- --         traceShowM ("let = " <> show t2)
------ -- -- 
------ -- --         pure ( (ccx <> concat ccs) :=> t2
------ -- --              , removeAssumptionSet ts as1 <> removeAssumptionSet ts as2 
------ -- --              , cs1 <> cs2 <> cs3 <> [] -- <> [(s, t) | (v :>: s) <- ts, (w :>: t) <- as1 <> as2, v == w]
------ -- --              )
------ -- -- 
------ -- --     ELam pat expr -> do
------ -- --         ts <- inferPattern pat
------ -- --         (ccx :=> t1, as1, cs1) <- expr
------ -- --         name <- supply
------ -- --         let t = tvar name star
------ -- --         let (cs3, ccs) = unzip [((s, t), cc1 <> cc2) | (v :>: (cc1 :=> s)) <- ts, (w :>: (cc2 :=> t)) <- as1, v == w]
------ -- -- 
------ -- --         traceShowM ("lam = " <> show (t `tarr` t1))
------ -- -- 
------ -- --         pure ( (ccx <> concat ccs) :=> (t `tarr` t1) 
------ -- --              , removeAssumptionSet ts as1 
------ -- --              , cs1 -- <> [(s, t) | (v :>: s) <- ts, (w :>: t) <- as1, v == w] )
------ -- --              )
------ -- -- 
------ -- -- inferPattern :: (MonadSupply Name m) => Pattern -> m [TypeAssumption]
------ -- -- inferPattern = cata $ \case
------ -- --     PVar var -> do
------ -- --         name <- supply
------ -- --         pure [var :>: ([] :=> tvar name star)]
------ -- --         --beta <- varT <$> supply
------ -- --         --tellAssumption (var, beta)
------ -- --         --pure beta
------ -- -- 
------ -- -- inferApp :: (MonadSupply Name m) => m (Qualified Type, [TypeAssumption], [Constraint]) -> m (Qualified Type, [TypeAssumption], [Constraint]) -> m (Qualified Type, [TypeAssumption], [Constraint])
------ -- -- inferApp e1 e2 = do
------ -- --     name <- supply
------ -- --     let t = tvar name star
------ -- --     traceShowM ("app = " <> show t)
------ -- -- 
------ -- --     (cc1 :=> t1, as1, cs1) <- e1 -- infer (as, cs) e1
------ -- --     (cc2 :=> t2, as2, cs2) <- e2 -- infer (as <> as1, cs <> cs1) e2
------ -- -- 
------ -- --     pure ( (cc1 <> cc2) :=> t
------ -- --          , as1 <> as2 
------ -- --          , cs1 <> cs2 <> [(t1, t2 `tarr` t)]
------ -- --          )
------ -- --     --let t = undefined -- tvar name star
------ -- --     --(cc1 :=> t1, as1, cs1) <- fun
------ -- --     --(cc2 :=> t2, as2, cs2) <- arg
------ -- --     --pure ( cc1 <> cc2 :=> t
------ -- --     --     , as1 <> as2
------ -- --     --     , cs1 <> cs2 <> [(t1, t2 `tarr` t)] 
------ -- --     --     )
