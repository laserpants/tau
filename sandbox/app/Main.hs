{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib3
import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Foldable
import Data.Function ((&))
import Data.List
import Data.Maybe (fromJust)
import Data.Maybe (fromMaybe)
import Data.Partition
import Data.Set (Set)
import Data.Tuple.Extra (thd3)
import Tau.Env
import Tau.Eval
import Tau.Expr
import Tau.Expr.Patterns
import Tau.Type
--import Tau.Type.Class (reduce)
import Tau.Type.Inference
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Util
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env
import qualified Tau.Type.Class as Class
import qualified Data.Map.Strict as Map
import qualified Data.Set as PlainSet

--data Fun = Fun
--
--class Baz a where
--    toX :: a -> Fun
--
--instance Baz (a -> b) where
--    toX = undefined

expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")
expr2 = letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
expr3 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow", varExpr () "x"])
expr4 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
expr5 = letExpr () (varPat () "f") (varExpr () "lenShow") (lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"]))
expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 5)]
expr7 = lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"])
expr8 = lamExpr () (varPat () "x") (lamExpr () (varPat () "y") (appExpr () [varExpr () "f", lamExpr () (varPat () "x") (lamExpr () (varPat () "y") (varExpr () "z"))]))
expr9 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow2", varExpr () "x"])

-- lenShow { show = \x => "five" } 5
expr10 = appExpr () 
    [ varExpr () "lenShow"
    , recExpr () [Field () "show" showInt]
    , litExpr () (LInt 5) ]
  where
    showInt = lamExpr () (varPat () "x") (litExpr () (LString "five"))

lenShow :: Value Eval
lenShow = fromJust $ runEval (eval foo3) mempty -- Closure "d" foo1 mempty
  where
    -- \d => match d with | { show = show } => \x => show x
    foo2 = lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "show" "show"]] [] (lamExpr () (varPat () "x") (appExpr () [varExpr () "show", varExpr () "x"]))])
    Right foo3 = simplified foo2

    -- foo1 = lamExpr () "d" (matExpr () [varExpr () "d"] [Clause [RCon () "{show}" ["show"]] [] (lamExpr () "x" (appExpr () [varExpr () "show", varExpr () "x"]))])
--        lamExpr () "x" (appExpr () [undefined, varExpr () "x"])

--bb10 = fromJust $ evalExpr expr $ Env.fromList 
bb10 = evalExpr expr $ Env.fromList [ ("lenShow", lenShow) ]
  where
    Right expr = simplified expr10

expr11 = letExpr () (recPat () [Field () "name" "x"]) (recExpr () [Field () "name" (litExpr () (LInt 5))]) (varExpr () "x")

bb11 = 
    traceShow expr1 $ fromJust $ runEval (eval expr1) mempty
  where
    Right expr1 = simplified expr11

expr12 = letExpr () (recPat () [Field () "name" "x", Field () "id" "id", Field () "size" "s"])
                    (recExpr () [ Field () "name" (litExpr () (LString "Bob"))
                                , Field () "id" (litExpr () (LInt 5))
                                , Field () "size" (litExpr () (LInt 11)) ])
                    (varExpr () "s")

bb12 = 
    traceShow expr1 $ fromJust $ runEval (eval expr1) mempty
  where
    Right expr1 = simplified expr12

--bb11 = 
--    traceShow expr1 $ fromJust $ runEval (eval expr1) mempty
--  where
--    Right expr1 = simplified expr11


expr13 = letExpr () (conPat () "Just" [varPat () "x"]) (conExpr () "Just" [litExpr () (LInt 5)]) (varExpr () "x")

expr14 = conExpr () "Just" [litExpr () (LInt 5)]

expr15 = conExpr () "(,)" [litExpr () (LInt 5), litExpr () LUnit]

expr16 = letExpr () (conPat () "Just" [varPat () "x"]) (varExpr () "y") (varExpr () "x")

expr17 = recExpr () [Field () "name" (litExpr () (LString "Bob")), Field () "id" (litExpr () (LInt 5))]


expr18 = letExpr () (recPat () [Field () "name" "n", Field () "age" "a"])  
                    (recExpr () [Field () "age" (litExpr () (LInt 40)), Field () "name" (litExpr () (LString "Barnaby"))]) (varExpr () "n")


bb18 = 
    traceShow expr1 $ fromJust $ runEval (eval expr1) mempty
  where
    Right expr1 = simplified expr18


expr19 = appExpr () [varExpr () "@showInt", litExpr () (LInt 8)]

bb19 = evalExpr expr $ Env.fromList [] 
  where
    Right expr = simplified expr19


expr20 = appExpr () [varExpr () "@(+)Int", litExpr () (LInt 8), litExpr () (LInt 5)]

bb20 = evalExpr expr $ Env.fromList [] 
  where
    Right expr = simplified expr20


expr21 = lamExpr () (varPat () "xs") (appExpr () [varExpr () "map", lamExpr () (varPat () "x") (appExpr () [varExpr () "@(+)Int", varExpr () "x", litExpr () (LInt 1)]), varExpr () "xs"])

expr22 = (appExpr () [varExpr () "f", varExpr () "x"])


----


addConstrs :: [(Name, Type)] -> Type -> (Type, [(Name, Type)])
addConstrs css ty = (ty, [(n, t) | s <- vars, (n, t) <- css, s == t])
  where
    vars :: [Type]
    vars = flip cata ty $ \case
        TVar k var -> [tVar k var]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        _          -> []

applyFinal :: [(Name, Type)] -> (Type, [(Name, Type)]) -> (Type, [(Name, Type)])
applyFinal kvs (t, css) = 
    (apply sub t, second (apply sub) <$> css)
  where
    sub = Tau.Type.Substitution.fromList kvs

type T = (Type, [(Name, Type)])



dicts :: Expr T (Pattern T) (Pattern T) -> [(Name, Type)]
dicts = cata $ \case
    ELam (_, cs) _ e1 -> cs <> e1
    _                 -> []


rebuildTree :: Expr T (Pattern T) (Pattern T) -> StateT Bool Infer (Expr T (Pattern T) (Pattern T))
rebuildTree = cata $ \case
    EApp t exs -> do
        put False
        sequence exs >>= \case
            [] -> pure (appExpr t [])
            e:es -> do
                let ds = []
                pure (appExpr t (e:ds <> es))

      where
        toDict :: Expr T (Pattern T) (Pattern T) -> Expr T (Pattern T) (Pattern T)
        toDict = undefined

    ELam t p e1 -> do
        nested <- get
        if nested
            then lamExpr t p <$> e1
            else do
                put True
                next <- lamExpr t p <$> e1 
                let ds = sortOn fst (dicts next)
                traceShowM "//////////////////"
                traceShowM ds
                --et (_, css) = getTag e1 :: T
                pure undefined
                --pure (lamExpr (second (const []) t) undefined next)

                --next <- lamExpr t p <$> e1 
                --let ds = sortOn fst (dicts next)
                ----let xxx = dicts next
                ----traceShowM xxx
                --pure (foldr fffoo next ds)

    e -> do
        put False
        embed <$> sequence e

--rebuildTree :: Expr T (Pattern T) (Pattern T) -> StateT Bool Infer (Expr T (Pattern T) (Pattern T))
--rebuildTree = cata $ \case
--    EApp t exs  -> do
--        put False
--        sequence exs >>= \case
--            [] -> pure (appExpr t [])
--            e:es -> do
--                let (_, css) = getTag e :: T
--                pure (appExpr t (e:(gggoo <$> css) <> es))
--
--                --let (ttt, css) = getTag e :: T
--                --    next = appExpr t eee
--                --    ts :: [Type]
--                --    ts = fmap (uncurry dictType) css
--                --    ds = fmap gggoo css
--                --    ttt2 = foldr tArr ttt ts
--                --pure (appExpr t (setTag ((ttt2, []) :: T) e:ds <> es))
--
--    ELam t p e1 -> do
--        nested <- get
--        if nested
--            then lamExpr t p <$> e1
--            else do
--                put True
--                next <- lamExpr t p <$> e1 
--                let ds = sortOn fst (dicts next)
--                --let xxx = dicts next
--                --traceShowM xxx
--                pure (foldr fffoo next ds)
--
--    e -> do
--        put False
--        embed <$> sequence e
--
--dictType :: Name -> Type -> Type
--dictType name = tApp (tCon (kArr kStar kStar) name) 
--
--gggoo :: (Name, Type) -> Expr T (Pattern T) (Pattern T)
--gggoo (n, t) = varExpr (tApp (tCon (kArr kStar kStar) n) t, []) "DICT"
--
----gggoo (n, t) = recExpr (tApp (tCon (kArr kStar kStar) n) t, []) [Field "show" tmp]
----tmp = lamExpr undefined (anyPat undefined) undefined
--
--fffoo :: (Name, Type) -> Expr T (Pattern T) (Pattern T) -> Expr T (Pattern T) (Pattern T)
--fffoo (n, t) y = let t1 = dictType n t in lamExpr (t1 `tArr` tx, []) (varPat (t1, []) "DICT") y
----fffoo (n, t) y = let t1 = dictType n t in lamExpr (t1 `tArr` tx, []) (undefined) y -- (varPat (t1, []) "DICT") y
--  where
--    xx :: T
--    xx@(tx, _) = getTag y
--
----    EVar t var     -> varExpr t var
----    ECon t con exs -> conExpr t con exs
----    ELit t lit     -> litExpr t lit
----    ELet t p e1 e2 -> letExpr t p e1 e2
----    EIf  t c e1 e2 -> ifExpr  t c e1 e2
----    EMat t exs eqs -> matExpr t exs eqs
----    EOp  t op      -> opExpr  t op

aa = c
  where
    c = runInfer b
    b = do
        --((te, as), cs) <- infer_ expr11
        ((te, as), cs) <- infer_ expr21
        traceShowM "99999999999999999999999999999999999999999"
        traceShowM te
        traceShowM "2xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM cs
        traceShowM "3xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM as
        traceShowM "4xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM "4xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM "4xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM "4xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        traceShowM "4xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
        --let xx = [(t, s) | (u, s) <- Env.toList env1, (v :>: t) <- as, u == v]
        let cs' = cs <> [Explicit t s | u :>: (t, _) <- as, (v, s) <- Env.toList env1, u == v]
        (sub, (xx1, xx2)) <- runStateT (solve cs') ([], [])
        traceShowM "-----------------------------------------"
        traceShowM "-----------------------------------------"
        traceShowM (sub, (xx1, xx2))
        traceShowM "-----------------------------------------"
        traceShowM "-----------------------------------------"
        let te1 = mapTags (toFunction sub) te
--        traceShowM xx1
--        traceShowM xx2
        let te2 = mapTags (addConstrs xx2) te1
        let te3 = mapTags (applyFinal xx1) te2
        --(zzz, _) <- runStateT (rebuildTree te3) False
        --traceShowM "*********5"
        --traceShowM zzz -- (mapTags (const ()) zzz)
        --traceShowM "----------"
        pure (te3, cs', sub) -- (te, sub)

    env1 =
        Env.fromList [
            -- ("lenShow", sForall kStar [("show", tGen 0 `tArr` tString)] (sScheme (tGen 0 `tArr` tInt)))
            ( "lenShow", sForall kStar ["Show"] (sScheme (tGen 0 `tArr` tInt)) )
          , ( "lenShow2", sForall kStar ["Show", "Eq"] (sScheme (tGen 0 `tArr` tInt)) )
          , ( "Just", sForall kStar [] (sScheme (tGen 0 `tArr` (tApp (tCon (kArr kStar kStar) "Maybe") (tGen 0)))) )
          , ( "(,)", sForall kStar [] (sForall kStar [] (sScheme (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 0)) (tGen 1))))) )
          , ( "map", sForall (kArr kStar kStar) ["Functor"] (sForall kStar [] (sForall kStar [] (sScheme ((tGen 1 `tArr` tGen 0) `tArr` (tApp (tGen 2) (tGen 1)) `tArr` (tApp (tGen 2) (tGen 0)))))) )
          , ( "@(+)Int", sScheme (tInt `tArr` tInt `tArr` tInt) )
        ]
 
--scheme1 = sForall (kArr kStar kStar) [("Functor", tGen 0)] (sForall kStar [] (sForall kStar [] (sScheme ((tGen 1 `tArr` tGen 0) `tArr` (tApp (tGen 2) (tGen 1)) `tArr` (tApp (tGen 2) (tGen 0))))))
scheme1 = sForall (kArr kStar kStar) ["Functor"] (sForall kStar [] (sForall kStar [] (sScheme ((tGen 1 `tArr` tGen 0) `tArr` (tApp (tGen 2) (tGen 1)) `tArr` (tApp (tGen 2) (tGen 0))))))


    --inject
    --  :: [(Type, Scheme)] 
    --  -> Expr Node p q 
    --  -> Expr Node p q
    --inject ss = cata $ \case
    --    EVar (Node t cs set) var ->
    --        varExpr (Node t (cs <> concatMap fn ss) set) var
    --      where
    --        fn (t1, s) 
    --            | t1 == tVar kStar t = [Explicit s]
    --            | otherwise          = []
    --    e -> 
    --        embed e








--     env1 =
--         Env.fromList [
--             ("lenShow", sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
--         ]
--        embed <$> sequence e






-- ----------------------------------
-- ----------------------------------
-- ----------------------------------
-- ----------------------------------
-- ----------------------------------
-- 
-- --instance Free Constraint where
-- --    free (Equality t1 t2)      = free t1 `Set.union` free t2
-- --    free (Implicit t1 t2 mono) = free t1 `Set.union` free t2
-- --    free (Explicit ty scheme)  = free ty `Set.union` free scheme
-- 
-- 
-- --join_ :: Constraint -> Partition Name -> Partition Name
-- --join_ (Equality (Fix (TVar _ a)) (Fix (TVar _ b)))   p = joinElems a b p
-- --join_ (Implicit (Fix (TVar _ a)) (Fix (TVar _ b)) _) p = joinElems a b p
-- --join_ _ p = p
-- 
-- 
-- constraintPartition :: Constraint -> Partition Type -> Partition Type
-- constraintPartition (Equality t1 t2)   p = joinElems t1 t2 p
-- constraintPartition (Implicit t1 t2 _) p = joinElems t1 t2 p
-- constraintPartition _                  p = p
-- 
-- 
-- --testScheme1 = 
-- --    sForall kStar [Predicate "o1" tInt] 
-- --        (sForall kStar [Predicate "o2" tBool] 
-- --            (sScheme (tGen 1 `tArr` tGen 0 `tArr` tUnit)))
-- 
-- 
-- instantiate_ :: Scheme -> Infer (Type, [(Name, Type)])
-- instantiate_ scheme = do
--     ns <- supplies (length kinds)
--     let ts = reverse (zipWith tVar kinds ns)
--     pure (substBound ts ty, fmap (substBound ts) <$> preds1)
-- 
--   where
--     (kinds, preds) = unzip $ flip cata scheme $ \case
--         Mono _         -> []
--         Forall k ps rs -> (k, toPair <$> ps):rs
-- 
--     preds1 = fmap fn (zip (reverse $ concat preds) [0..]) where
--         fn ((n, t), i) = (n, tGen i `tArr` t)
-- 
--     ty = flip cata scheme $ \case
--         Mono t       -> t
--         Forall _ _ t -> t
-- 
--     toPair (Predicate n t) = (n, t)
-- 
--     substBound :: [Type] -> Type -> Type 
--     substBound ts = cata $ \case
--         TGen n     -> ts !! n
--         TArr t1 t2 -> tArr t1 t2
--         TApp t1 t2 -> tApp t1 t2
--         TVar k var -> tVar k var
--         TCon k con -> tCon k con
-- 
-- 
-- bazz :: Assumption Name -> (Name, Type)
-- bazz (name :>: v) = (name, tVar kStar v)
-- 
-- hello2 expr =
--     runInfer go
--   where
--     envConstraints as = do
--         (x, s) <- bazz <$> as
--         (y, t) <- Env.toList env1
--         guard (x == y)
--         pure (Explicit s t)
-- 
--     go = do
--         ((te, as), cs) <- infer__ expr
--         let cs' = cs <> envConstraints as
--         (sub, x) <- solve cs' 
--         pure (apply sub (modifyTags (tVar kStar) te), x, sub)
-- 
--     env1 =
--         Env.fromList [
--             ("lenShow", sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
--         ]
-- 
--     runInfer_ = 
--         runExceptT
--           >>> flip runReaderT (Monoset mempty) 
--           >>> flip evalSupply (numSupply "a")
--           >>> fromMaybe (throwError ImplementationError)
-- 
-- 
-- --yello = do
-- --    zs <- hello
-- --    undefined
-- 
-- --hello :: Either InferError [(Type, [(Name, Type)], Constraint)]
-- hello expr = 
--     runInfer go
--   where
--     envConstraints as = do
--         (x, s) <- bazz <$> as
--         (y, t) <- Env.toList env1
--         guard (x == y)
--         pure (Explicit s t)
-- 
--     --zoo = do
--     --    zs <- go
--     --    undefined
-- 
--     go = do
--         ((te, as), cs) <- infer__ expr
-- 
--         let cs' = cs <> envConstraints as
-- 
--         traceShowM cs
-- 
--         let partition :: Partition Type
--             partition = foldr constraintPartition discrete cs'
-- 
--         traceShowM partition
--         yyy2 <- traverse (xyz partition) cs'
-- 
--         let zs = Map.fromList (concat yyy2)
--         let rrr = (snd . snd) <$> (concat yyy2)
-- 
--         (sub, gooo) <- solve (cs' <> rrr)
-- 
-- --        traceShowM gooo
-- 
--         let -- foo :: (Name, Type) -> 
--             foo (a, t) = (a, apply sub t)
-- 
--         let g t = 
--               case Map.lookup (tVar kStar t) zs of
--                   Nothing      -> (apply sub (tVar kStar t), [])
--                   Just (xs, _) -> (apply sub (tVar kStar t), foo <$> xs)
-- 
--         --let rs = snd <$> zs
-- 
-- 
--         -- let te' = modifyTags g te
-- 
--         pure (modifyTags g te) -- , cs')
-- 
--     xyz p (Explicit t scheme) = do
-- 
--         let fn :: Type -> Infer (Type, ([(Name, Type)], Constraint))
--             fn s = do
--                 (t, ps) <- instantiate_ scheme
--                 pure (s, (ps, Equality s t))
-- 
--         let a = Data.Partition.find p t
--         traverse fn (PlainSet.toList a)
-- 
-- --        let zz :: PlainSet.Set Type
-- --            zz = p `Data.Partition.find` t 
-- --            yy = PlainSet.toList zz
-- --            xx = traverse fn yy
-- --
-- --            fn :: Type -> Infer ([(Name, Type)], Constraint)
-- --            fn s = do
-- --                (t, ps) <- instantiate_ scheme
-- --                pure (ps, Equality s t)
-- --
-- --         in xx
-- 
--     xyz _ _ = 
--         pure []
-- 
-- 
--     env1 =
--         Env.fromList [
--             ("lenShow", sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
--         ]
-- 
--     runInfer_ = 
--         runExceptT
--           >>> flip runReaderT (Monoset mempty) 
--           >>> flip evalSupply (numSupply "a")
--           >>> fromMaybe (throwError ImplementationError)
-- 
-- 
-- 
-- expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")
-- 
-- 
-- expr2 = 
--     letExpr () 
--         (varPat () "f") 
--         (varExpr () "lenShow") 
--         (appExpr () [varExpr () "f", litExpr () (LInt 5)])
-- 
-- 
-- expr3 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow", varExpr () "x"])
-- 
-- 
-- expr4 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
-- 
-- 
-- expr5 = letExpr () (varPat () "f") (varExpr () "lenShow") (lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"]))
-- 
-- 
-- expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 5)]
-- 
-- 
-- 
-- -- baz6 =
-- --     --reduce env [TypeClass "Show" (tApp (tCon (kArr kStar kStar) "List") (tCon kStar "Int"))]
-- --     --Class.byInstance env (TypeClass "Show" (tApp (tCon (kArr kStar kStar) "List") (tCon kStar "Int")))
-- --     Class.toHeadNormalForm env [TypeClass "Show" (tCon kStar "Int")]
-- --     --instances env "Show"
-- --   where
-- --     --env2 = (Env.fromList [], [])
-- -- 
-- --     env = (Env.fromList
-- --       [ ("Show", ( [], [ [] :=> TypeClass "Show" tInt 
-- --                        , [TypeClass "Show" (tVar kStar "a")] :=> TypeClass "Show" (tList (tVar kStar "a"))
-- --                        ] ))
-- --       ]
-- --       , [])
-- -- 
-- 
-- --testExpr5 =
-- --    appExpr () [varExpr () "show", varExpr () "xs"]
-- --
-- --baz5 = runInfer $ do
-- --    xx@(te, as, cs) <- infer testExpr5
-- --    let cs' = cs <> [ Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))
-- --                    , Explicit (tVar kStar "a3") (Forall [] ([] :=> tList tInt)) ]
-- --    (sub, tcs) <- solve cs'
-- --    --pure (xx, apply sub te, tcs)
-- --    --pure (apply sub te, tcs)
-- ----    pure (apply sub te)
-- --    pure tcs
-- --    --pure as
-- 
-- 
-- 
-- 
-- --testExpr4 =
-- --    letExpr () 
-- --        (varPat () "f")
-- --        (varExpr () "show")
-- --        (varExpr () "f")
-- --
-- --baz4 = runInfer $ do
-- --    xx@(te, as, cs) <- infer testExpr4
-- --    let cs' = cs <> [] -- [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- ----    let cs' = cs 
-- --    (sub, tcs) <- solve cs'
-- --    --pure (xx, apply sub te, tcs)
-- --    --pure (apply sub te, tcs)
-- --    pure (apply sub te, as, cs) -- (apply sub te, tcs)
-- 
-- 
-- 
-- -- 
-- -- testExpr3 =
-- --     lamExpr () (varPat () "x") (appExpr () [varExpr () "show", conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []]])
-- -- 
-- -- 
-- -- baz3 = runInfer $ do
-- --     xx@(te, as, cs) <- infer testExpr3
-- -- --    let cs' = cs <> [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- --     let cs' = cs <> [Explicit (tVar kStar "a3") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- --     (sub, tcs) <- solve cs'
-- --     --pure (xx, apply sub te, tcs)
-- --     --pure (apply sub te, tcs)
-- --     --pure (apply sub te, apply sub tcs) 
-- --     pure (apply sub te, apply sub tcs) 
-- -- 
-- -- 
-- -- -- (+) : Num a => a -> a -> a
-- -- 
-- -- -- let f = \x -> x x (f x) in f
-- -- 
-- -- testExpr2 =
-- --     letExpr () 
-- --         (varPat () "f")
-- --         (lamExpr () (varPat () "x") (appExpr () [varExpr () "(+)", varExpr () "x", appExpr () [varExpr () "f", varExpr () "x"]]))
-- --         (varExpr () "f")
-- -- 
-- -- baz2 = runInfer $ do
-- --     xx@(te, as, cs) <- infer testExpr2
-- -- --    let cs' = cs <> [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- --     let cs' = cs <> [Explicit (tVar kStar "a5") (Forall [kStar] ([TypeClass "Num" (tGen 0)] :=> (tGen 0 `tArr` (tGen 0 `tArr` tGen 0))))]
-- --     (sub, tcs) <- solve cs'
-- --     --pure (xx, apply sub te, tcs)
-- --     --pure (apply sub te, tcs)
-- --     pure te -- (apply sub te)
-- -- 
-- -- 
-- -- 
-- -- testExpr1 =
-- --     letExpr () 
-- --         (varPat () "f")
-- --         (varExpr () "show")
-- --         (appExpr () [varExpr () "f", litExpr () (LInt 5)])
-- -- 
-- -- 
-- -- baz = runInfer $ do
-- --     xx@(te, as, cs) <- infer testExpr1
-- --     let cs' = cs <> [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- --     (sub, tcs) <- solve cs'
-- --     --pure (xx, apply sub te, tcs)
-- --     --pure (apply sub te, tcs)
-- --     pure (apply sub te)
-- -- 
-- -- 
-- -- --testAgain2 =
-- -- --    infer testAgain
-- -- --
-- -- --testAgain3 =
-- -- --    runInfer testAgain2
-- -- --
-- -- --testAgain4 = apply sub e
-- -- --  where
-- -- --    cs' = cs <> [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
-- -- --    Right (e, as, cs) = testAgain3
-- -- ----testAgain5 = s
-- -- ----  where
-- -- --    Right (sub, tcs) = runInfer (solve cs')
-- -- 
-- -- 
-- -- --
-- -- --
-- -- 
-- -- testEnv :: ConstructorEnv
-- -- testEnv = constructorEnv 
-- --     [ ("Cons" , ["Cons", "Nil"]) 
-- --     , ("Nil"  , ["Cons", "Nil"]) 
-- --     ]
-- 
-- abcdef1 =
--     letExpr () 
--         (conPat () "Just" [varPat () "x"]) 
--         (conExpr () "Just" [litExpr () (LInt 5)])
--         (varExpr () "x")
-- 
-- --abcdef2 = infer abcdef1
-- --
-- --abcdef3 = r
-- --  where
-- --    Right (r, _, _) = runInfer abcdef2
-- --
-- --abcdef4 = simplify abcdef3
-- 
-- abcdef5 = r
--   where
--     Right r = simplified abcdef1
-- 
-- abcdef6 = fromJust $ evalExpr abcdef5 $ Env.fromList 
--     [ ("Just", constructor "Just" 1)
--     ]
-- 
-- 
-- --
-- 
-- abcdef21 =
--     matExpr () [varExpr () "x"] 
--         [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1)) 
--         , Clause [anyPat ()]          [] (litExpr () (LInt 2)) 
--         ]
-- 
-- --abcdef22 = infer abcdef21
-- --
-- --abcdef23 = r
-- --  where
-- --    Right (r, _, _) = runInfer abcdef22
-- 
-- abcdef24 = simplify abcdef21
-- 
-- abcdef25 = r
--   where
--     Right r = simplified abcdef21
-- 
-- 
-- 
-- -- first : forall a. (first : a -> Int) => a -> Int
-- -- isZero : Int -> Bool
-- --
-- -- \t -> isZero (first t)
-- --   : forall a. (first : a -> Int) => a -> Bool
-- --
-- --
-- --
-- -- first : forall a. (first : a -> b) => a -> b
-- --
-- -- \t -> isZero (first t)
-- --   : forall a. (first : a -> b) => a -> Bool
-- testExpr3 =
--     lamExpr () 
--         (varPat () "t")
--         (appExpr () 
--             [ varExpr () "isZero"
--             , appExpr () [ varExpr () "first", varExpr () "t" ] 
--             ])
-- 
-- tIsZero = sScheme (tInt `tArr` tBool)
-- tFirst = sForall kStar [Predicate "first" tInt] (sScheme (tGen 0 `tArr` tInt))
-- 
-- tFirst1 = sForall kStar [] (sForall kStar [Predicate "first" (tGen 1)] (sScheme (tGen 0 `tArr` tGen 1)))
-- 
-- baz = runInfer fun where
--     fun = do
--         (te, as, cs) <- infer testExpr3
--         let cs' = cs <> 
--                   -- isZero
--                   [ Explicit (tVar kStar "a3") tIsZero
--                   -- first
--                   , Explicit (tVar kStar "a5") tFirst
--                   ]
--         (sub, xx) <- solve cs'
--         traceShowM xx
--         pure (apply sub te)
-- 
-- baz2 = runInfer fun where
--     fun = do
--         (te, as, cs) <- infer testExpr3
--         let cs' = cs <> 
--                   -- isZero
--                   [ Explicit (tVar kStar "a3") tIsZero
--                   -- first
--                   , Explicit (tVar kStar "a5") tFirst1
--                   ]
--         (sub, xx) <- solve cs'
--         traceShowM xx
--         pure (apply sub te)
-- 
-- 
--     --let cs' = cs <> [Explicit (tVar kStar "a2") (Forall [kStar] ([TypeClass "Show" (tGen 0)] :=> (tGen 0 `tArr` tCon kStar "String")))]
--     --(sub, tcs) <- solve cs'
--     --pure (xx, apply sub te, tcs)
--     --pure (apply sub te, tcs)
--     -- pure (apply sub te)
-- 
-- testExpr5 =
--     appExpr () 
--         [ varExpr () "first"
--         , litExpr () (LInt 5)
--         ]
-- 
-- 
-- baz5 = runInfer fun where
--     fun = do
--         (te, as, cs) <- infer testExpr5
--         let cs' = cs <> [ Explicit (tVar kStar "a2") tFirst ]
--         (sub, xx) <- solve cs'
--         traceShowM cs
--         --pure (apply sub te)
--         pure (apply sub te, sub)
-- 
-- 
-- 
-- 
-- 
-- -- 
-- -- --ccc1 :: [[Pattern t]]
-- -- ccc1 =
-- --     [ [ conPat () "Cons" [ litPat () (LInt 5), conPat () "Nil" []                                 ] ]
-- --     , [ conPat () "Cons" [ litPat () (LInt 4), conPat () "Cons" [ varPat () "y", varPat () "ys" ] ] ]
-- --     , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
-- --     , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
-- --     , [ conPat () "Nil"  []                                                                         ]                                                  
-- --     , [ varPat () "xs"                                                                              ]
-- --     ]
-- -- 
-- -- ddd1 :: Bool
-- -- ddd1 = runReader (exhaustive ccc1) testEnv 
-- -- 
-- -- 
-- -- --ccc2 :: [[Pattern]]
-- -- ccc2 =
-- --     [ [ conPat () "Cons" [ litPat () (LInt 5), conPat () "Nil" []                                 ] ]
-- --     , [ conPat () "Cons" [ litPat () (LInt 4), conPat () "Cons" [ varPat () "y", varPat () "ys" ] ] ]
-- --     , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
-- --     , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
-- --     , [ conPat () "Nil"  []                                                                         ]
-- --     ]
-- -- 
-- -- ddd2 :: Bool
-- -- ddd2 = runReader (exhaustive ccc2) testEnv 
-- -- 
-- -- 
-- -- --ccc3 :: [[Pattern]]
-- -- ccc3 =
-- --     [ [ conPat () "Nil" [], conPat () "Nil" [] ] 
-- --     ]
-- -- 
-- -- ddd3 :: Bool
-- -- ddd3 = runReader (exhaustive ccc3) testEnv 
-- -- 
-- -- 
-- -- --ccc4 :: [[Pattern]]
-- -- ccc4 =
-- --     [ [ conPat () "Nil" [], conPat () "Nil" [] ] 
-- --     , [ conPat () "Nil" [], conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
-- --     ]
-- -- 
-- -- ddd4 :: Bool
-- -- ddd4 = runReader (exhaustive ccc4) testEnv 
-- -- 
-- -- --ccc5 :: [[Pattern]]
-- -- ccc5 =
-- --     [ [ conPat () "Nil" []                                 , conPat () "Nil" [] ] 
-- --     , [ conPat () "Nil" []                                 , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
-- --     , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Nil" [] ] 
-- --     ]
-- -- 
-- -- ddd5 :: Bool
-- -- ddd5 = runReader (exhaustive ccc5) testEnv 
-- -- 
-- -- 
-- -- --ccc6 :: [[Pattern]]
-- -- ccc6 =
-- --     [ [ conPat () "Nil" []                                 , conPat () "Nil" [] ] 
-- --     , [ conPat () "Nil" []                                 , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
-- --     , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Nil" [] ] 
-- --     , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
-- --     ]
-- -- 
-- -- ddd6 :: Bool
-- -- ddd6 = runReader (exhaustive ccc6) testEnv 
-- -- 
-- -- 
-- -- --ccc7 :: [[Pattern]]
-- -- ccc7 =
-- --     [ [ litPat () (LBool True) ] 
-- --     , [ litPat () (LBool False) ]
-- --     ]
-- -- 
-- -- ddd7 :: Bool
-- -- ddd7 = runReader (exhaustive ccc7) testEnv 
-- -- 
-- -- 
-- -- --ccc8 :: [[Pattern]]
-- -- ccc8 =
-- --     [ [ litPat () (LBool True) ] 
-- --     ]
-- -- 
-- -- ddd8 :: Bool
-- -- ddd8 = runReader (exhaustive ccc8) testEnv 
-- -- 
-- -- 
-- -- 
-- -- 
-- -- 
-- -- --data ThingF a = Case a
-- -- --
-- -- --type Thing = Fix ThingF
-- -- --
-- -- --
-- -- --yy1 = unfoldr fun 1
-- -- --  where
-- -- --    fun x = if x == 5 then Nothing else Just (x, x+1)
-- -- 
-- -- --data Thing = Case Thing | Base deriving (Show, Eq)
-- -- --
-- -- --yy1 = unfoldr fun 0
-- -- --  where
-- -- --    fun x = 
-- -- --        if x == 5 then Nothing
-- -- --                  else Just (Base, x + 1)
-- -- 
-- -- --data ThingF a = Case a | Base deriving (Show, Eq, Functor)
-- -- --
-- -- --deriveShow1 ''ThingF
-- -- --deriveEq1   ''ThingF
-- -- --
-- -- --type Thing = Fix ThingF
-- -- --
-- -- ----yyy :: Int -> Thing
-- -- ----yyy = ana coalg 
-- -- ----  where
-- -- ----    coalg 0 = Base
-- -- ----    coalg n = Case (n - 1)
-- -- --
-- -- --
-- -- --
-- -- --xx1 :: Maybe [(Name, Value Eval)]
-- -- --xx1 = 
-- -- --    tryClause 
-- -- --        [ PVar () "x", PVar () "y" ] 
-- -- --        [ Value (LInt 5), Value (LInt 3) ]
-- -- --
-- -- --xx2 :: Maybe [(Name, Value Eval)]
-- -- --xx2 = 
-- -- --    tryClause 
-- -- --        [ PCon () "Just" [ "x" ] ] 
-- -- --        [ Data "Just" [ Value (LInt 2) ] ]
-- -- --
-- -- --xx3 :: Maybe [(Name, Value Eval)]
-- -- --xx3 = 
-- -- --    tryClause 
-- -- --        [ PCon () "Just" [ "x" ] ] 
-- -- --        [ Data "Must" [ Value (LInt 2) ] ]
-- -- --
-- -- --newtype X a = X { unX :: SupplyT Name Maybe a } deriving
-- -- --    ( Functor
-- -- --    , Applicative
-- -- --    , Monad
-- -- --    , MonadSupply Name )
-- -- --
-- -- --instance MonadFail X where
-- -- --    fail _ = X (lift Nothing)
-- -- --
-- -- --xx5 :: X (Expr () (SimpleRep ()) Name)
-- -- --xx5 = simplify (matExpr () 
-- -- --    [varExpr () "xs"] 
-- -- --    [Clause [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PCon () "Cons" [Fix (PVar () "y"), Fix (PVar () "ys")])])] [] (varExpr () "e1")]
-- -- --    )
-- -- --
-- -- --runX :: X b -> Maybe b
-- -- --runX x = evalSupplyT (unX x) []
-- -- --
-- -- --xx6 = runX xx5
-- -- --
-- -- ----
-- -- --
-- -- --xx7 = conGroups 
-- -- --    [ Clause [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PLit () (LInt 5))])] [] (varExpr () "e1") 
-- -- --    , Clause [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PVar () "xs")])] [] (varExpr () "e2") 
-- -- --    , Clause [Fix (PCon () "Nil" [])] [] (varExpr () "e3") 
-- -- --    ]
-- -- --
-- -- --
-- -- --xx8 :: PatternExpr ()
-- -- --xx8 =
-- -- --    ifExpr () 
-- -- --        (eqOp () (varExpr () "x") (varExpr () "y")) 
-- -- --        (litExpr () (LInt 5))
-- -- --        (litExpr () (LInt 3))
-- -- --
-- -- --xx9 :: Either InferError (PatternExpr Type, [TypeAssumption], [Constraint])
-- -- --xx9 =
-- -- --    runInfer (infer xx8)
-- -- --
-- -- ----
-- -- --
-- -- ---- let x = 3 in f x
-- -- --
-- -- ----testExpr1 :: PatternExpr ()
-- -- ----testExpr1 =
-- -- ----    eLet 
-- -- ----        (rVar () "x") 
-- -- ----        (tagLit () (LInt 3)) 
-- -- ----        (tagApp () [eVar "f", tagVar () "x"])
-- -- ----
-- -- ----test1 = r where Right r = runInfer (infer testExpr1)
-- -- ----
-- -- ------ let (Just x) = (Just 3) in x
-- -- ----
-- -- ----testRep2 :: Rep ()
-- -- ----testRep2 = rCon () "Just" [rVar () "x"]
-- -- ----
-- -- ----testExpr2 :: PatternExpr ()
-- -- ----testExpr2 =
-- -- ----    eLet 
-- -- ----        testRep2
-- -- ----        (tagApp () [tagVar () "Just", tagLit () (LInt 3)]) 
-- -- ----        (tagVar () "x")
-- -- ----
-- -- ----runTestRep2 :: (Rep Type, [TypeAssumption])
-- -- ----runTestRep2 = r where Right r = runInfer (inferRep testRep2)
-- -- ----
-- -- ----test2 :: (RepExpr Type, [TypeAssumption], [Constraint])
-- -- ----test2 = r where Right r = runInfer (infer testExpr2)
-- -- ----
-- -- ----test2Sub = sub
-- -- ----  where
-- -- ----    (tr, as, cs) = test2
-- -- ----    Right (sub, tycls) = runInfer (solve cs)
-- -- ----
-- -- ----test22 :: Infer (RepExpr Type)
-- -- ----test22 = do
-- -- ----    (tr, as, cs) <- infer testExpr2
-- -- ----    (sub, tycls) <- solve cs
-- -- ----    pure (apply sub tr)
-- -- ----
-- -- ----runTest22 = runInfer test22
-- -- ----
-- -- ------
-- -- ----
-- -- ------ match x with 
-- -- ------   | Just 3 :: [] => e1
-- -- ------   | Just x :: [] => e2
-- -- ------
-- -- ----testExpr3 =
-- -- ----    tagMatch ()
-- -- ----      [tagVar () "x"]
-- -- ----      [ Clause [pCon () "Cons" [pCon () "Just" [pLit () (LInt 3)], pCon () "Nil" []]] [] (tagVar () "e1") 
-- -- ----      , Clause [pCon () "Cons" [pCon () "Just" [pVar () "x"], pCon () "Nil" []]] [] (tagVar () "e2") 
-- -- ----      ]
-- -- ----
-- -- ----test3 = do
-- -- ----    (tr, as, cs) <- infer testExpr3
-- -- ----    pure tr
-- -- ----
-- -- ----runTest3 = runInfer test3

type List = []

mmmap :: (a -> b) -> List a -> List b
mmmap f = cata $ \case
    Nil       -> []
    Cons x xs -> f x:xs


main :: IO ()
main = pure ()
