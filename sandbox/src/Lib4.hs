{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StrictData                 #-}
module Lib4 where

import Control.Arrow
import Data.Tree.View
import Control.Monad.Except
import Data.Tree
import Data.Text (Text, pack, unpack)
import Data.Foldable (traverse_)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Map.Strict (Map)
import Data.Tuple.Extra (first3, snd3, uncurry3)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Maybe (fromMaybe)
import Tau.Expr
import Tau.Type
import Tau.Type.Class
import Tau.Type.Substitution
import Tau.Type.Inference
import Tau.Util
import Tau.Pretty
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Type.Unification as Uni
import qualified Tau.Type.Substitution as Sub


--
-- Tests

--debugTree runTest1

debugTree :: (Pretty t) => Expr t (Pattern t) (Pattern t) -> IO ()
debugTree expr = putStrLn (showTree (Text.unpack <$> toTree3 expr))

toTree3 :: (Pretty t) => Expr t (Pattern t) (Pattern t) -> Tree Text
toTree3 = cata $ \case
    EVar t var        -> node t ("Var " <> var) []
    ECon t con exs    -> node t ("Con " <> con) exs
    ELit t lit        -> node t (fromLit lit) []
    EApp t exs        -> node t "App" exs
    ELet t pat e1 e2  -> node t "Let" [pattern_ pat, e1, e2]
    ELam t pat e1     -> node t "Lam" [pattern_ pat, e1]
    EIf  t cond tr fl -> node t "If" [cond, tr, fl]
    ERec t fields     -> node t "Rec" (field <$> fields)
    EMat t exs eqs    -> node t "Mat" (exs <> (clause <$> eqs))
    _ -> error "not implemented"
  where
    clause (Clause ps exs e) = Node "*" ((pattern_ <$> ps) <> exs <> [e])

    pattern_ = cata $ \case
        PVar t var    -> node t ("Var " <> var) []
        PCon t con ps -> node t ("Con " <> con) ps
        PLit t lit    -> node t (fromLit lit) []
        PRec t fields -> node t "Rec" (field <$> fields)
        PAny t        -> node t "_" []

    field (Field _ k v) = Node (k <> " = " <> rootLabel v) []

    fromLit = pack . show 
    node t ex = Node (ex <> " : " <> pp t)

pp :: (Pretty p) => p -> Text
pp = prettyPrint 

--    prettyText = 
--        renderStrict . layoutPretty defaultLayoutOptions . pretty


test1 = lamExpr () (varPat () "x") (varExpr () "x")
runTest1 = 
    case runInfer2 mempty (infer2 mempty test1) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e

test2 = letExpr () (varPat () "x") (litExpr () (LInt 5)) (lamExpr () (varPat () "y") (varExpr () "x"))
runTest2 = 
    case runInfer2 mempty (infer2 mempty test2) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e

test3 = lamExpr () (varPat () "y") (litExpr () (LInt 5))
runTest3 = 
    case runInfer2 mempty (infer2 mempty test3) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e

test4 = letExpr () (varPat () "id") (lamExpr () (varPat () "x") (varExpr () "x")) (appExpr () [varExpr () "(,)", appExpr () [varExpr () "id", litExpr () (LInt 5)], appExpr () [varExpr () "id", litExpr () LUnit]])
runTest4 = 
    case runInfer2 as (infer2 mempty test4) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test5 = appExpr () [varExpr () "(,)", appExpr () [varExpr () "id", litExpr () (LInt 5)], appExpr () [varExpr () "id", litExpr () LUnit]]
runTest5 = 
    case runInfer2 as (infer2 mempty test5) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test6 = appExpr () [varExpr () "(,)", litExpr () (LInt 5), litExpr () LUnit]
runTest6 = 
    case runInfer2 as (infer2 mempty test6) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test7 = letExpr () (varPat () "id") (lamExpr () (varPat () "x") (varExpr () "x")) (conExpr () "(,)" [appExpr () [varExpr () "id", litExpr () (LInt 5)], appExpr () [varExpr () "id", litExpr () LUnit]])
runTest7 = 
    case runInfer2 as (infer2 mempty test7) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test8 = ifExpr () (litExpr () (LInt 5)) (litExpr () (LInt 1)) (litExpr () (LInt 2))
runTest8 = 
    case runInfer2 as (infer2 mempty test8) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test9 = ifExpr () (litExpr () (LBool True)) (litExpr () (LInt 1)) (litExpr () (LInt 2))
runTest9 = 
    case runInfer2 as (infer2 mempty test9) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test10 = recExpr () [Field () "name" (litExpr () (LString "Bob")), Field () "id" (litExpr () (LInt 10)), Field () "admin" (litExpr () (LBool True))]
runTest10 = 
    case runInfer2 as (infer2 mempty test10) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "id" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tGen 0))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]

test11 = 
    letExpr () (recPat () [Field () "name" (varPat () "x"), Field () "id" (varPat () "id")]) 
               (recExpr () [Field () "name" (litExpr () (LString "Bob")), Field () "id" (litExpr () (LInt 111))]) 
               (varExpr () "x")
runTest11 = 
    case runInfer2 as (infer2 mempty test11) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [] 


test12 = 
    letExpr () (conPat () "(,)" [varPat () "x", varPat () "y"]) 
               (conExpr () "(,)" [litExpr () (LInt 41), litExpr () (LBool True)]) 
               (varExpr () "x")
runTest12 = 
    case runInfer2 as (infer2 mempty test12) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]


test13 = 
    letExpr () (varPat () "x") (conExpr () "Some" [litExpr () (LInt 444)]) 
        (matExpr () [varExpr () "x"] [Clause [conPat () "Some" [varPat () "y"]] [] (varExpr () "y")])
runTest13 = 
    case runInfer2 as (infer2 mempty test13) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "Some" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tApp (tCon (kArr kStar kStar) "Option") (tGen 0)))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]


test14 = 
    letExpr () (varPat () "x") (conExpr () "Some" [litExpr () (LInt 444)]) 
        (matExpr () [varExpr () "x"] [Clause [conPat () "Some" [litPat () (LBool True)]] [] (litExpr () (LInt 1))])
runTest14 = 
    case runInfer2 as (infer2 mempty test14) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "Some" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tApp (tCon (kArr kStar kStar) "Option") (tGen 0)))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]


test15 = sForall kStar "a" ["Show", "Eq"] (sForall kStar "b" ["Ord"] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0))))

test16 = sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0))))

test16b = sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))



-- let { x = (a, b) } = { x = (4, 8) } in a

test17 = 
    letExpr () (recPat () [Field () "x" (conPat () "(,)" [varPat () "a", varPat () "b"])]) (recExpr () [Field () "x" (conExpr () "(,)" [litExpr () (LInt 4), litExpr () (LInt 8)])]) (varExpr () "a")

runTest17 = 
    case runInfer2 as (infer2 mempty test17) of
        Right (tree, sub) -> mapTags (apply sub) tree
        Left e -> error e
  where
    as = [As2 "Some" (sForall kStar "a" [] (sScheme (tGen 0 `tArr` tApp (tCon (kArr kStar kStar) "Option") (tGen 0)))), As2 "(,)" (sForall kStar "a" [] (sForall kStar "b" [] (sScheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kStar (kArr kStar kStar)) "(,)") (tGen 1)) (tGen 0)))))]




--
-- Type assumption

--data Assumption2 = Name :>: Scheme
data Assumption2 = As2 Name Scheme
    deriving (Show, Eq)

findAssumption :: Name -> [Assumption2] -> Maybe Scheme
findAssumption _ [] = Nothing 
findAssumption name (As2 a scheme:as)
    | a == name = Just scheme
    | otherwise = findAssumption name as

--
-- Unification

--sub1 @@ sub2 = Sub.fromList ([(u, apply sub1 t) | (u, t) <- s2] <> s1)
--  where
--    s1 = Sub.toList sub1
--    s2 = Sub.toList sub2

unify :: (MonadSupply Name m, MonadError String m) => Type -> Type -> StateT Substitution m ()
unify t1 t2 = do
    sub1 <- get
    sub2 <- Uni.unify (apply sub1 t1) (apply sub1 t2)
    modify (sub2 <>)

--
-- Inference

instantiate2 :: (MonadSupply Name m) => Scheme -> m (Type, [Predicate])
instantiate2 scheme = do
    ts <- zipWith tVar kinds <$> supplies (length kinds)
    pure (replaceBound (reverse ts) ty, [])
  where
    (ty, kinds) = flip cata scheme $ \case
        Scheme t             -> (t, [])
        Forall k _ _ (t, ks) -> (t, k:ks)

    replaceBound :: [Type] -> Type -> Type 
    replaceBound ts = cata $ \case
        TGen n     -> ts !! n
        TArr t1 t2 -> tArr t1 t2
        TApp t1 t2 -> tApp t1 t2
        TVar k var -> tVar k var
        TCon k con -> tCon k con

typeOf2 :: Expr Type p q -> Type
typeOf2 = getTag

typeOf3 :: Pattern Type -> Type
typeOf3 = getTag

newTVar :: (MonadSupply Name m) => Kind -> m Type
newTVar kind = tVar kind <$> supply 

lookupScheme :: (MonadError String m) => Name -> [Assumption2] -> m Scheme
lookupScheme name as =
    case findAssumption name as of
        Nothing     -> throwError ("Unbound identifier: " <> Text.unpack name)
        Just scheme -> pure scheme

--newtype Infer2 a = Infer2 { unInfer2 :: StateT Substitution (ReaderT [Assumption2] (SupplyT Name (ExceptT String Maybe))) a }
type Infer2 a = StateT Substitution (ReaderT [Assumption2] (SupplyT Name (ExceptT String Maybe))) a 

runInfer2 :: [Assumption2] -> Infer2 a -> Either String (a, Substitution)
runInfer2 as = 
    flip runStateT mempty
        >>> flip runReaderT as
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "xxxxxxxxxx")

--runInfer2 :: [Assumption2] -> StateT Substitution (ReaderT [Assumption2] (SupplyT Name (ExceptT String Maybe))) a -> Either String (a, Substitution)
--runInfer2 as a = fromMaybe (Left "xxxxxxxxxx") (runInfer2r a)
--  where
--    runInfer2r :: (MonadFail m) => StateT Substitution (ReaderT [Assumption2] (SupplyT Name (ExceptT String m))) a -> m (Either String (a, Substitution))
--    runInfer2r a = runExceptT (runInfer2z a)
--    runInfer2z :: (MonadFail m, MonadError String m) => StateT Substitution (ReaderT [Assumption2] (SupplyT Name m)) a -> m (a, Substitution)
--    runInfer2z a = evalSupplyT (runInfer2y a) (numSupply "a")
--    runInfer2y :: (MonadSupply Name m, MonadError String m) => StateT Substitution (ReaderT [Assumption2] m) a -> m (a, Substitution)
--    runInfer2y a = runReaderT (runInfer2x a) as
--    runInfer2x :: (MonadSupply Name m, MonadReader [Assumption2] m, MonadError String m) => StateT Substitution m a -> m (a, Substitution)
--    runInfer2x a = runStateT a mempty

infer2 
  :: (MonadSupply Name m, MonadReader [Assumption2] m, MonadError String m) 
  => ClassEnv a 
  -> PatternExpr t 
  -> StateT Substitution m (PatternExpr Type)
infer2 env = cata alg 
  where 
    alg expr = do
        newTy <- newTVar kStar
        case expr of
            EVar _ var -> do
                as <- ask
                (ty, ps) <- lookupScheme var as >>= instantiate2
                unify ty newTy
                pure (varExpr newTy var)

            ECon _ con exprs -> do
                as <- ask
                (ty, ps) <- lookupScheme con as >>= instantiate2
                es <- sequence exprs
                unify ty (foldr tArr newTy (typeOf2 <$> es))
                pure (conExpr newTy con es)

            ELit _ lit -> do
                lt <- inferLiteral2 lit
                unify newTy lt
                pure (litExpr newTy lit)

            EApp _ exprs -> do
                es <- sequence exprs
                case es of
                    []     -> pure ()
                    f:args -> unify (typeOf2 f) (foldr tArr newTy (typeOf2 <$> args))
                pure (appExpr newTy es)

            ELet _ pat expr1 expr2 -> do
                (tp, as) <- inferPattern2 pat
                e1 <- expr1
                e2 <- local (foldr (:) as) expr2
                unify newTy (typeOf2 e2)
                unify (typeOf3 tp) (typeOf2 e1)
                pure (letExpr newTy tp e1 e2)

            ELam _ pat expr1 -> do
                (tp, as) <- inferPattern2 pat
                e1 <- local (foldr (:) as) expr1
                unify newTy (typeOf3 tp `tArr` typeOf2 e1)
                pure (lamExpr newTy tp e1)

            EIf _ cond tr fl -> do
                e1 <- cond
                e2 <- tr
                e3 <- fl
                unify (typeOf2 e1) tBool
                unify (typeOf2 e2) (typeOf2 e3)
                unify newTy (typeOf2 e2)
                pure (ifExpr newTy e1 e2 e3)

            EOp  _ (OAnd a b) -> inferLogicOp2 OAnd a b
            EOp  _ (OOr  a b) -> inferLogicOp2 OOr a b
            EOp  _ _ -> undefined

            EMat _ exs eqs -> do
                es1 <- sequence exs
                es2 <- sequence (inferClause2 newTy es1 <$> eqs)
                pure (matExpr newTy es1 es2)

            ERec _ fields -> do
                let (_, ns, fs) = unzip3 (sortedFields fields)
                es <- sequence fs
                let tfs = zipWith (\n e -> Field (typeOf2 e) n e) ns es
                unify newTy (foldl tApp (recordType ns) (typeOf2 <$> es))
                pure (recExpr newTy tfs)

inferClause2 
  :: (MonadSupply Name m, MonadReader [Assumption2] m, MonadError String m) 
  => Type
  -> [Expr Type (Pattern Type) (Pattern Type)]
  -> Clause (Pattern t) (StateT Substitution m (Expr Type (Pattern Type) (Pattern Type))) 
  -> StateT Substitution m (Clause (Pattern Type) (Expr Type (Pattern Type) (Pattern Type)))
inferClause2 ty es1 clause@(Clause ps _ _) = do
    (tps, as) <- sequenced (inferPattern2 <$> ps)
    let (Clause _ exs e) = local (foldr (:) as) <$> clause
    forM_ exs (>>= unify tBool . typeOf2)
    forM_ (zip tps es1) (\(p, e2) -> unify (typeOf3 p) (typeOf2 e2)) 
    es <- sequence exs
    e1 <- e
    unify ty (typeOf2 e1)
    pure (Clause tps es e1)

inferLiteral2 :: (MonadSupply Name m) => Literal -> StateT Substitution m Type
inferLiteral2 = pure . \case
    LUnit{}    -> tUnit
    LBool{}    -> tBool
    LInt{}     -> tInt
    LInteger{} -> tInteger
    LFloat{}   -> tFloat
    LChar{}    -> tChar
    LString{}  -> tString

inferPattern2 
  :: (MonadSupply Name m, MonadReader [Assumption2] m, MonadError String m) 
  => Pattern t 
  -> StateT Substitution m (Pattern Type, [Assumption2])
inferPattern2 = cata alg
  where
    alg pat = do
        newTy <- newTVar kStar
        case pat of
            PVar _ var -> 
                pure (varPat newTy var, [As2 var (sScheme newTy)])

            PCon _ con ps -> do
                as1 <- ask
                (trs, as2) <- sequenced ps
                let as = as1 <> as2
                (ty, ps) <- lookupScheme con as >>= instantiate2
                unify ty (foldr tArr newTy (typeOf3 <$> trs))
                pure (conPat newTy con trs, as)

            PLit _ lit -> do
                lt <- inferLiteral2 lit
                pure (litPat lt lit, [])

            PRec _ fields -> do
                let (_, ns, fs) = unzip3 (sortedFields fields)
                (ps, as) <- second concat . unzip <$> sequence fs
                let tfs = zipWith (\n p -> Field (getTag p) n p) ns ps
                unify newTy (foldl tApp (recordType ns) (getTag <$> ps))
                pure (recPat newTy tfs, as)

            PAny _ -> 
                pure (anyPat newTy, [])

recordType :: [Name] -> Type
recordType names = tCon kind ("{" <> Text.intercalate "," names <> "}")
  where 
    kind = foldr kArr kStar (replicate (length names) kStar)

inferLogicOp2 
  :: (MonadSupply Name m, MonadError String m) 
  => (PatternExpr Type -> PatternExpr Type -> Op (PatternExpr Type))
  -> StateT Substitution m (PatternExpr Type)
  -> StateT Substitution m (PatternExpr Type)
  -> StateT Substitution m (PatternExpr Type)
inferLogicOp2 op a b = do
    newTy <- newTVar kStar
    e1 <- a
    e2 <- b
    unify newTy tBool
    unify (typeOf2 e1) tBool
    unify (typeOf2 e2) tBool 
    pure (opExpr newTy (op e1 e2))
