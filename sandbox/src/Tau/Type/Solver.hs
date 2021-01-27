{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Solver where

import Control.Arrow (first, second, (>>>), (<<<))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldlM, foldrM, traverse_)
import Data.List (find, delete, nub)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set, union, intersection, (\\))
import Data.Types.Injective
import Tau.Expr
import Tau.Type
import Tau.Type.Class
import Tau.Type.Inference
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

class Active a where
    active :: a -> Set Name

instance (Active a) => Active [a] where
    active = join . Set.fromList . (active <$>)

instance Active Constraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `Set.intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

modifyFst :: (MonadState (a, b) m) => (a -> a) -> m () 
modifyFst = modify . first

getFst :: (MonadState (a, b) m) => m a
getFst = gets fst

putFst :: (MonadState (a, b) m) => a -> m ()
putFst = modify . first . const

getsFst :: (MonadState (a, b) m) => (a -> c) -> m c
getsFst f = f <$> getFst

modifySnd :: (MonadState (a, b) m) => (b -> b) -> m () 
modifySnd = modify . second

getSnd :: (MonadState (a, b) m) => m b
getSnd = gets snd

putSnd :: (MonadState (a, b) m) => b -> m ()
putSnd = modify . second . const

getsSnd :: (MonadState (a, b) m) => (b -> c) -> m c
getsSnd f = f <$> getSnd

--

isSolvable :: [Constraint] -> Constraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset mono)) = Set.null vars where
    vars = free t2 \\ mono `intersection` active cs
isSolvable _ _ = True

choice :: [Constraint] -> Maybe ([Constraint], Constraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

solve__ 
  :: (MonadError String m, MonadSupply Name m) 
  => [Constraint] 
  -> m (Substitution, [(Name, Type)], [Predicate])
solve__ constraints = to <$> runStateT (solve constraints) ([], [])

solve :: (MonadError String m, MonadSupply Name m) => [Constraint] -> StateT ([(Name, Type)], [Predicate]) m Substitution
solve [] = pure mempty
solve css = do
    (cs, c) <- maybe (error "solve") pure (choice css)
    case c of 
        Equality t1 t2 -> do
            sub1 <- split =<< unify t1 t2
            sub2 <- solve (apply sub1 cs)
            modifySnd (apply sub1 <$>)
            pure (sub2 <> sub1)

        Implicit t1 t2 (Monoset set) -> do
            env <- getSnd
            t3 <- generalize env set <$> grok t2
            solve (Explicit t1 t3:cs)

        Explicit t1 scheme -> do
            t2 <- instantiate scheme
            solve (Equality t1 t2:cs)

--grok :: Type -> StateT X Infer Type
grok t = do
    sub <- getsFst (Subst . Map.fromList)
    pure (apply sub t)

--split :: Substitution -> StateT X Infer Substitution
split :: (MonadError String m, MonadSupply Name m) => Substitution -> StateT ([(Name, Type)], [Predicate]) m Substitution
split (Subst sub) = do
    sub <- Subst <$> Map.traverseWithKey (const xxx1) sub
    aaa1 <- getFst
    bbb1 <- traverse (
              \(n, t) -> do
                  case Map.lookup n (getSubst sub) of 
                      Just (Fix (TVar _ m)) -> 
                          case lookup m aaa1 of
                              Just t1 | t /= t1 -> throwError "Unif. error"
                              _ -> pure (m, t)
                      _  -> pure (n, t)
            ) aaa1
    putFst bbb1
    --gork <- traverse (fun sub) aaa1
    --putFst gork
    --modifyFst gork -- (\x -> fun sub <$> x)
    pure sub
  where
--    fun (Subst sub) = first $ \v ->
--        case unfix <$> Map.lookup v sub of 
--            Just (TVar _ w) -> pure w
--            _ -> pure v

--    xxx1 :: Type -> StateT X Infer Type
    xxx1 = cata $ \case
        tCon@(TCon kind _) -> do
            tv <- supply
            ty <- embed <$> sequence tCon
            modifyFst ((tv, ty) :)
            pure (tVar kind tv)

        ty -> 
            embed <$> sequence ty

generalize :: [Predicate] -> Set Name -> Type -> Scheme
generalize env set ty = apply sub t
  where
    (t, sub, _) = foldr go (sScheme ty, nullSubst, 0) vs

    vs = filter (flip Set.notMember set . fst) vars

    go (v, k) (t, sub, n) = do
        let cs = filter (predicateType >>> (tVar k v ==)) env
         in ( sForall k (nameSupply "" !! (m - n - 1)) (predicateName <$> cs) t
            , v `mapsTo` tGen n <> sub
            , succ n )

    m = length vars

    vars :: [(Name, Kind)]
    vars = nub . flip cata ty $ \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        _          -> []

instantiate :: (MonadSupply Name m) => Scheme -> StateT ([(Name, Type)], [Predicate]) m Type
instantiate scheme = do
    ts <- zipWith tVar kinds <$> supplies (length kinds)
    modifySnd ([InClass c t | (t, cs) <- zip ts (predicates ts), c <- cs] <>)
    pure (replaceBound (reverse ts) ty)
  where
    (ty, kinds) = flip cata scheme $ \case
        Scheme t             -> (t, [])
        Forall k _ _ (t, ks) -> (t, k:ks)

    predicates :: [Type] -> [[Name]]
    predicates ts = flip cata scheme $ \case
        Scheme{}          -> []
        Forall _ _ ps pss -> ps:pss

    replaceBound :: [Type] -> Type -> Type 
    replaceBound ts = cata $ \case
        TGen n     -> ts !! n
        TArr t1 t2 -> tArr t1 t2
        TApp t1 t2 -> tApp t1 t2
        TVar k var -> tVar k var
        TCon k con -> tCon k con

--    ty :: Type
--    ty = flip cata scheme $ \case
--        Mono t       -> t
--        Forall _ _ t -> t
--
--    kinds :: [Kind]
--    kinds = flip cata scheme $ \case
--        Mono _        -> []
--        Forall k _ ks -> k:ks

--    replace :: [Type] -> (Name, Type) -> (Name, Type)
--    replace = fmap . replaceBound
--    replace ts (n, t) = 
--        (n, replaceBound ts t)

--newtype Substitution = Subst { getSubst :: Map Name (Type, [(Name, Type)]) }
--    deriving (Show, Eq)
--
--mapsTo :: Name -> Type -> Substitution
--mapsTo name val = Subst (Map.singleton name (val, []))
--
--compose :: Substitution -> Substitution -> Substitution
--compose s1 s2 = Subst (fmap (apply2 s1) (getSubst s2) `Map.union` getSubst s1)
--
--apply1 :: Substitution -> Type -> Type
--apply1 = undefined
--
--apply2 :: Substitution -> d -> c
--apply2 = undefined
--
------class Substitutable t where
------    apply :: Substitution -> t -> t
----
----apply1 :: Substitution -> (Type, [(Name, Type)]) -> (Type, [(Name, Type)])
----apply1 (Subst sub) (t, cs) =
----    case unfix t of
----        TVar kind var -> 
----            let (t1, cs1) = Map.findWithDefault (tVar kind var, cs) var sub
----             in (t1, cs <> cs1)
----        TArr t1 t2    -> 
----            let (t1, cs1) = apply1 (Subst sub) (t1, cs)
----             in undefined -- tArr t1 t2
----        TApp t1 t2    -> undefined -- tApp t1 t2
----        ty            -> undefined -- Fix ty
----
----
----apply2 :: Substitution -> Type -> (Type, [(Name, Type)])
----apply2 (Subst sub) t = 
----    case unfix t of
----        TVar kind var -> Map.findWithDefault (tVar kind var, []) var sub
----        TArr t1 t2    -> 
----            let (xx, yy) = apply2 (Subst sub) t1
----                (zz, rr) = apply2 (Subst sub) t2
----             in (tArr xx zz, yy <> rr)
----        TApp t1 t2    -> 
----            let (xx, yy) = apply2 (Subst sub) t1
----                (zz, rr) = apply2 (Subst sub) t2
----             in (tApp xx zz, yy <> rr)
----        ty -> (Fix ty, [])
----
----substWithDefault :: Type -> Name -> Substitution -> Type
----substWithDefault def name = undefined -- Map.findWithDefault def name . getSubst
--
----
--
--unify :: (Monad m) => Type -> Type -> m Substitution
--unify t u = 
--    case (unfix t, unfix u) of
--        (TArr t1 t2, TArr u1 u2) -> 
--            unifyPairs (t1, t2) (u1, u2)
--        (TApp t1 t2, TApp u1 u2) -> 
--            undefined
--        (TVar kind name, _) -> 
--            bind name kind t
--        (_, TVar kind name) -> 
--            undefined
--        (_, _) | t == u -> 
--            undefined
--        (_, _) -> 
--            error "Cannot unify"
--
--unifyPairs :: (Monad m) => (Type, Type) -> (Type, Type) -> m Substitution
--unifyPairs (t1, t2) (u1, u2) = do
--    sub1 <- unify t1 u1
--    let (xx, yy) = apply1 sub1 t2
--    let (zz, rr) = apply1 sub1 u2
--    sub2 <- unify xx zz
--    --sub2 <- unify  (apply1 sub1 u2)
--    pure (compose sub2 sub1)
--
--bind :: (Monad m) => Name -> Kind -> Type -> m Substitution
--bind = undefined
--
----import Control.Arrow
----import Control.Monad.Reader
----import Control.Monad.Except
----import Control.Monad.State
----import Control.Monad.Supply
----import Data.Foldable (foldlM, foldrM, traverse_)
----import Data.Map.Strict (Map)
----import Data.Maybe (fromMaybe)
----import Data.List (nub, delete, find)
----import Data.Text (Text, pack)
----import Tau.Env (Env(..))
----import Data.Set.Monad (Set, union, intersection, (\\))
----import Debug.Trace
----import Tau.Env (Env)
----import Tau.Type
----import Tau.Type.Inference
----import Tau.Type.Substitution
----import Tau.Type.Unification
----import Tau.Util
----import qualified Tau.Env as Env
----import qualified Data.Set.Monad as Set
----import qualified Data.Map.Strict as Map
----
----isSolvable :: [Constraint] -> Constraint -> Bool
----isSolvable cs (Implicit _ t2 (Monoset mono)) = Set.null vars where
----    vars = free t2 \\ mono `intersection` active cs
----isSolvable _ _ = True
----
----choice :: [Constraint] -> Maybe ([Constraint], Constraint)
----choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]
----
----runUnify :: ExceptT TypeError Infer a -> Infer a
----runUnify m = runExceptT (withExceptT TypeError m) >>= liftEither
----
----type PredicateMap = Env [Predicate]
------type PredicateMap = Env [Assumption Type]
----
----solve :: [Constraint] -> Infer (Substitution, PredicateMap)
----solve = flip runStateT mempty . solver
----
----solver :: [Constraint] -> StateT PredicateMap Infer Substitution
----solver [] = pure mempty
----solver conss = do
----    (cs, c) <- maybe (throwError CannotSolve) pure (choice conss)
----    case c of 
----        Equality t1 t2 -> do
----            sub1 <- mapStateT runUnify (unify t1 t2)
----            blapp sub1
----            sub2 <- solver (apply sub1 cs)
----            pure (sub2 <> sub1)
----
----        Implicit t1 t2 (Monoset vars) -> do
----            --traceShowM t1
----            --traceShowM t2
----            t3 <- generalize vars t2
----            --traceShowM t3
----            solver (Explicit t1 t3:cs)
----
----        Explicit t1 scheme -> do
----            --traceShowM t1
----            --traceShowM scheme
----            t2 <- instantiate scheme
----            --traceShowM t2
----            solver (Equality t1 t2:cs)
----
----blapp :: Substitution -> StateT PredicateMap Infer ()
----blapp sub = do 
----    modify (Env . Map.mapKeysWith (<>) fn . getEnv)
----    --modify (Env . Map.map (apply sub) . Map.mapKeys fn . getEnv)
----  where
----    fn k = case Map.lookup k (getSubst sub) of
----        Just (Fix (TVar _ v)) -> v
----        Just (Fix t) -> trace ("xxxx :" <> show t) k
----        _ -> k
----
----
----
----bazoo t = runStateT (generalize mempty t)
----bazoo2 = bazoo (tInt `tArr` tVar kStar "a" `tArr` tVar kStar "b"  `tArr` tVar (kArr kStar kStar) "c")
----    (Env.fromList [ 
----      ("a", [ Predicate "toString" (tVar kStar "a" `tArr` tCon kStar "String") ]) 
----    , ("c", [ Predicate "isZero"   (tVar kStar "c" `tArr` tCon kStar "Bool")   ])
----    ])
----bazoo3 = s where Right (s, _) = runInfer bazoo2
----
----bazoo8 = runStateT (instantiate bazoo3) mempty
----bazoo9 = runInfer bazoo8
----
----generalize :: Set Name -> Type -> StateT PredicateMap Infer Scheme
----generalize set ty = do
----    (t, sub, _) <- foldrM go (sScheme ty, nullSubst, 0) [p | p <- vars ty, fst p `Set.notMember` set]
----    pure (apply sub t)
----  where
----    go (v, k) (t, sub, n) = do
----        env <- get
----        let os = fromMaybe [] (Env.lookup v env)
----        pure (sForall k os t, v `mapsTo` tGen n <> sub, succ n)
----
----    vars :: Type -> [(Name, Kind)]
----    vars ty = nub . flip cata ty $ \case
----        TVar k var -> [(var, k)]
----        TArr t1 t2 -> t1 <> t2
----        TApp t1 t2 -> t1 <> t2
----        ty         -> []
----
----
----bazoo99 = runInfer $ runStateT (generalize mempty (tVar kStar "a5")) mempty
----
----bazoo100 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a2" `tArr` tVar kStar "a3")
----      , Equality (tVar kStar "a2") (tVar kStar "a8") 
----      , Equality (tVar kStar "a3") (tVar kStar "a6") 
----      , Equality (tVar kStar "a4") (tVar kStar "a5") 
----      , Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a6")
----      , Implicit (tVar kStar "a7") (tVar kStar "a4") (Monoset $ Set.fromList ["x"])
----      , Explicit (tVar kStar "a5") (sForall kStar [] (sScheme (tGen 0 `tArr` tCon kStar "String")))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [9..])
----        
----
----
----tString = tCon kStar "String"
----
----bazoo101 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a2") (tVar kStar "a3" `tArr` tVar kStar "a1")
----      , Equality (tVar kStar "a3") tInt
----      , Explicit (tVar kStar "a2") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Equality (tVar kStar "a4") (tVar kStar "a5" `tArr` tVar kStar "a3" `tArr` tVar kStar "a1")
----      , Explicit (tVar kStar "a4") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----
----      --, Implicit (tVar kStar "a7") (tVar kStar "a4") (Monoset $ Set.fromList ["x"])
----      --, Equality (tVar kStar "a3") (tVar kStar "a6") 
----      --, Equality (tVar kStar "a4") (tVar kStar "a5") 
----      --, Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a6")
----      --, Implicit (tVar kStar "a7") (tVar kStar "a4") (Monoset $ Set.fromList ["x"])
----      --, Explicit (tVar kStar "a5") (sForall kStar [] (sScheme (tGen 0 `tArr` tCon kStar "String")))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [6..])
----        
----
----bazoo102 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a4")
----      , Implicit (tVar kStar "a4") (tVar kStar "a2") (Monoset mempty)
----      , Equality (tVar kStar "a2") (tVar kStar "a3")
----      , Explicit (tVar kStar "a3") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Equality (tVar kStar "a5") (tVar kStar "a6" `tArr` tVar kStar "a3")
----      , Explicit (tVar kStar "a5") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [7..])
----        
----
----
----
----bazoo103 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a4")
----      , Implicit (tVar kStar "a5") (tVar kStar "a2") (Monoset mempty)
----      , Equality (tVar kStar "a2") (tVar kStar "a3")
----      , Equality (tVar kStar "a5") (tVar kStar "a6" `tArr` tVar kStar "a4")
----      , Equality (tVar kStar "a6") tInt
----      , Explicit (tVar kStar "a3") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
------      , Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a3")
------      , Explicit (tVar kStar "a7") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [7..])
----        
----
----
----bazoo104 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a2" `tArr` tVar kStar "a3")
----      , Equality (tVar kStar "a2") (tVar kStar "a5")
----      , Equality (tVar kStar "a4") (tVar kStar "a5" `tArr` tVar kStar "a3")
----      , Explicit (tVar kStar "a4") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Equality (tVar kStar "a6") (tVar kStar "a7" `tArr` tVar kStar "a4")
----      , Explicit (tVar kStar "a6") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [8..])
----        
----
----
----
----bazoo105 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a4")
----      , Equality (tVar kStar "a2") (tVar kStar "a3")
----      , Equality (tVar kStar "a9") (tVar kStar "a10" `tArr` tVar kStar "a3")
----      , Equality (tVar kStar "a4") (tVar kStar "a5" `tArr` tVar kStar "a6")
----      , Equality (tVar kStar "a5") (tVar kStar "a8")
----      , Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a6")
----      , Implicit (tVar kStar "a7") (tVar kStar "a2") (Monoset $ Set.fromList ["x"])
----      , Explicit (tVar kStar "a3") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Explicit (tVar kStar "a9") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [11..])
----        
----
----
----
----
----bazoo106 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a2" `tArr` tVar kStar "a3")
----      , Equality (tVar kStar "a2") (tVar kStar "a8")
----      , Equality (tVar kStar "a3") (tVar kStar "a6")
----      , Equality (tVar kStar "a4") (tVar kStar "a5")
----      , Implicit (tVar kStar "a7") (tVar kStar "a4") (Monoset $ Set.fromList ["x"])
----      , Equality (tVar kStar "a9") (tVar kStar "a10" `tArr` tVar kStar "a5")
----      , Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a6")
----      , Explicit (tVar kStar "a5") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Explicit (tVar kStar "a9") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [11..])
----        
----
----
----
----bazoo107 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a4")
----      , Equality (tVar kStar "a2") (tVar kStar "a3")
----      , Implicit (tVar kStar "a4") (tVar kStar "a2") (Monoset $ Set.fromList [])
------      , Equality (tVar kStar "a5") (tVar kStar "a6" `tArr` tVar kStar "a3")
----      , Explicit (tVar kStar "a3") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
------      , Explicit (tVar kStar "a5") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      , Equality (tVar kStar "a3") (tVar kStar "x1" `tArr` tInt)
----      , Equality (tVar kStar "a2") (tVar kStar "x2" `tArr` tInt)
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [5..])
----        
----
----
----
----
----
----
----bazoo108 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a1") (tVar kStar "a4")
----      , Equality (tVar kStar "a2") (tVar kStar "a3")
----      , Equality (tVar kStar "a7") (tVar kStar "a8" `tArr` tVar kStar "a3")
----      , Equality (tVar kStar "a6") tInt
----      , Implicit (tVar kStar "a5") (tVar kStar "a2") (Monoset $ Set.fromList [])
----      , Explicit (tVar kStar "a3") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
----      , Explicit (tVar kStar "a7") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
----      , Equality (tVar kStar "a5") (tVar kStar "a6" `tArr` tVar kStar "a4")
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [9..])
----        
----
----
----bazoo109 = runInfer $ solve cs
----  where
----    cs =
----      [ Equality (tVar kStar "a2") (tVar kStar "a3" `tArr` tVar kStar "a1")
----      , Equality (tVar kStar "a3") tInt
----      , Explicit (tVar kStar "a2") (sForall kStar [Predicate "show" tString] (sScheme (tGen 0 `tArr` tInt)))
------      , Equality (tVar kStar "a2") (tVar kStar "a3")
------      , Implicit (tVar kStar "a4") (tVar kStar "a2") (Monoset $ Set.fromList [])
--------      , Equality (tVar kStar "a5") (tVar kStar "a6" `tArr` tVar kStar "a3")
--------      , Explicit (tVar kStar "a5") (sForall kStar [] (sScheme ((tGen 0 `tArr` tString) `tArr` tGen 0 `tArr` tInt)))
------      , Equality (tVar kStar "a2") (tVar kStar "x2" `tArr` tInt)
----      ]
----    runInfer = 
----        unInfer
----          >>> runExceptT
----          >>> flip runReaderT (Monoset mempty) 
----          >>> flip evalSupply numSupply
----          >>> fromMaybe (throwError ImplementationError)
----    numSupply = 
----        fmap ("a" <>) (pack . show <$> [4..])
----        
----
----
----
----
----
----
------fazoo  = runStateT (instantiate foo) mempty
------fazoo2 = runInfer fazoo 
------foo = sForall (kArr kStar kStar) [] (sForall kStar [] (sScheme (tGen 0 `tArr` tGen 1)))
----
----instantiate :: Scheme -> StateT PredicateMap Infer Type
----instantiate scheme = do
----    ns <- supplies (length ks)
----    let ts = reverse (zipWith tVar ks ns)
----    traverse_ ins (zip ns (fmap (replaceImplicit ts <$>) (bindings ts)))
----    pure (replaceBound ts ty)
----  where
----    ks = kinds scheme
----    ins (n, os) = modify (Env.insert n os)
----
----    bindings ts = flip cata scheme $ \case
----        Forall _ os oss -> os:oss
----        Mono t          -> []
----
----    ty = flip cata scheme $ \case
----        Mono t       -> t
----        Forall _ _ t -> t
----
----    kinds = cata $ \case
----        Mono t        -> []
----        Forall k _ ks -> k:ks
----
----    replaceBound :: [Type] -> Type -> Type 
----    replaceBound ts = cata $ \case
----        TGen n     -> ts !! n
----        TArr t1 t2 -> tArr t1 t2
----        TApp t1 t2 -> tApp t1 t2
----        TVar k var -> tVar k var
----        TCon k con -> tCon k con
----
----    --replaceImplicit :: [Type] -> Implicit -> Implicit
----    --replaceImplicit ts (Implicit name ty) = Implicit name (replaceBound ts ty) 
----
----    -- replaceImplicit :: [Type] -> Assumption Type -> Assumption Type
----    replaceImplicit ts (Predicate name ty) = Predicate name (replaceBound ts ty)
----
------solver :: [Constraint] -> Infer Substitution
------solver [] = pure mempty
------solver cs0 = do
------    (cs, c) <- maybe (throwError CannotSolve) pure (choice cs0)
------    case c of
------        Equality t1 t2 -> do
------            sub1 <- runUnify (unify t1 t2)
------            sub2 <- solver (apply sub1 cs)
------            pure (sub2 <> sub1)
------
------        Implicit t1 t2 (Monoset vars) ->
------            solver (Explicit t1 (generalize vars t2):cs)
------
------        Explicit t1 scheme -> do
------            t2 <- instantiate scheme
------            solver (Equality t1 t2:cs)
------
--------solve :: [Constraint] -> Infer (Substitution, [TypeClass])
--------solve = flip runStateT [] . solver
--------  where
--------    solver :: [Constraint] -> StateT [TypeClass] Infer Substitution
--------    solver [] = pure mempty
--------    solver cs0 = do
--------        traceShowM cs0
--------        (cs, c) <- maybe (throwError CannotSolve) pure (choice cs0)
--------        case c of
--------            Equality t1 t2 -> do
--------                sub1 <- mapStateT runUnify (unify t1 t2)
--------                modify (apply sub1)
--------                sub2 <- solver (apply sub1 cs)
--------                pure (sub2 <> sub1)
--------
--------            Implicit t1 t2 (Monoset vars) ->
--------                solver (Explicit t1 (generalize vars t2):cs)
--------
--------            Explicit t1 scheme -> do
--------                (t2, ps1) <- instantiate scheme
--------                modify (<> ps1)
--------                solver (Equality t1 t2:cs)
----
------generalize :: Set Name -> Type -> Scheme
------generalize set ty = Forall ks (apply s qt) where
------    qt = [] :=> ty
------    (vs, ks) = unzip [(v, k) | (v, k) <- vars ty, v `Set.notMember` set]
------    s = fromList (zip vs (tGen <$> [0..]))
------
------vars :: Type -> [(Name, Kind)]
------vars ty = nub . flip cata ty $ \case
------    TVar k var -> [(var, k)]
------    TArr t1 t2 -> t1 <> t2
------    TApp t1 t2 -> t1 <> t2
------    ty         -> mempty
------
------instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [TypeClass])
------instantiate (Forall ks s@(ps :=> t)) = do
------    ts <- traverse freshVar ks
------    pure (replaceBound ts t, instConstraint ts <$> ps)
------  where
------    freshVar k = tVar k <$> supply
------    instConstraint ts (TypeClass name ty) = TypeClass name (replaceBound ts ty)
------
------replaceBound :: [Type] -> Type -> Type 
------replaceBound ts = cata $ \case
------    TGen n     -> ts !! n
------    TArr t1 t2 -> tArr t1 t2
------    TApp t1 t2 -> tApp t1 t2
------    TVar k var -> tVar k var
------    TCon k con -> tCon k con
