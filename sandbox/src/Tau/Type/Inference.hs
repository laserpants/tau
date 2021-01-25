{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Type.Inference where

import Control.Arrow
import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Data.List (nub, delete, find, sortOn)
--import Data.Types.Isomorphic
import Data.Set.Monad (Set)
import Data.Tuple.Extra (snd3)
import Data.Types.Injective
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text

newtype Monoset = Monoset { getMonoset :: Set Name }
    deriving (Show, Eq)

instance Free Monoset where
    free (Monoset set) = set

monosetInsert :: Name -> Monoset -> Monoset
monosetInsert var (Monoset set) = Monoset (Set.insert var set)

monosetInsertSet :: Set Name -> Monoset -> Monoset
monosetInsertSet = flip (foldr monosetInsert)

data Assumption = Name :>: (Type, Monoset)
    deriving (Show, Eq)

assumptionVar :: Assumption -> Name
assumptionVar (name :>: _) = name

removeAssumption :: Name -> [Assumption] -> [Assumption]
removeAssumption name = filter (\a -> name /= assumptionVar a)

removeAssumptionSet :: Set Name -> [Assumption] -> [Assumption]
removeAssumptionSet = flip (Set.foldr removeAssumption) 

--findAssumption :: Name -> [Assumption] -> Maybe a
--findAssumption = undefined

--findAssumption :: Name -> [Assumption] -> Maybe a
--findAssumption _ [] = Nothing 
--findAssumption i (name :>: a:as)
--    | i == name = Just a
--    | otherwise = findAssumption i as

data Constraint
    = Equality Type Type
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

newtype Infer a = Infer { unInfer :: ReaderT Monoset (Supply Name) a } 
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name
    , MonadReader Monoset )

runInfer :: Infer a -> Maybe a
runInfer a = evalSupply (runReaderT (unInfer a) (Monoset mempty)) (numSupply "a")

infer_
  :: (MonadReader Monoset m, MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) 
  -> m ((Expr Name (Pattern Name) (Pattern Name), [Assumption]), [Constraint])
infer_ = runWriterT . infer

infer___
  :: (MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) 
  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption], [Constraint])
infer___ = flip runReaderT (Monoset mempty) . (to <$>) . infer_ 

infer__
  :: (MonadReader Monoset m, MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) 
  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption], [Constraint])
infer__ = (to <$>) . infer_ 

infer
  :: (MonadReader Monoset m, MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) 
  -> WriterT [Constraint] m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
infer = cata $ \case

    EVar _ var -> do
        tv <- supply
        set <- ask
        pure ( varExpr tv var
             , [var :>: (tVar kStar tv, set)] )

    ECon _ con exprs -> do
        tv1 <- supply
        tv2 <- supply
        set <- ask
        (es1, as1) <- sequenced exprs
        tell [Equality (tVar kStar tv2) (foldr tArr (tVar kStar tv1) (typeOf <$> es1))]
        pure ( conExpr tv1 con es1
             , as1 <> [con :>: (tVar kStar tv2, set)] )

    ELit _ lit -> do
        tv <- supply
        lt <- inferLiteral lit
        tell [Equality (tVar kStar tv) lt]
        pure ( litExpr tv lit, [] )

    EApp _ exprs -> do
        tv <- supply
        (es1, as1) <- sequenced exprs
        tell $ case es1 of
            []   -> []
            e:es -> [ Equality (typeOf e) (foldr tArr (tVar kStar tv) (typeOf <$> es)) ]
        pure ( appExpr tv es1, as1 )

    ELet _ pat expr1 expr2 -> do
        tv <- supply
        (tp, as0) <- inferPattern pat
        (e1, as1) <- expr1
        (e2, as2) <- expr2
        tell [ Equality (tVar kStar tv) (typeOf e2) 
             , Equality (typeOf tp) (typeOf e1) ]
        tell $ do 
            v :>: (t, set) <- as2
            w :>: (u, _) <- as0
            guard (v == w)
            pure (Implicit t u set)
        pure ( letExpr tv tp e1 e2
             , as1 <> removeAssumptionSet (free tp) (as0 <> as2) )

    ELam _ pat expr1 -> do
        tv <- supply
        (tp, as0) <- inferPattern pat
        (e1, as1) <- local (monosetInsertSet (free tp)) expr1
        tell [Equality (tVar kStar tv) (typeOf tp `tArr` typeOf e1)]
        tell $ do
            v :>: (t, _) <- as1
            w :>: (u, _) <- as0
            guard (v == w)
            pure (Equality t u)
        pure ( lamExpr tv tp e1
             , removeAssumptionSet (free tp) (as0 <> as1) )

    EIf _ cond tr fl -> do
        tv <- supply
        (e1, as1) <- cond
        (e2, as2) <- tr
        (e3, as3) <- fl
        tell [ Equality (tVar kStar tv) (typeOf e2) 
             , Equality (tVar kStar tv) (typeOf e3)
             , Equality (typeOf e1) tBool ]
        pure ( ifExpr tv e1 e2 e3, as1 <> as2 <> as3 )

    EOp  _ (OAnd a b) -> inferLogicOp OAnd a b
    EOp  _ (OOr  a b) -> inferLogicOp OOr a b

    EMat _ exs eqs -> do
        tv <- supply
        (es1, as1) <- sequenced exs
        (es2, as2) <- sequenced (inferClause <$> eqs)
        tell $ concat $ do
            Clause ps exs e <- es2
            e1 <- exs
            (p, e2) <- zip ps es1
            pure [ Equality (tVar kStar tv) (typeOf e)
                 , Equality tBool (typeOf e1)
                 , Equality (typeOf p) (typeOf e2) ]
        pure ( matExpr tv es1 es2
             , as1 <> as2 )

    ERec _ fields -> do
        tv <- supply
        let info = sortedFields fields
            tagField (_, n, v) = first (\a -> Field (getTag a) n a) <$> v
        (fs, as1) <- sequenced (tagField <$> info)
        tell (recordConstraints tv info fs)
        pure ( recExpr tv fs
             , as1 )

recordConstraints :: Name -> [(t, Name, v)] -> [Field Name a] -> [Constraint] 
recordConstraints tv info fs = 
    [Equality (tVar kStar tv) (foldl tApp (tCon kind constr) (typeOf <$> fs))]
  where 
    kind = foldr kArr kStar (replicate (length info) kStar)
    constr = "{" <> Text.intercalate "," (snd3 <$> info) <> "}"

inferClause 
  :: (MonadReader Monoset m, MonadSupply Name m)  
  => Clause (Pattern t) (WriterT [Constraint] m (Expr Name (Pattern Name) (Pattern Name), [Assumption])) 
  -> WriterT [Constraint] m (Clause (Pattern Name) (Expr Name (Pattern Name) (Pattern Name)), [Assumption])
inferClause clause@(Clause ps _ _) = do
    (tps, as0) <- sequenced (inferPattern <$> ps)
    let (Clause _ exs e) = local (monosetInsertSet (free tps)) <$> clause
    (es1, as1) <- sequenced exs
    (es2, as2) <- e 
    tell $ do
        v :>: (t, _) <- as1 <> as2
        w :>: (u, _) <- as0
        guard (v == w)
        pure (Equality t u)
    pure ( Clause tps es1 es2
         , removeAssumptionSet (free tps) (as0 <> as1 <> as2) )

inferLogicOp
  :: (MonadReader Monoset m, MonadSupply Name m) 
  => (Expr Name (Pattern Name) (Pattern Name) -> Expr Name (Pattern Name) (Pattern Name) -> Op (Expr Name (Pattern Name) (Pattern Name)))
  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
inferLogicOp op a b = do 
    tv <- supply
    (e1, as1) <- a
    (e2, as2) <- b
    let cs = [ Equality (tVar kStar tv) tBool 
             , Equality (typeOf e1) tBool
             , Equality (typeOf e2) tBool ]
    pure ( opExpr tv (op e1 e2)
         , as1 <> as2 )

inferPattern
  :: (MonadReader Monoset m, MonadSupply Name m) 
  => Pattern t 
  -> WriterT [Constraint] m (Pattern Name, [Assumption])
inferPattern = cata $ \pat -> do
    tv <- supply
    set <- ask
    case pat of
        PVar _ var -> 
            pure ( varPat tv var
                 , [var :>: (tVar kStar tv, set)] )

        PCon _ con ps -> do
            tv1 <- supply
            (trs, as) <- sequenced ps
            tell [Equality (tVar kStar tv1) (foldr tArr (tVar kStar tv) (typeOf <$> trs))]
            pure ( conPat tv con trs
                 , as <> [con :>: (tVar kStar tv1, set)] )

        PLit _ lit -> do
            t <- inferLiteral lit
            tell [Equality (tVar kStar tv) t]
            pure ( litPat tv lit, [] )

        PRec _ fields -> do
            let info = sortedFields fields
            fs <- traverse (\(_, n, v) -> supply >>= \t -> pure $ Field t n v) info
            tell (recordConstraints tv info fs)
            pure ( recPat tv fs, [] )

        PAny _ -> 
            pure ( anyPat tv, [] )

inferLiteral :: (Monad m) => Literal -> m Type
inferLiteral = pure . \case
    LUnit{}   -> tUnit
    LBool{}   -> tBool
    LInt{}    -> tInt
    LString{} -> tString

sequenced :: (Monad m) => [m (a, [b])] -> m ([a], [b])
sequenced = (second concat . unzip <$>) . sequence

typeOf :: (TaggedA a Name) => a -> Type
typeOf = tVar kStar . getTag 

--

instance Substitutable Constraint where
    apply sub (Equality t1 t2)     = Equality (apply sub t1) (apply sub t2)
    apply sub (Implicit t1 t2 set) = Implicit (apply sub t1) (apply sub t2) (apply sub set)
    apply sub (Explicit t1 scheme) = Explicit (apply sub t1) (apply sub scheme)

instance Substitutable Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . tVar kStar =<< set)

instance Substitutable Scheme where
    apply sub = cata $ \case
        Forall k cs s -> sForall k cs s
        Scheme t      -> sScheme (apply sub t)

--patternVars :: Pattern t -> [(Name, t)]
--patternVars = cata $ \case
--    PVar t var  -> [(var, t)]
--    PCon _ _ ps -> concat ps
--    PLit _ lit  -> []
--    PAny _      -> []
--
--choice :: [Thing Constraint] -> Maybe ([Thing Constraint], Thing Constraint)
--choice xs = find solvable [(ys, x) | x <- xs, let ys = delete x xs]
--
--solve :: (Monad m) => ([Thing Constraint], [Thing [(Name, Type)]]) -> m ([Thing Constraint], [Thing [(Name, Type)]])
--solve (xs, _) = do
--    (cs, (_, t1, c)) <- maybe (error "x") pure (choice xs)
--    case c of 
--        Equality t2 -> do
--            sub1 <- unify t1 t2
--            undefined
--            --sub2 <- solve (apply sub1 cs)
--            --pure (cs, undefined)
--            --pure (compose sub2 sub1)
--
--        Implicit t2 (Monoset set) ->
--            undefined
--
--        Explicit scheme -> 
--            undefined
--
--unify = undefined
--
--apply = undefined
--
--compose = undefined
--
----
--
--newtype Monoset = Monoset { getMonoset :: Set Name }
--    deriving (Show, Eq)
--
--data Assumption = Name :>: Type
--    deriving (Show, Eq)
--
--data Constraint
--    = Equality Type
--    | Implicit Type Monoset
--    | Explicit Scheme
--    deriving (Show, Eq)
--
--data Name = Name Name [Constraint] Monoset
--    deriving (Show, Eq)
--
--newtype Infer a = Infer { unInfer :: ReaderT Monoset (Supply Name) a } 
--  deriving
--    ( Functor
--    , Applicative
--    , Monad
--    , MonadSupply Name
--    , MonadReader Monoset )
--
--runInfer :: Infer a -> Maybe a
--runInfer a = evalSupply (runReaderT (unInfer a) (Monoset mempty)) (numSupply "a")
--
--infer
--  :: (MonadReader Monoset m, MonadSupply Name m) 
--  => Expr t (Pattern t) (Pattern t) 
--  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
--infer = cata $ \case
--
--    EVar _ var -> do
--        tv <- supply
--        set <- ask
--        pure ( varExpr (Name tv [] set) var
--             , [var :>: tVar kStar tv] )
--
--    ECon _ con exprs -> do
--        tv1 <- supply
--        tv2 <- supply
--        set <- ask
--        (es1, as1) <- sequenced exprs
--        let cs = [Equality (foldr tArr (tVar kStar tv2) (typeOf <$> es1))]
--        pure ( conExpr (Name tv1 cs set) con es1
--             , as1 <> [con :>: tVar kStar tv1] )
--
--    ELit _ lit -> do
--        tv <- supply
--        lt <- inferLiteral lit
--        set <- ask
--        let cs = [Equality lt]
--        pure ( litExpr (Name tv cs set) lit, [] )
--
--    EApp _ exprs ->
--        foldl1 inferApp exprs
--
--    ELet _ pat expr1 expr2 -> do
--        tv <- supply
--        (tp, as0) <- inferPattern pat
--        (e1, as1) <- expr1
--        (e2, as2) <- expr2
--        set <- ask
--        let cs = [Equality (typeOf e2)]
--        let e2' = injectConstraints (\t set -> [Implicit t set]) as0 e2
--        pure ( letExpr (Name tv cs set) (addConstraint (Equality (typeOf e1)) tp) e1 e2'
--             , as1 <> removeAssumptionSet (free tp) (as0 <> as2) )
--
--    ELam _ pat expr1 -> do
--        tv <- supply
--        (tp, as0) <- inferPattern pat
--        (e1, as1) <- local (monosetInsertSet (free tp)) expr1
--        set <- ask
--        let cs = [Equality (fromPatternTag tp `tArr` typeOf e1)]
--        let e1' = injectConstraints (\t _ -> [Equality t]) as0 e1
--        pure ( lamExpr (Name tv cs set) tp e1'
--             , removeAssumptionSet (free tp) (as0 <> as1) )
--
--    EIf _ cond tr fl -> do
--        tv <- supply
--        (e1, as1) <- cond
--        (e2, as2) <- tr
--        (e3, as3) <- fl
--        set <- ask
--        let cs = [Equality (typeOf e2)]
--        pure ( ifExpr (Name tv cs set) 
--                      (addConstraint2 (Equality tBool) e1) 
--                      (addConstraint2 (Equality (typeOf e3)) e2) 
--                      e3
--             , as1 <> as2 <> as3 )
--
--    EOp  _ (OAnd a b) -> inferLogicOp OAnd a b
--    EOp  _ (OOr  a b) -> inferLogicOp OOr a b
--
--    EMat _ exs eqs -> do
--        tv <- supply
--        (es1, as1) <- sequenced exs
--        (es2, as2) <- sequenced (inferClause es1 <$> eqs)
--        set <- ask
--        let cs = concat $ es2 >>= \c -> pure [Equality (fromClauseTag c)]
--        pure ( matExpr (Name tv cs set) es1 es2
--             , as1 <> as2 )
--
--inferClause 
--  :: (MonadReader Monoset m, MonadSupply Name m) 
--  => [Expr Name (Pattern Name) (Pattern Name)]
--  -> Clause (Pattern t) (m (Expr Name (Pattern Name) (Pattern Name), [Assumption])) 
--  -> m (Clause (Pattern Name) (Expr Name (Pattern Name) (Pattern Name)), [Assumption])
--inferClause es clause@(Clause ps _ _) = do
--    (tps, as0) <- sequenced (inferPattern <$> ps)
--    let (Clause _ exs e) = local (monosetInsertSet (free tps)) <$> clause
--    (es1, as1) <- sequenced exs
--    (es2, as2) <- e 
--    let es2' = injectConstraints (\t _ -> [Equality t]) (as0 <> as1) es2
--    pure ( Clause (fn <$> zip es tps) (addConstraint2 (Equality tBool) <$> es1) es2'
--         , removeAssumptionSet (free tps) (as0 <> as1 <> as2) )
--  where
--    fn (e, p) = addConstraint (Equality (typeOf e)) p
--
--inferLogicOp
--  :: (MonadReader Monoset m, MonadSupply Name m) 
--  => (Expr Name p q -> Expr Name p q -> Op (Expr Name p q))
--  -> m (Expr Name p q, [Assumption])
--  -> m (Expr Name p q, [Assumption])
--  -> m (Expr Name p q, [Assumption])
--inferLogicOp op a b = do
--    tv <- supply
--    (e1, as1) <- a
--    (e2, as2) <- b
--    set <- ask
--    let cs = [Equality tBool]
--    pure ( opExpr (Name tv cs set) 
--                  (op (addConstraint2 (Equality tBool) e1) 
--                      (addConstraint2 (Equality tBool) e2))
--         , as1 <> as2 )
--
--inferPattern
--  :: (MonadReader Monoset m, MonadSupply Name m) 
--  => Pattern t 
--  -> m (Pattern Name, [Assumption])
--inferPattern = cata $ \pat -> do
--    tv <- supply
--    set <- ask
--    let node = Name tv [] set
--    case pat of
--        PVar _ var -> 
--            pure ( varPat node var
--                 , [var :>: tVar kStar tv] )
--
--        PCon _ con ps -> do
--            (trs, as) <- sequenced ps
--            pure ( conPat node con trs
--                 , as <> [con :>: tVar kStar con] )
--
--        PLit _ lit -> do
--            t <- inferLiteral lit
--            pure ( litPat node lit, [] )
--
--        PAny _ -> 
--            pure ( anyPat node, [] )
--
--inferApp
--  :: (MonadReader Monoset m, MonadSupply Name m) 
--  => m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
--  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
--  -> m (Expr Name (Pattern Name) (Pattern Name), [Assumption])
--inferApp expr1 expr2 = do
--    tv <- supply
--    (e1, as1) <- expr1
--    (e2, as2) <- expr2
--    set <- ask
--    pure ( appExpr (Name tv [] set) [addConstraint2 (Equality (typeOf e2 `tArr` tVar kStar tv)) e1, e2]
--         , as1 <> as2 )
--
--inferLiteral :: (Monad m) => Literal -> m Type
--inferLiteral = pure . \case
--    LUnit{} -> tUnit
--    LBool{} -> tBool
--    LInt{}  -> tInt
--
--injectConstraints
--  :: (Type -> Monoset -> [Constraint]) 
--  -> [Assumption] 
--  -> Expr Name p q 
--  -> Expr Name p q
--injectConstraints toc as = cata $ \case
--    EVar (Name t cs set) var ->
--        varExpr (Name t (cs <> concatMap fn as) set) var
--      where
--        fn (name :>: t1) 
--            | name == var = toc t1 set
--            | otherwise   = []
--    e -> 
--        embed e
--
--sequenced :: (Monad m) => [m (a, [b])] -> m ([a], [b])
--sequenced = (second concat . unzip <$>) . sequence

--addConstraint :: Constraint -> Pattern Name -> Pattern Name
--addConstraint = modifyPatternTag . addConstraint1
--
--addConstraint1 :: Constraint -> Name -> Name
--addConstraint1 c (Name t cs set) = Name t (c:cs) set
--
--addConstraint2 :: Constraint -> Expr Name p q -> Expr Name p q
--addConstraint2 = modifyTag . addConstraint1
--
--nodeTag :: Name -> Name
--nodeTag (Name t _ _) = t
--
--typeOf :: Expr Name p q -> Type
--typeOf = tVar kStar . nodeTag . getTag
--
--fromPatternTag :: Pattern Name -> Type
--fromPatternTag = tVar kStar . nodeTag . getPatternTag
--
--fromClauseTag :: Clause p (Expr Name p q) -> Type
--fromClauseTag (Clause _ _ e) = typeOf e
--
--monosetInsert :: Name -> Monoset -> Monoset
--monosetInsert var (Monoset set) = Monoset (Set.insert var set)
--
--monosetInsertSet :: Set Name -> Monoset -> Monoset
--monosetInsertSet = flip (foldr monosetInsert)
--
----import Control.Arrow
----import Control.Monad.Except
----import Control.Monad.Reader
----import Control.Monad.Supply
----import Control.Monad.Writer
----import Data.Foldable (foldrM, foldl')
----import Data.Maybe (fromMaybe)
----import Data.Text (pack)
----import Data.Set.Monad (Set, union, intersection, (\\))
----import Tau.Expr
----import Tau.Expr.Patterns
----import Tau.Type
----import Tau.Type.Substitution
----import Tau.Type.Unification
----import Tau.Util
----import qualified Data.Set.Monad as Set
----
----data Constraint
----    = Equality Type Type
----    | Implicit Type Type Monoset
----    | Explicit Type Scheme
----    deriving (Show, Eq)
----
----instance Substitutable Constraint where
----    apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
----    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
----    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)
----
----class Active a where
----    active :: a -> Set Name
----
----instance (Active a) => Active [a] where
----    active = join . Set.fromList . fmap active
----
----instance Active Constraint where
----    active (Equality t1 t2)      = free t1 `union` free t2
----    active (Implicit t1 t2 mono) = free t1 `union` (free mono `Set.intersection` free t2)
----    active (Explicit ty scheme)  = free ty `union` free scheme
----
----newtype Monoset = Monoset { getMonoset :: Set Name }
----    deriving (Show, Eq)
----
----instance Substitutable Monoset where
----    apply sub (Monoset set) = Monoset (free . apply sub . tVar kStar =<< set)
----
----instance Free Monoset where
----    free (Monoset set) = set
----
----monosetInsert :: Name -> Monoset -> Monoset
----monosetInsert var (Monoset set) = Monoset (Set.insert var set)
----
----monosetInsertSet :: [Name] -> Monoset -> Monoset
----monosetInsertSet = flip (foldr monosetInsert)
----
----data Assumption a = Name :>: a
----    deriving (Show, Eq, Functor, Foldable, Traversable)
----
----instance (Substitutable t) => Substitutable (Assumption t) where
----    apply = fmap . apply 
----
----instance (Free t) => Free (Assumption t) where
----    free (_ :>: t) = free t
----
----assumptionVar :: Assumption a -> Name
----assumptionVar (name :>: _) = name
----
------findAssumption :: Name -> [Assumption a] -> Maybe a
------findAssumption _ [] = Nothing 
------findAssumption i (name :>: a:as)
------    | i == name = Just a
------    | otherwise = findAssumption i as
----
----removeAssumption :: Name -> [Assumption a] -> [Assumption a]
----removeAssumption name = filter (\a -> name /= assumptionVar a)
----
----removeAssumptionSet :: Set Name -> [Assumption a] -> [Assumption a]
----removeAssumptionSet = flip (Set.foldr removeAssumption) 
----
----
----type TypeAssumption = Assumption Type
----
----data InferError 
----    = CannotSolve
----    | TypeError TypeError
----    | ImplementationError
----    deriving (Show, Eq)
----
----newtype Infer a = Infer { unInfer :: ExceptT InferError (ReaderT Monoset (Supply Name)) a } 
----  deriving
----    ( Functor
----    , Applicative
----    , Monad
----    , MonadSupply Name
----    , MonadReader Monoset 
----    , MonadError InferError )
----
----runInfer :: Infer a -> Either InferError a
----runInfer = 
----    unInfer
----      >>> runExceptT
----      >>> flip runReaderT (Monoset mempty) 
----      >>> flip evalSupply (numSupply "a")
----      >>> fromMaybe (throwError ImplementationError)
----
----
----newtype Infer_ a = Infer_ { unInfer_ :: WriterT [Constraint] (ExceptT InferError (ReaderT Monoset (Supply Name))) a } 
----  deriving
----    ( Functor
----    , Applicative
----    , Monad
----    , MonadSupply Name
----    , MonadReader Monoset 
----    , MonadWriter [Constraint]
----    , MonadError InferError )
----
----
------runInfer_ :: Infer_ a -> Either InferError (a, [Constraint])
------runInfer_ = 
------    unInfer_
------      >>> runWriterT
------      >>> runExceptT
------      >>> flip runReaderT (Monoset mempty) 
------      >>> flip evalSupply (numSupply "a")
------      >>> fromMaybe (throwError ImplementationError)
----
----
----infer__ 
----  :: Expr t (Pattern t) (Pattern t) 
----  -> Infer ((Expr Name (Pattern Name) (Pattern Name), [Assumption Name]), [Constraint])
----infer__ =
----    runWriterT . infer_ 
----
----
----infer_
----  :: Expr t (Pattern t) (Pattern t) 
----  -> WriterT [Constraint] Infer (Expr Name (Pattern Name) (Pattern Name), [Assumption Name])
----infer_ = cata $ \case
----
----    EVar _ var -> do
----        tvar <- supply
----        pure (varExpr tvar var, [var :>: tvar])
----
----    ECon _ con exprs -> do
----        tvar1 <- supply
----        tvar2 <- supply
----        (es1, as1) <- sequenced_ exprs
----        tell [ Equality (tVar kStar tvar1) 
----                        (foldr tArr (tVar kStar tvar2) (typeOf <$> es1)) ]
----        pure (conExpr tvar2 con es1, as1 <> [con :>: tvar1])
----
----    ELit _ lit -> do
----        tvar <- supply
----        t <- inferLiteral_ lit
----        tell [ Equality (tVar kStar tvar) t ] 
----        pure (litExpr tvar lit, [])
----
----    EApp _ exprs ->
----        foldl1 inferApp_ exprs
----
----    ELet _ pat expr1 expr2 -> do
----        tvar <- supply
----        (tp, as0) <- inferPattern_ pat
----        (e1, as1) <- expr1
----        (e2, as2) <- expr2
----        set <- ask
----        tell [ Equality (tVar kStar tvar) (typeOf e2) 
----             , Equality (fromPatternTag tp) (typeOf e1) ]  
----
----        tell $ do
----            v :>: t <- as2
----            (w, u) <- patternVars tp
----            guard (v == w)
----            pure (Implicit (tVar kStar t) (tVar kStar u) set)
----
----        pure (letExpr tvar tp e1 e2, as1 <> removeAssumptionSet (free tp) as2)
----
----    ELam _ pat expr1 -> do
----        tvar <- supply
----        (tp, as0) <- inferPattern_ pat
----        (e1, as1) <- local (monosetInsertSet (assumptionVar <$> as0)) expr1
----        tell [ Equality (tVar kStar tvar) (fromPatternTag tp `tArr` typeOf e1) ]
----
----        tell $ do
----            v :>: t <- as1
----            (w, u) <- patternVars tp
----            guard (v == w)
----            pure (Equality (tVar kStar t) (tVar kStar u))
----
----        pure (lamExpr tvar tp e1, removeAssumptionSet (free tp) as1)
----
----    EIf _ cond tr fl -> do
----        tvar <- supply
----        (e1, as1) <- cond
----        (e2, as2) <- tr
----        (e3, as3) <- fl
----
----        tell [ Equality (tVar kStar tvar) (typeOf e2)
----             , Equality (typeOf e1) tBool
----             , Equality (typeOf e2) (typeOf e3) ]
----
----        pure (ifExpr tvar e1 e2 e3, as1 <> as2 <> as3)
----
----    EOp  _ (OAnd a b) ->
----        inferLogicOp_ a b
----
----    EOp  _ (OOr a b) -> 
----        inferLogicOp_ a b
----
----    EMat _ exs eqs -> do
----        tvar <- supply
----        (es1, as1) <- sequenced_ exs
----        (eqs, as2) <- sequenced_ (inferClause_ <$> eqs)
----
----        let cs3 = concat $ do
----            Clause ps exs e <- eqs
----            e1 <- exs
----            (p, e2) <- zip ps es1
----            pure [ Equality (tVar kStar tvar) (typeOf e)
----                 , Equality tBool (typeOf e1)
----                 , Equality (fromPatternTag p) (typeOf e2) ]
----
----        pure (matExpr tvar es1 eqs, as1 <> as2)
----
----typeOf :: Expr Name p q -> Type
----typeOf = tVar kStar . getTag
----
----fromPatternTag :: Pattern Name -> Type
----fromPatternTag = tVar kStar . getPatternTag
----
----sequenced_ :: [WriterT [Constraint] Infer (a, [Assumption Name])] -> WriterT [Constraint] Infer ([a], [Assumption Name])
----sequenced_ = fmap (fmap concat . unzip) . sequence 
----
----inferLogicOp_ 
----  :: WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
----  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
----  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name])
----inferLogicOp_ a b = do
----    tvar <- supply
----    (e1, as1) <- a
----    (e2, as2) <- b
----
----    tell [ Equality (tVar kStar tvar) tBool 
----         , Equality (typeOf e1) tBool
----         , Equality (typeOf e2) tBool ]
----
----    pure (andOp tvar e1 e2, as1 <> as2)
----
----inferClause_
----  :: Clause (Pattern t) (WriterT [Constraint] Infer (Expr Name (Pattern Name) q, [Assumption Name])) 
----  -> WriterT [Constraint] Infer (Clause (Pattern Name) (Expr Name (Pattern Name) q), [Assumption Name])
----inferClause_ eq@(Clause ps _ _) = do
----    (tps, as0) <- fmap concat . unzip <$> traverse inferPattern_ ps
----    let Clause _ exs e = local (monosetInsertSet (assumptionVar <$> as0)) <$> eq
----    (es1, as1) <- sequenced_ exs
----    (exp, as2) <- e 
----
----    tell $ do
----        v :>: t <- as1 <> as2
----        (w, u) <- patternVars =<< tps
----        guard (v == w)
----        pure (Equality (tVar kStar t) (tVar kStar u))
----
----    pure (Clause tps es1 exp, as0 <> removeAssumptionSet (free tps) (as1 <> as2))
----
----inferPattern_ :: Pattern t -> WriterT [Constraint] Infer (Pattern Name, [Assumption Name])
----inferPattern_ = cata $ \pat -> do
----    tvar <- supply
----    case pat of
----        PVar _ var -> 
----            pure (varPat tvar var, [var :>: tvar])
----
----        PCon _ con ps -> do
----            (trs, as) <- unzip <$> sequence ps
----            pure (conPat tvar con trs, concat as <> [con :>: tvar])
----
----        PLit _ lit -> do
----            t <- inferLiteral_ lit
----            pure (litPat tvar lit, [])
----
----        PAny _ -> 
----            pure (anyPat tvar, [])
----
----inferApp_
----  :: WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
----  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
----  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name])
----inferApp_ expr1 expr2 = do
----    tvar <- supply
----    (e1, as1) <- expr1
----    (e2, as2) <- expr2
----
----    tell [ Equality (typeOf e1) (typeOf e2 `tArr` tVar kStar tvar) ]
----
----    pure (appExpr tvar [e1, e2], as1 <> as2)
----
----inferLiteral_ :: Literal -> WriterT [Constraint] Infer Type
----inferLiteral_ = pure . \case
----    LUnit{} -> tUnit
----    LBool{} -> tBool
----    LInt{}  -> tInt
----
----
------ ***********
------ ***********
------ ***********
------ ***********
------ ***********
----
----
----infer 
----  :: Expr t (Pattern t) (Pattern t) 
----  -> Infer (Expr Type (Pattern Type) (Pattern Type), [TypeAssumption], [Constraint])
----infer = cata $ \case
----    EVar _ var -> do
----        name <- supply
----        let t = tVar kStar name 
----        pure (varExpr t var, [var :>: t], [])
----
----    ECon _ con exprs -> do
----        name <- supply
----        let t = tVar kStar name 
----        (es1, as1, cs1) <- sequenced exprs
----        pure ( conExpr t con es1
----             , as1 <> [con :>: foldr tArr t (getTag <$> es1)]
----             , cs1 )
----
----    ELit _ lit -> do
----        t <- inferLiteral lit
----        pure (litExpr t lit, [], [])
----
----    EApp _ exprs ->
----        foldl1 inferApp exprs
----
----    ELet _ pat expr1 expr2 -> do
----        (tp, as0) <- inferPattern pat
----        (e1, as1, cs1) <- expr1
----        (e2, as2, cs2) <- expr2
----        set <- ask
----        let cs3 = [Implicit t u set | v :>: t <- as2, (w, u) <- patternVars tp, v == w]
----        pure ( letExpr (getTag e2) tp e1 e2
----             , as1 <> removeAssumptionSet (free tp) as2
----             , cs1 <> cs2 <> [Equality (getPatternTag tp) (getTag e1)] <> cs3 )
----
----    ELam _ pat expr1 -> do
----        (tp, as0) <- inferPattern pat
----        (e1, as1, cs1) <- local (monosetInsertSet (assumptionVar <$> as0)) expr1
----        let cs2 = [Equality t u | v :>: t <- as1, (w, u) <- patternVars tp, v == w]
----        pure ( lamExpr (getPatternTag tp `tArr` getTag e1) tp e1
----             , removeAssumptionSet (free tp) as1
----             , cs1 <> cs2 )
----
----    EIf _ cond tr fl -> do
----        (e1, as1, cs1) <- cond
----        (e2, as2, cs2) <- tr
----        (e3, as3, cs3) <- fl
----        pure ( ifExpr (getTag e2) e1 e2 e3
----             , as1 <> as2 <> as3
----             , cs1 <> cs2 <> cs3 <> [Equality (getTag e1) tBool, Equality (getTag e2) (getTag e3)])
----
----    EOp  _ (OEq a b) -> do
----        (e1, as1, cs1) <- a
----        (e2, as2, cs2) <- b
----        pure ( eqOp tBool e1 e2
----             , as1 <> as2
----             , cs1 <> cs2 )
----
----    EOp  _ (OAnd a b) -> do
----        (e1, as1, cs1) <- a
----        (e2, as2, cs2) <- b
----        pure ( andOp tBool e1 e2
----             , as1 <> as2
----             , cs1 <> cs2 )
----
----    EOp  _ (OOr a b) -> do
----        (e1, as1, cs1) <- a
----        (e2, as2, cs2) <- b
----        pure ( orOp tBool e1 e2
----             , as1 <> as2
----             , cs1 <> cs2 )
----
----    EMat _ exs eqs -> do
----        name <- supply
----        let t = tVar kStar name 
----        (es1, as1, cs1) <- sequenced exs
----        (eqs, as2, cs2) <- sequenced (inferClause <$> eqs)
----
----        let cs3 = concat $ do
----            Clause ps exs e <- eqs
----            e1 <- exs
----            (p, e2) <- zip ps es1
----            pure [ Equality t (getTag e)
----                 , Equality tBool (getTag e1)
----                 , Equality (getPatternTag p) (getTag e2) ]
----
----        pure ( matExpr t es1 eqs
----             , as1 <> as2
----             , cs1 <> cs2 <> cs3 )
----
----inferClause 
----  :: Clause (Pattern t) (Infer (Expr Type (Pattern Type) q, [Assumption Type], [Constraint])) 
----  -> Infer (Clause (Pattern Type) (Expr Type (Pattern Type) q), [TypeAssumption], [Constraint])
----inferClause eq@(Clause ps _ _) = do
----    (tps, as0) <- fmap concat . unzip <$> traverse inferPattern ps
----
----    let Clause _ exs e = local (monosetInsertSet (assumptionVar <$> as0)) <$> eq
----    (es1, as1, cs1) <- sequenced exs
----    (exp, as2, cs2) <- e 
----    let cs3 = [Equality t u | v :>: t <- as1 <> as2, (w, u) <- patternVars =<< tps, v == w]
----
----    pure ( Clause tps es1 exp
----         , as0 <> removeAssumptionSet (free tps) (as1 <> as2)
----         , cs1 <> cs2 <> cs3 )
----
----sequenced :: [Infer (a, [TypeAssumption], [Constraint])] -> Infer ([a], [TypeAssumption], [Constraint])
----sequenced = fmap (go . unzip3) . sequence where
----    go (a, as, cs) = (a, concat as, concat cs)
----
----inferPattern :: Pattern t -> Infer (Pattern Type, [TypeAssumption])
----inferPattern = cata $ \pat -> do
----    name <- supply
----    let t = tVar kStar name 
----    case pat of
----        PVar _ var -> 
----            pure (varPat t var, [var :>: t])
----
----        PCon _ con ps -> do
----            (trs, as) <- unzip <$> sequence ps
----            pure (conPat t con trs, concat as <> [con :>: t])
----
----        PLit _ lit -> do
----            t <- inferLiteral lit
----            pure (litPat t lit, [])
----
----        PAny _ -> 
----            pure (anyPat t, [])
----
----inferApp 
----  :: Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
----  -> Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
----  -> Infer (Expr Type p q, [TypeAssumption], [Constraint])
----inferApp expr1 expr2 = do
----    name <- supply
----    let t = tVar kStar name 
----    (t1, as1, cs1) <- expr1
----    (t2, as2, cs2) <- expr2
----    pure ( appExpr t [t1, t2]
----         , as1 <> as2
----         , cs1 <> cs2 <> [Equality (getTag t1) (getTag t2 `tArr` t)] )
----
----inferLiteral :: Literal -> Infer Type
----inferLiteral = pure . \case
----    LUnit{} -> tUnit
----    LBool{} -> tBool
----    LInt{}  -> tInt
