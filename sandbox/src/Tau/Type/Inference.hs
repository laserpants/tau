{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Inference where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM, foldl')
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Data.Set.Monad (Set, union, intersection, (\\))
import Tau.Expr
import Tau.Expr.Patterns
import Tau.Type
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Data.Set.Monad as Set

data Constraint
    = Equality Type Type
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

instance Substitutable Constraint where
    apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)

class Active a where
    active :: a -> Set Name

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active

instance Active Constraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `Set.intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

newtype Monoset = Monoset { getMonoset :: Set Name }
    deriving (Show, Eq)

instance Substitutable Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . tVar kStar =<< set)

instance Free Monoset where
    free (Monoset set) = set

monosetInsert :: Name -> Monoset -> Monoset
monosetInsert var (Monoset set) = Monoset (Set.insert var set)

monosetInsertSet :: [Name] -> Monoset -> Monoset
monosetInsertSet = flip (foldr monosetInsert)

data Assumption a = Name :>: a
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance (Substitutable t) => Substitutable (Assumption t) where
    apply = fmap . apply 

instance (Free t) => Free (Assumption t) where
    free (_ :>: t) = free t

assumptionVar :: Assumption a -> Name
assumptionVar (name :>: _) = name

--findAssumption :: Name -> [Assumption a] -> Maybe a
--findAssumption _ [] = Nothing 
--findAssumption i (name :>: a:as)
--    | i == name = Just a
--    | otherwise = findAssumption i as

removeAssumption :: Name -> [Assumption a] -> [Assumption a]
removeAssumption name = filter (\a -> name /= assumptionVar a)

removeAssumptionSet :: Set Name -> [Assumption a] -> [Assumption a]
removeAssumptionSet = flip (Set.foldr removeAssumption) 


type TypeAssumption = Assumption Type

data InferError 
    = CannotSolve
    | TypeError TypeError
    | ImplementationError
    deriving (Show, Eq)

newtype Infer a = Infer { unInfer :: ExceptT InferError (ReaderT Monoset (Supply Name)) a } 
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name
    , MonadReader Monoset 
    , MonadError InferError )

runInfer :: Infer a -> Either InferError a
runInfer = 
    unInfer
      >>> runExceptT
      >>> flip runReaderT (Monoset mempty) 
      >>> flip evalSupply (numSupply "a")
      >>> fromMaybe (throwError ImplementationError)


newtype Infer_ a = Infer_ { unInfer_ :: WriterT [Constraint] (ExceptT InferError (ReaderT Monoset (Supply Name))) a } 
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name
    , MonadReader Monoset 
    , MonadWriter [Constraint]
    , MonadError InferError )


--runInfer_ :: Infer_ a -> Either InferError (a, [Constraint])
--runInfer_ = 
--    unInfer_
--      >>> runWriterT
--      >>> runExceptT
--      >>> flip runReaderT (Monoset mempty) 
--      >>> flip evalSupply (numSupply "a")
--      >>> fromMaybe (throwError ImplementationError)


infer__ 
  :: Expr t (Pattern t) (Pattern t) 
  -> Infer ((Expr Name (Pattern Name) (Pattern Name), [Assumption Name]), [Constraint])
infer__ =
    runWriterT . infer_ 


infer_
  :: Expr t (Pattern t) (Pattern t) 
  -> WriterT [Constraint] Infer (Expr Name (Pattern Name) (Pattern Name), [Assumption Name])
infer_ = cata $ \case

    EVar _ var -> do
        tvar <- supply
        pure (varExpr tvar var, [var :>: tvar])

    ECon _ con exprs -> do
        tvar1 <- supply
        tvar2 <- supply
        (es1, as1) <- sequenced_ exprs
        tell [ Equality (tVar kStar tvar1) 
                        (foldr tArr (tVar kStar tvar2) (fromTag <$> es1)) ]
        pure (conExpr tvar2 con es1, as1 <> [con :>: tvar1])

    ELit _ lit -> do
        tvar <- supply
        t <- inferLiteral_ lit
        tell [ Equality (tVar kStar tvar) t ] 
        pure (litExpr tvar lit, [])

    EApp _ exprs ->
        foldl1 inferApp_ exprs

    ELet _ pat expr1 expr2 -> do
        tvar <- supply
        (tp, as0) <- inferPattern_ pat
        (e1, as1) <- expr1
        (e2, as2) <- expr2
        set <- ask
        tell [ Equality (tVar kStar tvar) (fromTag e2) 
             , Equality (fromPatternTag tp) (fromTag e1) ]  

        tell $ do
            v :>: t <- as2
            (w, u) <- patternVars tp
            guard (v == w)
            pure (Implicit (tVar kStar t) (tVar kStar u) set)

        pure (letExpr tvar tp e1 e2, as1 <> removeAssumptionSet (free tp) as2)

    ELam _ pat expr1 -> do
        tvar <- supply
        (tp, as0) <- inferPattern_ pat
        (e1, as1) <- local (monosetInsertSet (assumptionVar <$> as0)) expr1
        tell [ Equality (tVar kStar tvar) (fromPatternTag tp `tArr` fromTag e1) ]

        tell $ do
            v :>: t <- as1
            (w, u) <- patternVars tp
            guard (v == w)
            pure (Equality (tVar kStar t) (tVar kStar u))

        pure (lamExpr tvar tp e1, removeAssumptionSet (free tp) as1)

    EIf _ cond tr fl -> do
        tvar <- supply
        (e1, as1) <- cond
        (e2, as2) <- tr
        (e3, as3) <- fl

        tell [ Equality (tVar kStar tvar) (fromTag e2)
             , Equality (fromTag e1) tBool
             , Equality (fromTag e2) (fromTag e3) ]

        pure (ifExpr tvar e1 e2 e3, as1 <> as2 <> as3)

    EOp  _ (OAnd a b) ->
        inferLogicOp_ a b

    EOp  _ (OOr a b) -> 
        inferLogicOp_ a b

    EMat _ exs eqs -> do
        tvar <- supply
        (es1, as1) <- sequenced_ exs
        (eqs, as2) <- sequenced_ (inferClause_ <$> eqs)

        let cs3 = concat $ do
            Clause ps exs e <- eqs
            e1 <- exs
            (p, e2) <- zip ps es1
            pure [ Equality (tVar kStar tvar) (fromTag e)
                 , Equality tBool (fromTag e1)
                 , Equality (fromPatternTag p) (fromTag e2) ]

        pure (matExpr tvar es1 eqs, as1 <> as2)

fromTag :: Expr Name p q -> Type
fromTag = tVar kStar . getTag

fromPatternTag :: Pattern Name -> Type
fromPatternTag = tVar kStar . getPatternTag

sequenced_ :: [WriterT [Constraint] Infer (a, [Assumption Name])] -> WriterT [Constraint] Infer ([a], [Assumption Name])
sequenced_ = fmap (fmap concat . unzip) . sequence 

inferLogicOp_ 
  :: WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name])
inferLogicOp_ a b = do
    tvar <- supply
    (e1, as1) <- a
    (e2, as2) <- b

    tell [ Equality (tVar kStar tvar) tBool 
         , Equality (fromTag e1) tBool
         , Equality (fromTag e2) tBool ]

    pure (andOp tvar e1 e2, as1 <> as2)

inferClause_
  :: Clause (Pattern t) (WriterT [Constraint] Infer (Expr Name (Pattern Name) q, [Assumption Name])) 
  -> WriterT [Constraint] Infer (Clause (Pattern Name) (Expr Name (Pattern Name) q), [Assumption Name])
inferClause_ eq@(Clause ps _ _) = do
    (tps, as0) <- fmap concat . unzip <$> traverse inferPattern_ ps
    let Clause _ exs e = local (monosetInsertSet (assumptionVar <$> as0)) <$> eq
    (es1, as1) <- sequenced_ exs
    (exp, as2) <- e 

    tell $ do
        v :>: t <- as1 <> as2
        (w, u) <- patternVars =<< tps
        guard (v == w)
        pure (Equality (tVar kStar t) (tVar kStar u))

    pure (Clause tps es1 exp, as0 <> removeAssumptionSet (free tps) (as1 <> as2))

inferPattern_ :: Pattern t -> WriterT [Constraint] Infer (Pattern Name, [Assumption Name])
inferPattern_ = cata $ \pat -> do
    tvar <- supply
    case pat of
        PVar _ var -> 
            pure (varPat tvar var, [var :>: tvar])

        PCon _ con ps -> do
            (trs, as) <- unzip <$> sequence ps
            pure (conPat tvar con trs, concat as <> [con :>: tvar])

        PLit _ lit -> do
            t <- inferLiteral_ lit
            pure (litPat tvar lit, [])

        PAny _ -> 
            pure (anyPat tvar, [])

inferApp_
  :: WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name]) 
  -> WriterT [Constraint] Infer (Expr Name p q, [Assumption Name])
inferApp_ expr1 expr2 = do
    tvar <- supply
    (e1, as1) <- expr1
    (e2, as2) <- expr2

    tell [ Equality (fromTag e1) (fromTag e2 `tArr` tVar kStar tvar) ]

    pure (appExpr tvar [e1, e2], as1 <> as2)

inferLiteral_ :: Literal -> WriterT [Constraint] Infer Type
inferLiteral_ = pure . \case
    LUnit{} -> tUnit
    LBool{} -> tBool
    LInt{}  -> tInt


-- ***********
-- ***********
-- ***********
-- ***********
-- ***********


infer 
  :: Expr t (Pattern t) (Pattern t) 
  -> Infer (Expr Type (Pattern Type) (Pattern Type), [TypeAssumption], [Constraint])
infer = cata $ \case
    EVar _ var -> do
        name <- supply
        let t = tVar kStar name 
        pure (varExpr t var, [var :>: t], [])

    ECon _ con exprs -> do
        name <- supply
        let t = tVar kStar name 
        (es1, as1, cs1) <- sequenced exprs
        pure ( conExpr t con es1
             , as1 <> [con :>: foldr tArr t (getTag <$> es1)]
             , cs1 )

    ELit _ lit -> do
        t <- inferLiteral lit
        pure (litExpr t lit, [], [])

    EApp _ exprs ->
        foldl1 inferApp exprs

    ELet _ pat expr1 expr2 -> do
        (tp, as0) <- inferPattern pat
        (e1, as1, cs1) <- expr1
        (e2, as2, cs2) <- expr2
        set <- ask
        let cs3 = [Implicit t u set | v :>: t <- as2, (w, u) <- patternVars tp, v == w]
        pure ( letExpr (getTag e2) tp e1 e2
             , as1 <> removeAssumptionSet (free tp) as2
             , cs1 <> cs2 <> [Equality (getPatternTag tp) (getTag e1)] <> cs3 )

    ELam _ pat expr1 -> do
        (tp, as0) <- inferPattern pat
        (e1, as1, cs1) <- local (monosetInsertSet (assumptionVar <$> as0)) expr1
        let cs2 = [Equality t u | v :>: t <- as1, (w, u) <- patternVars tp, v == w]
        pure ( lamExpr (getPatternTag tp `tArr` getTag e1) tp e1
             , removeAssumptionSet (free tp) as1
             , cs1 <> cs2 )

    EIf _ cond tr fl -> do
        (e1, as1, cs1) <- cond
        (e2, as2, cs2) <- tr
        (e3, as3, cs3) <- fl
        pure ( ifExpr (getTag e2) e1 e2 e3
             , as1 <> as2 <> as3
             , cs1 <> cs2 <> cs3 <> [Equality (getTag e1) tBool, Equality (getTag e2) (getTag e3)])

    EOp  _ (OEq a b) -> do
        (e1, as1, cs1) <- a
        (e2, as2, cs2) <- b
        pure ( eqOp tBool e1 e2
             , as1 <> as2
             , cs1 <> cs2 )

    EOp  _ (OAnd a b) -> do
        (e1, as1, cs1) <- a
        (e2, as2, cs2) <- b
        pure ( andOp tBool e1 e2
             , as1 <> as2
             , cs1 <> cs2 )

    EOp  _ (OOr a b) -> do
        (e1, as1, cs1) <- a
        (e2, as2, cs2) <- b
        pure ( orOp tBool e1 e2
             , as1 <> as2
             , cs1 <> cs2 )

    EMat _ exs eqs -> do
        name <- supply
        let t = tVar kStar name 
        (es1, as1, cs1) <- sequenced exs
        (eqs, as2, cs2) <- sequenced (inferClause <$> eqs)

        let cs3 = concat $ do
            Clause ps exs e <- eqs
            e1 <- exs
            (p, e2) <- zip ps es1
            pure [ Equality t (getTag e)
                 , Equality tBool (getTag e1)
                 , Equality (getPatternTag p) (getTag e2) ]

        pure ( matExpr t es1 eqs
             , as1 <> as2
             , cs1 <> cs2 <> cs3 )

inferClause 
  :: Clause (Pattern t) (Infer (Expr Type (Pattern Type) q, [Assumption Type], [Constraint])) 
  -> Infer (Clause (Pattern Type) (Expr Type (Pattern Type) q), [TypeAssumption], [Constraint])
inferClause eq@(Clause ps _ _) = do
    (tps, as0) <- fmap concat . unzip <$> traverse inferPattern ps

    let Clause _ exs e = local (monosetInsertSet (assumptionVar <$> as0)) <$> eq
    (es1, as1, cs1) <- sequenced exs
    (exp, as2, cs2) <- e 
    let cs3 = [Equality t u | v :>: t <- as1 <> as2, (w, u) <- patternVars =<< tps, v == w]

    pure ( Clause tps es1 exp
         , as0 <> removeAssumptionSet (free tps) (as1 <> as2)
         , cs1 <> cs2 <> cs3 )

sequenced :: [Infer (a, [TypeAssumption], [Constraint])] -> Infer ([a], [TypeAssumption], [Constraint])
sequenced = fmap (go . unzip3) . sequence where
    go (a, as, cs) = (a, concat as, concat cs)

inferPattern :: Pattern t -> Infer (Pattern Type, [TypeAssumption])
inferPattern = cata $ \pat -> do
    name <- supply
    let t = tVar kStar name 
    case pat of
        PVar _ var -> 
            pure (varPat t var, [var :>: t])

        PCon _ con ps -> do
            (trs, as) <- unzip <$> sequence ps
            pure (conPat t con trs, concat as <> [con :>: t])

        PLit _ lit -> do
            t <- inferLiteral lit
            pure (litPat t lit, [])

        PAny _ -> 
            pure (anyPat t, [])

inferApp 
  :: Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> Infer (Expr Type p q, [TypeAssumption], [Constraint])
inferApp expr1 expr2 = do
    name <- supply
    let t = tVar kStar name 
    (t1, as1, cs1) <- expr1
    (t2, as2, cs2) <- expr2
    pure ( appExpr t [t1, t2]
         , as1 <> as2
         , cs1 <> cs2 <> [Equality (getTag t1) (getTag t2 `tArr` t)] )

inferLiteral :: Literal -> Infer Type
inferLiteral = pure . \case
    LUnit{} -> tUnit
    LBool{} -> tBool
    LInt{}  -> tInt
