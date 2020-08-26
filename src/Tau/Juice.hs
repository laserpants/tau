{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
module Tau.Juice where

import Control.Arrow ((>>>))
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Eq.Deriving
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.Functor.Const (Const(..))
import Data.Functor.Foldable
import Data.List (intersperse, find, delete, nub, elemIndex)
import Data.Map.Strict (Map, notMember, (!?))
import Data.Maybe (fromMaybe, fromJust)
import Data.Set.Monad (Set, union, intersection, member, (\\))
import Data.Text (Text, pack, unpack)
import Data.Tuple (swap)
import Data.Tuple.Extra (first3)
import Debug.Trace
import GHC.Show (showSpace)
import Test.Hspec
import Text.Show.Deriving
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Data.Either

-- ==============
-- ==== Util ====
-- ==============

type Name = Text

(|>) = (&)
($>) = (&)

infixl 1 |>
infixl 0 $>

data (f :*: g) a = (:*:)
    { left  :: f a
    , right :: g a }
  deriving
    ( Eq
    , Show
    , Functor
    , Foldable
    , Traversable )

type Algebra f a = f a -> a

$(deriveShow1 ''(:*:))
$(deriveEq1   ''(:*:))

-- ==============
-- ==== Type ====
-- ==============

-- | Type to represent types
data Type
    = TCon Name            -- ^ Type constructor
    | TVar Name            -- ^ Type variable
    | TArr Type Type       -- ^ Functions type
    | TApp Type Type       -- ^ Type application
    deriving (Show, Eq, Ord)

-- | Type class constraint
data Class = Class Name Type
    deriving (Show, Eq)

-- | Polymorphic type
data Scheme = Forall [Name] [Class] Type
    deriving (Show, Eq)

data Kind
    = Arrow Kind Kind      -- ^ Type arrow
    | Star                 -- ^ Concrete type
    deriving (Show, Eq)

-- | Type context
newtype Context = Context (Map Name Scheme)
    deriving (Show, Eq)

tInt     = TCon "Int"      -- ^ Int
tInteger = TCon "Integer"  -- ^ Integer
tBool    = TCon "Bool"     -- ^ Bool
tFloat   = TCon "Float"    -- ^ Float
tString  = TCon "String"   -- ^ String
tChar    = TCon "Char"     -- ^ Char
tUnit    = TCon "Unit"     -- ^ Unit
tVoid    = TCon "Void"     -- ^ Void

-- ===========================
-- ==== Type.Substitution ====
-- ===========================

newtype Substitution = Substitution { runSubstitution :: Map Name Type }
    deriving (Show, Eq)

compose :: Substitution -> Substitution -> Substitution
compose sub@(Substitution map1) (Substitution map2) =
    Substitution (Map.union (Map.map (apply sub) map2) map1)

substitute :: Name -> Type -> Substitution
substitute name ty = Substitution (Map.singleton name ty)

instance Semigroup Substitution where
    (<>) = compose

instance Monoid Substitution where
    mempty = Substitution mempty

class Substitutable a where
    apply :: Substitution -> a -> a

instance (Substitutable a) => Substitutable [a] where
    apply = fmap . apply

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
    apply sub pair = (apply sub (fst pair), apply sub (snd pair))

instance Substitutable Type where
    apply sub (TVar var)   = Map.findWithDefault (TVar var) var (runSubstitution sub)
    apply sub (TArr t1 t2) = TArr (apply sub t1) (apply sub t2)
    apply sub (TApp t1 t2) = TApp (apply sub t1) (apply sub t2)
    apply _ ty = ty

instance Substitutable Class where
    apply sub (Class name ty) = Class name (apply sub ty)

instance Substitutable Scheme where
    apply (Substitution map) (Forall vars clcs ty) =
        Forall vars (apply sub clcs) (apply sub ty)
      where
        sub = Substitution (foldr Map.delete map vars)

-- | Class of types that support the notion of free type variables
class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (union . free) mempty

instance Free Type where
    free (TVar var)   = Set.singleton var
    free (TArr t1 t2) = free t1 `union` free t2
    free (TApp t1 t2) = free t1 `union` free t2
    free _            = mempty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance Free Context where
    free (Context env) = free (Map.elems env)

-- =============
-- ==== Ast ====
-- =============

-- | Language primitives
data Prim
    = Unit                   -- ^ Unit value
    | Bool Bool              -- ^ Boolean
    | Int Int                -- ^ Machine-level integers (32 or 64 bit)
    | Integer Integer        -- ^ Arbitrary precision integer
    | Float Double           -- ^ Floating point number
    | Char Char              -- ^ Char
    | String Text            -- ^ String
    deriving (Show, Eq)

data PatternF a
    = VarP Name              -- ^ Variable pattern
    | ConP Name [a]          -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Pattern = Fix PatternF

getVars :: Pattern -> [Name]
getVars = cata alg where
    alg :: Algebra PatternF [Name]
    alg (VarP v)    = [v]
    alg (ConP _ ps) = concat ps
    alg _           = []

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)

-- | Source language expression tree
data ExprF a
    = VarS Name
    | LamS Name a
    | AppS [a]
    | LitS Prim
    | LetS Name a a
    | IfS a a a
    | CaseS a [(Pattern, a)]
    | OpS (OpF a)
    | AnnS a Type
    | Err
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Expr = Fix ExprF

-- | Operators
data OpF a
    = AddS a a
    | SubS a a
    | MulS a a
    | EqS a a
    | LtS a a
    | GtS a a
    | NegS a
    | NotS a
    deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)

$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)

-- \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
-- \\\\\\\\\\\\\\\\\\\\\\\\\\\\ Smart constructors \\\\\\\\\\\\\\\\\\\\\\\\\\\\
-- \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

-- | VarS constructor
varS :: Name -> Expr
varS = Fix . VarS

-- | LamS constructor
lamS :: Name -> Expr -> Expr
lamS a = Fix . LamS a

-- | AppS constructor
appS :: [Expr] -> Expr
appS = Fix . AppS

-- | LitS constructor
litS :: Prim -> Expr
litS = Fix . LitS

-- | LetS constructor
letS :: Name -> Expr -> Expr -> Expr
letS a1 a2 = Fix . LetS a1 a2

-- | IfS constructor
ifS :: Expr -> Expr -> Expr -> Expr
ifS a1 a2 a3 = Fix (IfS a1 a2 a3)

-- | CaseS constructor
caseS :: Expr -> [(Pattern, Expr)] -> Expr
caseS a = Fix . CaseS a

-- | OpS constructor
opS :: OpF Expr -> Expr
opS = Fix . OpS

-- annS = TODO

errS :: Expr
errS = Fix Err

-- | AddS constructor
addS :: Expr -> Expr -> Expr
addS a1 a2 = opS (AddS a1 a2)

-- | SubS constructor
subS :: Expr -> Expr -> Expr
subS a1 a2 = opS (SubS a1 a2)

-- | MulS constructor
mulS :: Expr -> Expr -> Expr
mulS a1 a2 = opS (MulS a1 a2)

-- | EqS constructor
eqS :: Expr -> Expr -> Expr
eqS a1 a2 = opS (EqS a1 a2)

-- | LtS constructor
ltS :: Expr -> Expr -> Expr
ltS a1 a2 = opS (LtS a1 a2)

-- | GtS constructor
gtS :: Expr -> Expr -> Expr
gtS a1 a2 = opS (GtS a1 a2)

-- | NegS constructor
negS :: Expr -> Expr
negS a = opS (NegS a)

-- | NotS constructor
notS :: Expr -> Expr
notS a = opS (NotS a)

litUnit :: Expr
litUnit = litS Unit

litBool :: Bool -> Expr
litBool = litS . Bool

litInt :: Int -> Expr
litInt = litS . Int

litInteger :: Integer -> Expr
litInteger = litS . Integer

litFloat :: Double -> Expr
litFloat = litS . Float

litChar :: Char -> Expr
litChar = litS . Char

litString :: Text -> Expr
litString = litS . String

-- VarP constructor
varP :: Name -> Pattern
varP = Fix . VarP

-- ConP constructor
conP :: Name -> [Pattern] -> Pattern
conP a = Fix . ConP a

-- LitP constructor
litP :: Prim -> Pattern
litP = Fix . LitP

-- AnyP constructor
anyP :: Pattern
anyP = Fix AnyP

-- ========================
-- ==== Type.Inference ====
-- ========================

data TypeError
    = CannotSolve
    | CannotUnify
    | InfiniteType
    | UnboundVariable Name
    | EmptyCaseStatement
    | ImplementationError
    deriving (Show, Eq)

instance (Monad m) => MonadFail (InferT m) where
    fail = const (throwError ImplementationError)

instance MonadTrans InferT where
    lift = InferT . lift . lift . lift

type InferTStack m a = ReaderT Monoset (ExceptT TypeError (SupplyT Type m)) a

newtype InferT m a = InferT (InferTStack m a) deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader Monoset
    , MonadSupply Type
    , MonadError TypeError )

freshVars :: [Type]
freshVars = TVar . pfxed <$> [1..] where
    pfxed count = "a" <> pack (show count)

runInferT :: (Monad m) => InferT m a -> m (Either TypeError a)
runInferT (InferT a) =
    freshVars
        $> Monoset mempty
        |> runReaderT a
        |> runExceptT
        |> evalSupplyT

type Infer a = InferT Identity a

runInfer :: Infer a -> Either TypeError a
runInfer = runIdentity . runInferT

-- | Monomorphic set
newtype Monoset = Monoset (Set Name)
    deriving (Show, Eq)

insertIntoMonoset :: Name -> Monoset -> Monoset
insertIntoMonoset var (Monoset set) = Monoset (Set.insert var set)

insertManyIntoMonoset :: [Name] -> Monoset -> Monoset
insertManyIntoMonoset = flip (foldr insertIntoMonoset)

instance Free Monoset where
    free (Monoset set) = set

instance Substitutable Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . TVar =<< set)

type AnnotatedExprF a = Const a :*: ExprF

-- | Type-annotated syntax tree
newtype AnnotatedExpr a = AnnotatedExpr
    { runAnnotatedExpr :: Fix (AnnotatedExprF a) }
    deriving (Eq, Show)

instance Substitutable (AnnotatedExpr Type) where
    apply sub = runAnnotatedExpr >>> cata alg >>> AnnotatedExpr where
        alg (Const ty :*: expr) = Fix (Const (apply sub ty) :*: expr)

infer
  :: (Monad m)
  => Expr
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
infer = cata alg where
    alg :: (Monad m)
        => Algebra ExprF (InferT m (AnnotatedExpr Type, [Assumption], [Constraint]))
    alg = fmap expand >>> \case
        VarS name -> do
            beta <- supply
            pure ( annotated beta (VarS name)
                 , [Assumption (name, beta)]
                 , [] )

        LamS name expr -> do
            beta@(TVar var) <- supply
            (_expr, t1, a1, c1) <- local (insertIntoMonoset var) expr
            pure ( annotated (TArr beta t1) (LamS name _expr)
                 , removeAssumption name a1
                 , c1 <> [Equality t beta [] | (y, t) <- runAssumption <$> a1, name == y] )

        AppS exprs -> do
            (_expr, _, as, cs) <- foldl1 inferApp exprs
            pure ( AnnotatedExpr _expr, as, cs )

        LitS prim -> do
            t <- inferPrim prim
            pure ( annotated t (LitS prim), [], [] )

        LetS var expr body -> do
            (_e1, t1, a1, c1) <- expr
            (_e2, t2, a2, c2) <- body
            set <- ask
            pure ( annotated t2 (LetS var _e1 _e2)
                 {-, removeAssumption var a1 <> removeAssumption var a2 -}
                 , a1 <> removeAssumption var a2
                 , c1 <> c2 <> [Implicit t t1 set | (y, t) <- runAssumption <$> a1 <> a2, var == y] )

        IfS cond true false -> do
            (_cond, t1, a1, c1) <- cond
            (_true, t2, a2, c2) <- true
            (_false, t3, a3, c3) <- false
            pure ( annotated t2 (IfS _cond _true _false)
                 , a1 <> a2 <> a3
                 , c1 <> c2 <> c3 <> [Equality t1 tBool [], Equality t2 t3 []] )

        CaseS _ [] ->
            throwError EmptyCaseStatement

        CaseS expr clss -> do
            beta <- supply
            (_expr, t1, a1, c1) <- expr
            (_clss, as, cs) <- foldrM (inferClause beta t1) ([], [], []) clss
            pure ( annotated beta (CaseS _expr _clss)
                 , a1 <> as
                 , c1 <> cs )

        OpS op ->
            inferOp op

        AnnS expr ty ->
            undefined  -- TODO

type Clause = (Pattern, Fix (AnnotatedExprF Type))

inferClause
  :: (Monad m)
  => Type
  -> Type
  -> (Pattern, InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint]))
  -> ([Clause], [Assumption], [Constraint])
  -> InferT m ([Clause], [Assumption], [Constraint])
inferClause beta t (pttrn, expr) (ps, as, cs) = do
    (_expr, t1, a1, c1) <- local (insertManyIntoMonoset vars) expr
    (t2, a2, c2) <- inferPattern pttrn
    pure ( (pttrn, _expr):ps
         , as <> removeManyAssumptions vars a1
              <> removeManyAssumptions vars a2
         , cs <> c1 <> c2
              <> [Equality beta t1 [], Equality t t2 []]
              <> constraints a1 a2 )
  where
    vars = getVars pttrn
    constraints a1 a2 = do
        (y1, t1) <- runAssumption <$> a1
        (y2, t2) <- runAssumption <$> a2
        var <- vars
        guard (var == y1 && var == y2)
        pure (Equality t1 t2 [])

inferPattern :: (Monad m) => Pattern -> InferT m (Type, [Assumption], [Constraint])
inferPattern = cata $ \case
    VarP var -> do
        beta <- supply
        pure (beta, [Assumption (var, beta)], [])

    ConP name ps -> do
        beta <- supply
        (ts, ass, css) <- (fmap unzip3 . sequence) ps
        pure ( beta
             , concat ass <> [Assumption (name, foldr TArr beta ts)]
             , concat css )

    LitP prim -> do
        t <- inferPrim prim
        pure (t, [], [])

    AnyP -> do
        beta <- supply
        pure (beta, [], [])

inferApp
  :: (Monad m)
  => InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
inferApp fun arg = do
    (_e1, t1, a1, c1) <- fun
    (_e2, t2, a2, c2) <- arg
    beta <- supply
    pure ( Fix (Const beta :*: AppS [_e1, _e2])
         , beta
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (TArr t2 beta) []] )

inferOp
  :: (Monad m)
  => OpF (InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint]))
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
inferOp = \case
    AddS e1 e2 -> binOp AddS e1 e2 tInt tInt
    SubS e1 e2 -> binOp SubS e1 e2 tInt tInt
    MulS e1 e2 -> binOp MulS e1 e2 tInt tInt
    LtS e1 e2 -> binOp LtS e1 e2 tInt tBool
    GtS e1 e2 -> binOp GtS e1 e2 tInt tBool
    NegS e -> unOp NegS e tInt
    NotS e -> unOp NotS e tBool
    EqS e1 e2 -> do
        (_e1, t1, a1, c1) <- e1
        (_e2, t2, a2, c2) <- e2
        beta <- supply
        pure ( annotated beta (OpS (EqS _e1 _e2))
             , a1 <> a2
             , c1 <> c2 <> [Equality t1 t2 [], Equality beta tBool []] )

unOp
  :: (Monad m)
  => (Fix (AnnotatedExprF Type) -> OpF (Fix (AnnotatedExprF Type)))
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> Type
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
unOp op expr t = do
    (_e1, t1, a1, c1) <- expr
    beta <- supply
    pure ( annotated beta (OpS (op _e1))
         , a1
         , c1 <> [Equality (TArr t1 beta) (TArr t t) []] )

binOp
  :: (Monad m)
  => (Fix (AnnotatedExprF Type) -> Fix (AnnotatedExprF Type) -> OpF (Fix (AnnotatedExprF Type)))
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> Type
  -> Type
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
binOp op e1 e2 ta tb = do
    (_e1, t1, a1, c1) <- e1
    (_e2, t2, a2, c2) <- e2
    beta <- supply
    pure ( annotated beta (OpS (op _e1 _e2))
         , a1 <> a2
         , c1 <> c2 <> [Equality (TArr t1 (TArr t2 beta)) (TArr ta (TArr ta tb)) []] )

inferPrim :: (Monad m) => Prim -> InferT m Type
inferPrim = pure . \case
    Unit      -> tUnit
    Bool{}    -> tBool
    Int{}     -> tInt
    Integer{} -> tInteger
    Float{}   -> tFloat
    Char{}    -> tChar
    String{}  -> tString

inferType :: (Monad m) => Context -> Expr -> InferT m (AnnotatedExpr Scheme)
inferType (Context env) expr = do
    (ty, as, cs) <- infer expr
    case unboundVars env as of
        [] -> do
            sub <- solve $ cs <> do
                (x, s) <- runAssumption <$> as
                (y, t) <- Map.toList env
                guard (x == y)
                pure (Explicit s t)

            annotate sub ty

        (var:_) ->
            throwError (UnboundVariable var)
  where
    annotate
      :: (Monad m)
      => Map Name Signature
      -> AnnotatedExpr Type
      -> InferT m (AnnotatedExpr Scheme)
    annotate map = cata alg . runAnnotatedExpr
      where
        alg
          :: (Monad m)
          => Algebra (AnnotatedExprF Type) (InferT m (AnnotatedExpr Scheme))
        alg (Const ty :*: expr) =
            forall (applySigMap map [] ty) . fmap runAnnotatedExpr <$> sequence expr
        forall (clcs, ty) =
            let cod = enumFrom 1 >>= fmap (TVar . pack) . flip replicateM ['a'..'z']
                dom = nub $ Set.toList $ free ty
                sub = Substitution $ Map.fromList (dom `zip` cod)
             in annotated $ generalize mempty (apply sub clcs) (apply sub ty)

unboundVars :: Map Name a -> [Assumption] -> [Name]
unboundVars env as = filter (`notMember` env) (fst . runAssumption <$> as)

annotated :: t -> ExprF (Fix (AnnotatedExprF t)) -> AnnotatedExpr t
annotated t a = AnnotatedExpr $ Fix $ Const t :*: a

expand
  :: (Monad m)
  => m (AnnotatedExpr Type, [Assumption], [Constraint])
  -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
expand triple = do
    (e, as, cs) <- first3 runAnnotatedExpr <$> triple
    let Const t :*: _ = unfix e
    pure (e, t, as, cs)

{-# ANN inferOp ("HLint: ignore Reduce duplication" :: Text) #-}

-- =====================
-- ==== Type.Solver ====
-- =====================

newtype Assumption = Assumption { runAssumption :: (Name, Type) }
    deriving (Show, Eq)

removeAssumption :: Name -> [Assumption] -> [Assumption]
removeAssumption var = filter fun where fun (Assumption a) = fst a /= var

removeManyAssumptions :: [Name] -> [Assumption] -> [Assumption]
removeManyAssumptions = flip (foldr removeAssumption)

data Constraint
    = Equality Type Type [Class]
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

instance Substitutable Constraint where
    apply sub (Equality t1 t2 clcs) = Equality (apply sub t1) (apply sub t2) (apply sub clcs)
    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)

class Active a where
    active :: a -> Set Name

instance Active Constraint where
    active (Equality t1 t2 _)    = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active

isSolvable :: [Constraint] -> Constraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset vars)) =
    Set.null (free t2 \\ vars `intersection` active cs)
isSolvable _ _ = True

choice :: [Constraint] -> Maybe ([Constraint], Constraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

type Signature = ([Class], Type)

combine :: (Type -> Type -> Type) -> Signature -> Signature -> Signature
combine con (clcs1, t1) (clcs2, t2) = (nub (clcs1 <> clcs2), con t1 t2)

applySigMap :: Map Name Signature -> [Class] -> Type -> Signature
applySigMap map clcs = fun where
    fun ty@(TVar var) = Map.findWithDefault (clcs, ty) var map
    fun (TArr t1 t2)  = combine TArr (fun t1) (fun t2)
    fun (TApp t1 t2)  = combine TApp (fun t1) (fun t2)
    fun ty            = (clcs, ty)

composeMaps :: [Class] -> Map Name Signature -> Substitution -> Map Name Signature
composeMaps clcs map1 (Substitution map2) =
    Map.union (Map.map (applySigMap map1 clcs) map2) map1

solve
  :: (MonadError TypeError m, MonadSupply Type m)
  => [Constraint]
  -> m (Map Name Signature)
solve [] = pure mempty
solve xs = maybe (throwError CannotSolve) pure (choice xs) >>= uncurry run
  where
    run cs = \case
        Equality t1 t2 clcs -> do
            sub1 <- unify t1 t2
            sub2 <- solve (apply sub1 cs)
            pure (composeMaps clcs sub2 sub1)

        Implicit t1 t2 (Monoset vars) ->
            solve (Explicit t1 (generalize vars [] t2):cs)

        Explicit t1 scheme -> do
            (clcs, t2) <- instantiate scheme
            solve (Equality t1 t2 clcs:cs)

generalize :: Set Name -> [Class] -> Type -> Scheme
generalize vars clcs ty = Forall (Set.toList (free ty \\ vars)) clcs ty

instantiate :: (MonadSupply Type m) => Scheme -> m Signature
instantiate (Forall vars clcs ty) = do
    vars' <- traverse (const supply) vars
    let map = Map.fromList (zip vars vars')
    pure $ apply (Substitution map) (clcs, ty)

-- ==========================
-- ==== Type.Unification ====
-- ==========================

occursIn :: Name -> Type -> Bool
occursIn var ty = var `member` free ty

bind :: (MonadError TypeError m) => Name -> Type -> m Substitution
bind var ty
    | TVar var == ty    = pure mempty
    | var `occursIn` ty = throwError InfiniteType
    | otherwise         = pure (substitute var ty)

unifyPair :: (MonadError TypeError m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPair (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

unify :: (MonadError TypeError m) => Type -> Type -> m Substitution
unify (TArr t1 t2) (TArr u1 u2) = unifyPair (t1, t2) (u1, u2)
unify (TApp t1 t2) (TApp u1 u2) = unifyPair (t1, t2) (u1, u2)
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify t u
    | t == u    = pure mempty
    | otherwise = throwError CannotUnify

-- ===============
-- ==== Value ====
-- ===============

-- | The environment is a mapping from variables to values.
type Env m = Map Name (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                           -- ^ Literal value
    | Data Name [Value m]                  -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(Env m)  -- ^ Function closure

instance Eq (Value m) where
    (==) (Value v) (Value w)     = v == w
    (==) (Data c vs) (Data d ws) = c == d && vs == ws
    (==) _ _                     = False

instance Show (Value m) where
    showsPrec p (Value val) =
        showParen (p >= 11)
            $ showString "Value"
            . showSpace
            . showsPrec 11 val
    showsPrec p (Data name vals) =
        showParen (p >= 11)
            $ showString "Data"
            . showSpace
            . showsPrec 11 name
            . showSpace
            . showsPrec 11 vals
    showsPrec _ Closure{} =
        showString "<<function>>"

dataCon :: (MonadReader (Env m) m) => Name -> Int -> Value m
dataCon name 0 = Data name []
dataCon name n = Closure (varName 1) val mempty
  where
    val = tail vars
        $> init
        |> foldr (\name -> asks . Closure name)

    init = do
        env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

    vars = varName <$> [1..n]
    varName n = "%" <> pack (show n)

-- ======================
-- ==== Substitution ====
-- ======================

substituteExpr :: Name -> Expr -> Expr -> Expr
substituteExpr name val = para $ \case
    VarS var
        | name == var -> val
        | otherwise   -> varS var

    LamS var (expr, body)
        | name == var -> lamS var expr
        | otherwise   -> lamS var body

    AppS exprs ->
        appS (snd <$> exprs)

    LitS prim ->
        litS prim

    LetS var body expr ->
        let get = if name == var then fst else snd
         in letS var (get body) (get expr)

    IfS cond true false ->
        ifS (snd cond) (snd true) (snd false)

    CaseS expr clss ->
        caseS (snd expr) (fun <$> clss) where
            fun (p, e) = (p, if name `elem` getVars p then fst e else snd e)

    OpS op ->
        opS (snd <$> op)

    AnnS expr ty ->
        undefined  -- TODO

-- ============================================================================
-- ============================================================================
-- ======       ===============================================================
-- ====== Tests ===============================================================
-- ======       ===============================================================
-- ============================================================================
-- ============================================================================

testExpr :: Expr
testExpr = lamS "a" (appS [varS "concat", appS [varS "show", varS "a"], litString "..."])

listA :: Type
listA = TApp (TCon "List") (TVar "a")

tuple2AB :: Type
tuple2AB = TApp (TApp (TCon "Tuple2") (TVar "a")) (TVar "b")

testContext :: Context
testContext = Context (Map.fromList
    [ ("concat" , Forall []         [] (TArr tString (TArr tString tString)))
    , ("show"   , Forall ["a"] [Class "Show" (TVar "a")]
                                       (TArr (TVar "a") tString))
    , ("Nil"    , Forall ["a"]      [] listA)
    , ("Cons"   , Forall ["a"]      [] (TArr (TVar "a") (TArr listA listA)))
    , ("const"  , Forall ["a", "b"] [] (TArr (TVar "a") (TArr (TVar "b") (TVar "a"))))
    , ("foo"    , Forall ["a"]      [] (TArr (TVar "a") (TVar "a")))
    , ("Foo"    , Forall ["a"]      [] (TArr (TVar "a") (TApp (TCon "List") (TVar "a"))))
    , ("Baz"    , Forall []         [] tBool)
    , ("Tuple2" , Forall ["a", "b"] [] (TArr (TVar "a") (TArr (TVar "b") tuple2AB)))
    , ("fst"    , Forall ["a", "b"] [] (TArr tuple2AB (TVar "a")))
    , ("snd"    , Forall ["a", "b"] [] (TArr tuple2AB (TVar "b")))
    ])

-- ===================
-- ==== TestInfer ====
-- ===================

test010 :: Expr
test010 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit])

test011 :: Expr
test011 = appS [varS "const", litInt 5, litUnit]

test012 :: Expr
test012 = appS [varS "foo", litInt 5]

test013 :: Expr
test013 = appS [varS "Foo", litInt 5]

test014 :: Expr
test014 = lamS "a" (varS "a")

test015 :: Expr
test015 = lamS "a" (lamS "b" (varS "a"))

test020 :: Expr
test020 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5])

test030 :: Expr
test030 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses =
        [ (conP "Cons" [varP "y", varP "ys"], litInt 1)
        , (conP "Nil" [], litInt 2) ]

-- \xs -> case xs of { _ => 1 } Cons 5 Nil
test031 :: Expr
test031 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (anyP, litInt 1) ]

-- \xs -> case xs of { x => 1 } Cons 5 Nil
test032 :: Expr
test032 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (varP "x", litInt 1) ]

-- \xs -> case xs of { Cons y ys => 1 } Cons 5 Nil
test033 :: Expr
test033 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (conP "Cons" [varP "y", varP "ys"], litInt 1) ]

test034 :: Expr
test034 = letS "xs" (appS [varS "Baz"]) (caseS (varS "xs") [ (conP "Baz" [], litString "hello")])

test040 :: Expr
test040 = appS [lamS "xs" (caseS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]]

test041 :: Expr
test041 = appS [varS "Cons", litInt 5]

test042 :: Expr
test042 = appS [varS "Cons", litInt 5, appS [varS "Nil"]]

test043 :: Expr
test043 = appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]

test044 :: Expr
test044 = appS [varS "Cons", litInt 5, appS [varS "Cons", litBool True, appS [varS "Nil"]]]

-- case Cons 5 Nil of { Cons y ys -> y + 1; Nil -> 0 })
test050 :: Expr
test050 = caseS (appS [varS "Cons", litInt 5, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Nil" [], litInt 0)]

-- case Cons "a" Nil of { Cons y ys -> y + 1 })
test053 :: Expr
test053 = caseS (appS [varS "Cons", litString "a", appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

-- case Cons 6 Nil of { Cons y ys -> y + 1 })
test054 :: Expr
test054 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

test055 :: Expr
test055 = letS "xs" (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (letS "ys" (appS [varS "Cons", litInt 1, appS [varS "Nil"]]) (litInt 5))

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> 5 })
test056 :: Expr
test056 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Cons" [litP (Int 4), varP "ys"], litInt 5)]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> "foo" })
test057 :: Expr
test057 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (Int 4), varP "ys"], litString "foo") ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; 5 -> 1 })
test058 :: Expr
test058 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (litP (Int 5), litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons "w" z -> 1 })
test059 :: Expr
test059 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (String "w"), varP "z"], litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons z 5 -> 1 })
test060 :: Expr
test060 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [varP "z", litP (Int 5)], litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> "one"; _ -> "two" })
test061 :: Expr
test061 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], litString "one")
    , (anyP, litString "two") ]

-- case Cons 6 Nil of { Cons y ys -> y; _ -> "two" })
test062 :: Expr
test062 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], varS "y")
    , (anyP, litString "two") ]

-- case Nil of {}
test063 :: Expr
test063 = caseS (appS [varS "Nil"]) []

-- if 1 == True then 1 else 0
test070 :: Expr
test070 = ifS (eqS (litInt 1) (litBool True)) (litInt 1) (litInt 0)

-- if Cons True Nil == Cons 1 Nil then 1 else 0
test075 :: Expr
test075 = ifS (eqS (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (appS [varS "Cons", litInt 1, appS [varS "Nil"]])) (litInt 1) (litInt 0)

test080 :: Expr
test080 = letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]])))

-- let id = \x -> x in let x = (id, 4) in (fst x) (snd x) + 1
test090 :: Expr
test090 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1)))

test100 :: Expr
test100 = letS "x" (varS "x") (varS "x")

testInfer :: SpecWith ()
testInfer = do
    testSuccess
        (test010, Context mempty)
        (Forall ["a"] [] (TVar "a" `TArr` tUnit))
        "test010"

    testFailure
        (test010, Context mempty)
        (Forall ["a"] [] (TVar "a" `TArr` tInt))
        "test010"

    testSuccess
        (test011, testContext) (Forall [] [] tInt) "test011"

    testFailure
        (test011, testContext) (Forall [] [] tBool) "test011"

    testSuccess
        (test012, testContext) (Forall [] [] tInt) "test012"

    testSuccess
        (test013, testContext) (Forall [] [] (TApp (TCon "List") tInt)) "test013"

--    testFailure
--        (test013, testContext) (TApp (TCon "List") (TVar "a")) "test013"

--    testSuccess
--        (test014, Context mempty) (TVar "a" `TArr` TVar "a") "test014"

--    testSuccess
--        (test015, Context mempty) (TVar "a" `TArr` (TVar "b" `TArr` TVar "a")) "test015"
--
--    testFailure
--        (test015, Context mempty) (TVar "a" `TArr` (TVar "b" `TArr` TVar "b")) "test015"
--
--    testFailure
--        (test015, Context mempty) (TVar "b" `TArr` (TVar "b" `TArr` TVar "a")) "test015"

    testSuccess
        (test020, testContext) (Forall [] [] tUnit) "test020"

    testSuccess
        (test030, testContext) (Forall [] [] tInt) "test030"

    testSuccess
        (test031, testContext) (Forall [] [] tInt) "test031"

    testSuccess
        (test032, testContext) (Forall [] [] tInt) "test032"

    testSuccess
        (test033, testContext) (Forall [] [] tInt) "test033"

    testSuccess
        (test034, testContext) (Forall [] [] tString) "test034"

    testFailWithError
        (test053, testContext) CannotUnify "test053"

    testSuccess
        (test054, testContext) (Forall [] [] tInt) "test054"

    testSuccess
        (test055, testContext) (Forall [] [] tInt) "test055"

    testSuccess
        (test056, testContext) (Forall [] [] tInt) "test056"

    testFailWithError
        (test057, testContext) CannotUnify "test057"

    testFailWithError
        (test058, testContext) CannotUnify "test058"

    testFailWithError
        (test059, testContext) CannotUnify "test059"

    testFailWithError
        (test060, testContext) CannotUnify "test060"

    testSuccess
        (test061, testContext) (Forall [] [] tString) "test061"

    testFailWithError
        (test062, testContext) CannotUnify "test062"

    testFailWithError
        (test063, testContext) EmptyCaseStatement "test063"

    testFailWithError
        (test070, testContext) CannotUnify "test070"

    testFailWithError
        (test075, testContext) CannotUnify "test075"

    testSuccess
        (test080, testContext) (Forall [] [] tInt) "test080"

    testSuccess
        (test090, testContext) (Forall [] [] tInt) "test090"

    testFailWithError
        (test100, testContext) (UnboundVariable "x") "test100"

testSuccess :: (Expr, Context) -> Scheme -> Text -> SpecWith ()
testSuccess (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = unpack $
        "✔ has type : "
            <> prettyScheme ty

    describeFailure = unpack $
        "Expected type to be identical to : "
            <> prettyScheme ty
            <> " (up to isomorphism)"

    test = case runTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            pass

        _ ->
            expectationFailure describeFailure

testFailure :: (Expr, Context) -> Scheme -> Text -> SpecWith ()
testFailure (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = unpack $
        "✗ does not have type : "
            <> prettyScheme ty

    describeFailure = unpack $
        "Expected type NOT to be identical to : "
            <> prettyScheme ty

    test = case runTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            expectationFailure describeFailure

        _ ->
            pass

testFailWithError :: (Expr, Context) -> TypeError -> Text -> SpecWith ()
testFailWithError (expr, context) err name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> prettyExpr expr

    describeSuccess = "✗ fails with error " <> show err

    test = case runTest context expr of
        Left e | err == e ->
            pass

        _ ->
            expectationFailure ("Expected test to fail with error " <> show err)

runTest :: Context -> Expr -> Either TypeError Scheme
runTest context expr =
    getConst . left . unfix . runAnnotatedExpr <$> errorOrTypedExpr
  where
    errorOrTypedExpr = runInfer (inferType context expr)

-- =========================
-- ==== Pretty printing ====
-- =========================

pass :: Expectation
pass = pure ()

data TypeRep
    = ConRep Name
    | VarRep Int
    | ArrRep TypeRep TypeRep
    | AppRep TypeRep TypeRep
  deriving (Show, Eq)

canonical :: Scheme -> Scheme
canonical scheme = apply sub scheme
  where
    cod = enumFrom 1 >>= fmap (TVar . pack) . flip replicateM ['a'..'z']
    dom = nub $ Set.toList $ free scheme
    sub = Substitution $ Map.fromList (dom `zip` cod)

isoTypes :: Scheme -> Scheme -> Bool
isoTypes t u = canonical t == canonical u

prettyScheme :: Scheme -> Text
prettyScheme (Forall vars clcs ty) =
    quantifiedVars <> constraints <> prettyType ty
  where
    quantifiedVars
        | null vars = ""
        | otherwise = "forall " <> Text.concat (intersperse " " vars) <> ". "
    constraints
        | null clcs = ""
        | otherwise = Text.concat (intersperse ", " $ prettyClcs <$> clcs) <> " => "

prettyClcs :: Class -> Text
prettyClcs (Class name ty) = name <> " " <> prettyType ty

prettyType :: Type -> Text
prettyType = \case
    TCon name  -> name
    TVar name  -> name
    TApp t1 t2 -> prettyType t1 <> " " <> prettyType t2
    TArr t1 t2 -> prettyType t1 <> " -> " <> prettyType t2

prettyExpr :: Expr -> Text
prettyExpr = cata alg
  where
    alg :: Algebra ExprF Text
    alg = \case
        VarS name ->
            name

        LamS name a ->
            "\\" <> name
                 <> " -> "
                 <> a

        AppS exprs ->
            foldl1 (\f x -> "(" <> f <> " " <> x <> ")") exprs

        LitS Unit ->
            "()"

        LitS (Bool bool) ->
            pack (show bool)

        LitS (Int n) ->
            pack (show n)

        LitS (Float r) ->
            pack (show r)

        LitS (Char c) ->
            pack (show c)

        LitS (String str) ->
            pack (show str)

        LitS prim ->
            pack (show prim)

        LetS name expr body ->
            "let " <> name <> " = " <> expr <> " in " <> body

        IfS cond true false ->
            "if " <> cond <> " then " <> true <> " else " <> false

        CaseS expr [] ->
            "case {} of"

        CaseS expr clss ->
            "case " <> expr <> " of { " <> Text.concat (intersperse "; " $ prettyClause <$> clss) <> " }"

        OpS ops ->
            prettyOp ops

        AnnS expr ty ->
            "TODO"

prettyOp :: OpF Text -> Text
prettyOp (AddS a b) = a <> " + " <> b
prettyOp (SubS a b) = a <> " - " <> b
prettyOp (MulS a b) = a <> " * " <> b
prettyOp (EqS a b) = a <> " == " <> b
prettyOp (LtS a b) = a <> " < " <> b
prettyOp (GtS a b) = a <> " > " <> b
prettyOp (NegS a) = "-" <> a
prettyOp (NotS a) = "not " <> a

prettyClause :: (Pattern, Text) -> Text
prettyClause (p, e) = prettyPattern p <> " => " <> e

prettyPattern :: Pattern -> Text
prettyPattern = trim . cata alg where
    trim = dropPrefix . dropSuffix . Text.dropWhileEnd (== ' ')
    alg (VarP name)    = name <> " "
    alg (ConP name []) = name <> " "
    alg (ConP name ps) = "(" <> name <> " " <> Text.dropEnd 1 (Text.concat ps) <> ") "
    alg (LitP p)       = prettyPrim p <> " "
    alg AnyP           = "_ "

prettyPrim :: Prim -> Text
prettyPrim Unit        = "()"
prettyPrim (Bool b)    = pack (show b)
prettyPrim (Float r)   = pack (show r)
prettyPrim (Char c)    = pack (show c)
prettyPrim (Int n)     = pack (show n)
prettyPrim (Integer n) = pack (show n)
prettyPrim (String s)  = "\"" <> s <> "\""

dropPrefix :: Text -> Text
dropPrefix txt = fromMaybe txt $ Text.stripPrefix "(" txt

dropSuffix :: Text -> Text
dropSuffix txt = fromMaybe txt $ Text.stripSuffix ")" txt

patterns :: [Pattern] -> Text
patterns = Text.concat . intersperse "\n    - " . (:) "" . map prettyPattern

value :: Value m -> Text
value (Value p)        = prettyPrim p
value (Data name args) = name <> " " <> Text.concat (intersperse " " (value <$> args))
value Closure{}        = "<<function>>"
