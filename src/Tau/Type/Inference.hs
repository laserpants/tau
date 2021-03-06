{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Type.Inference where

import Control.Arrow ((>>>), (&&&), first)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Either.Extra (mapLeft)
import Data.Foldable (foldrM)
import Data.Functor.Const
import Data.Maybe (fromJust)
import Data.Tuple.Extra (first3)
import Tau.Env (Env)
import Tau.Expr
import Tau.Solver
import Tau.Type
import Tau.Util
import qualified Tau.Env as Env

data TypeError
    = UnboundVariable Name
    | CannotSolve
    | UnificationError UnificationError
    | EmptyMatchStatement
    | BadRecordAccess
    | MissingField Name
    | NameClash Name
    deriving (Show, Eq)

data TypeAssumption
    = TypeAssumption Name Type
    | DotOperator Name Type Type
    | Field Name
    deriving (Show, Eq)

type InferTypeStack a = ExceptT TypeError (ReaderT Monoset (Supply Name)) a

newtype InferType a = InferType { unInferType :: InferTypeStack a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError TypeError
    , MonadSupply Name
    , MonadReader Monoset )

instance MonadFail InferType where
    fail _ = throwError CannotSolve

type TypeInfo = (Fix (AnnotatedAstF Type), Type, [TypeAssumption])

runInferType
  :: Env Scheme
  -> Expr
  -> Either TypeError (Type, Substitution Type, [TyClass])
runInferType env = (first3 getAnnotation <$>) . runInferTree env

runInferTree
  :: Env Scheme
  -> Expr
  -> Either TypeError (AnnotatedAst Type, Substitution Type, [TyClass])
runInferTree env = runInfer . inferTypeTree env

runInfer :: InferType a -> Either TypeError a
runInfer = unInferType
    >>> runExceptT
    >>> flip runReaderT (Monoset mempty)
    >>> flip evalSupply (nameSupply "a")
    >>> fromJust

liftErrors :: (MonadError TypeError m) => (ExceptT UnificationError m) a -> m a
liftErrors = runExceptT >>> (mapLeft UnificationError <$>) >>> (liftEither =<<)

removeTypeAssumption :: (MonadError TypeError m) => Name -> [TypeAssumption] -> m [TypeAssumption]
removeTypeAssumption name = filterM fun where
    fun (TypeAssumption name' _) = pure (name /= name')
    fun (DotOperator name' _ _)  = pure (name /= name')
    fun (Field name')
        | name == name' = throwError (NameClash name)
        | otherwise     = pure True

removeManyAssumptions :: (MonadError TypeError m) => [Name] -> [TypeAssumption] -> m [TypeAssumption]
removeManyAssumptions = flip (foldrM removeTypeAssumption)

inferTypeTree
  :: (MonadFail m, MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
  => Env Scheme
  -> Expr
  -> m (AnnotatedAst Type, Substitution Type, [TyClass])
inferTypeTree env expr = do
    (tree, as, cs) <- inferTree expr
    failIfExists UnboundVariable (unboundVars env (typeAssumptions as))
    -- failIfExists NameClash (fieldsInEnv env (fieldAssumptions as))
    Just (sub, tycls) <- liftErrors (solveTypes (cs <> envConstraints as))
    sub1 <- foldrM fieldAccess sub (operatorAssumptions env as)
    pure (tree, sub1, tycls)
  where
    envConstraints :: [TypeAssumption] -> [TypeConstraint]
    envConstraints as = do
        (x, s) <- collectAssumptions as
        (y, t) <- Env.toList env
        guard (x == y)
        pure (Explicit s t)

    failIfExists :: (MonadError TypeError m) => (Name -> TypeError) -> [Name] -> m ()
    failIfExists e (var:_) = throwError (e var)
    failIfExists _ _       = pure ()

fieldAccess
  :: (MonadFail m, MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
  => (Name, Type, Type)
  -> Substitution Type
  -> m (Substitution Type)
fieldAccess (field, t1, t2) sub =
    case unfix (apply sub t1) of
        ArrT ty _ | Struct == nodeType ty ->
            case fieldType field (apply sub ty) of
                Nothing ->
                    throwError (MissingField field)

                Just ty' -> do
                    sub1 <- liftErrors (liftEither (unify ty' (apply sub t2)))
                    pure (sub1 <> sub)

        _ -> throwError BadRecordAccess

fieldsInEnv :: Env a -> [Name] -> [Name]
fieldsInEnv env = filter (`Env.isMember` env)

unboundVars :: Env a -> [(Name, Type)] -> [Name]
unboundVars env ass = Env.namesNotIn env (fst <$> ass)

annotated :: t -> ExprF (Fix (AnnotatedAstF t)) -> AnnotatedAst t
annotated t a = AnnotatedAst $ Fix $ Const t :*: a

expand :: AnnotatedAst t -> (Fix (AnnotatedAstF t), t)
expand = (id &&& getConst . left . unfix) . getAnnotatedAst

typeAssumptions :: [TypeAssumption] -> [(Name, Type)]
typeAssumptions = concatMap fun where
    fun (TypeAssumption name ty) = [(name, ty)]
    fun _ = []

operatorAssumptions :: Env Scheme -> [TypeAssumption] -> [(Name, Type, Type)]
operatorAssumptions env = concatMap fun where
    fun (DotOperator name t1 t2)
        | name `Env.isMember` env = []
        | otherwise               = [(name, t1, t2)]
    fun _ = []

fieldAssumptions :: [TypeAssumption] -> [Name]
fieldAssumptions = concatMap fun where
    fun (Field name) = [name]
    fun _ = []

collectAssumptions :: [TypeAssumption] -> [(Name, Type)]
collectAssumptions = concatMap fun where
    fun (TypeAssumption name ty) = [(name, ty)]
    fun (DotOperator name ty _)  = [(name, ty)]
    fun Field{} = []

inferTree
  :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
  => Expr
  -> m (AnnotatedAst Type, [TypeAssumption], [TypeConstraint])
inferTree = fmap to3 . runWriterT . cata alg
  where
    alg :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
        => Algebra ExprF (WriterT [TypeConstraint] m (AnnotatedAst Type, [TypeAssumption]))
    alg = fmap fmap fmap (to3 . first expand) >>> \case
        VarS name -> do
            beta <- varT <$> supply
            pure (annotated beta (VarS name), [TypeAssumption name beta])

        LamS name expr -> do
            var <- supply
            let beta = varT var
            (expr', t1, a1) <- local (insertIntoMonoset var) expr
            tell [Equality t beta | (y, t) <- collectAssumptions a1, name == y]
            a1' <- removeTypeAssumption name a1
            pure (annotated (beta `arrT` t1) (LamS name expr'), a1')

        AppS exprs -> do
            (expr', _, as) <- foldl1 inferApp exprs
            pure (AnnotatedAst expr', as)

        LitS prim -> do
            t <- inferPrim prim
            pure (annotated t (LitS prim), [])

        LetS var expr body ->
            inferLet False var expr body

        LetRecS var expr body ->
            inferLet True var expr body

        IfS cond true false -> do
            (cond', t1, a1) <- cond
            (true', t2, a2) <- true
            (false', t3, a3) <- false
            tell [Equality t1 tBool]
            tell [Equality t2 t3]
            pure (annotated t2 (IfS cond' true' false'), a1 <> a2 <> a3)

        MatchS _ [] ->
            throwError EmptyMatchStatement

        LamMatchS [] ->
            throwError EmptyMatchStatement

        MatchS expr clss -> do
            beta <- varT <$> supply
            (expr', t1, a1) <- expr
            (clss', as) <- foldrM (inferClause beta t1) ([], []) clss
            pure (annotated beta (MatchS expr' clss'), a1 <> as)

        LamMatchS clss -> do
            beta <- varT <$> supply
            zeta <- varT <$> supply
            (clss', as) <- foldrM (inferClause beta zeta) ([], []) clss
            pure (annotated (zeta `arrT` beta) (LamMatchS clss'), as)

        OpS op ->
            inferOp op

        DotS name expr -> do
            t1 <- varT <$> supply
            (e2', t2, a2) <- expr
            beta <- varT <$> supply
            tell [Equality t1 (t2 `arrT` beta)]
            pure (annotated beta (DotS name e2'), [DotOperator name t1 beta] <> a2)

        StructS fields -> do
            (expr', _, as) <- inferStruct fields
            pure (AnnotatedAst expr', as)

        AnnS{} ->
            undefined  -- TODO

        ErrS ->
            pure (annotated (conT "Error") ErrS, [])

inferStruct
  :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m, MonadWriter [TypeConstraint] m)
  => [(Name, m TypeInfo)]
  -> m TypeInfo
inferStruct fields = do
    beta <- varT <$> supply
    let ini = (Fix (Const beta :*: VarS con), beta, [TypeAssumption con beta])
    foldl inferApp (pure ini) (lefts >>= unpair)
  where
    con = "#Struct" <> intToText (length fields)
    lefts = first (pure . tinfo) <$> fields
    as = [Field n | (n, _) <- fields]
    tinfo field = let ty = conT ("#" <> field) in (Fix (Const ty :*: VarS field), ty, as)

inferClause
  :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m, MonadWriter [TypeConstraint] m)
  => Type
  -> Type
  -> MatchClause (m TypeInfo)
  -> ([MatchClause (Fix (AnnotatedAstF Type))], [TypeAssumption])
  -> m ([MatchClause (Fix (AnnotatedAstF Type))], [TypeAssumption])
inferClause beta t (pat, expr) (ps, as) = do
    (expr', t1, a1) <- local (insertManyIntoMonoset vars) expr
    (t2, a2) <- inferPattern pat
    tell [Equality beta t1]
    tell [Equality t t2]
    tell (constraints a1 a2)
    a1' <- removeManyAssumptions vars a1
    a2' <- removeManyAssumptions vars a2
    pure ((pat, expr'):ps, as <> a1' <> a2')
  where
    vars = patternVars pat
    constraints a1 a2 = do
        (y1, t1) <- collectAssumptions a1
        (y2, t2) <- collectAssumptions a2
        var <- vars
        guard (var == y1 && var == y2)
        pure (Equality t1 t2)

inferPattern :: (MonadSupply Name m, MonadWriter [TypeConstraint] m) => Pattern -> m (Type, [TypeAssumption])
inferPattern = cata $ \case
    VarP var -> do
        beta <- varT <$> supply
        pure (beta, [TypeAssumption var beta])

    RecP name keys ps -> do
        beta <- varT <$> supply
        (ts, ass) <- (fmap unzip . sequence) ps
        ts' <- fmap fmap fmap varT (supplies (length keys))
        tell [Equality (conT ("#" <> k)) kt | (k, kt) <- zip keys ts']
        pure (beta, TypeAssumption name (foldr arrT beta (concat (unpair <$> zip ts' ts))):concat ass)

    ConP name ps -> do
        beta <- varT <$> supply
        (ts, ass) <- (fmap unzip . sequence) ps
        pure (beta, TypeAssumption name (foldr arrT beta ts):concat ass)

    LitP prim -> do
        t <- inferPrim prim
        pure (t, [])

    AnyP -> do
        beta <- varT <$> supply
        pure (beta, [])

inferApp
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => m TypeInfo
  -> m TypeInfo
  -> m TypeInfo
inferApp fun arg = do
    (e1', t1, a1) <- fun
    (e2', t2, a2) <- arg
    beta <- varT <$> supply
    tell [Equality t1 (t2 `arrT` beta)]
    pure (Fix (Const beta :*: AppS [e1', e2']), beta, a1 <> a2)

inferLet
  :: (MonadError TypeError m, MonadReader Monoset m, MonadWriter [TypeConstraint] m)
  => Bool
  -> Name
  -> m TypeInfo
  -> m TypeInfo
  -> m (AnnotatedAst Type, [TypeAssumption])
inferLet rec var expr body = do
    (expr', t1, a1) <- expr
    (body', t2, a2) <- body
    set <- ask
    tell [Implicit t t1 set | (y, t) <- collectAssumptions (a1 <> a2), var == y]
    a1' <- removeTypeAssumption var a1
    a2' <- removeTypeAssumption var a2
    let (con, as) = if rec then (LetRecS, a1') else (LetS, a1)
    pure (annotated t2 (con var expr' body'), as <> a2')

inferOp
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => OpF (m TypeInfo)
  -> m (AnnotatedAst Type, [TypeAssumption])
inferOp = \case
    AddS e1 e2 -> op2 AddS e1 e2 numericOp2
    SubS e1 e2 -> op2 SubS e1 e2 numericOp2
    MulS e1 e2 -> op2 MulS e1 e2 numericOp2
    DivS e1 e2 -> op2 DivS e1 e2 numericOp2
    LtS e1 e2  -> op2 LtS e1 e2 comparisonOp
    GtS e1 e2  -> op2 GtS e1 e2 comparisonOp
    EqS e1 e2  -> op2 EqS e1 e2 equalityOp
    NeqS e1 e2 -> op2 NeqS e1 e2 equalityOp
    OrS e1 e2  -> op2 OrS e1 e2 logicalOp
    AndS e1 e2 -> op2 AndS e1 e2 logicalOp
    NegS e     -> op1 NegS e numericOp1
    NotS e     -> op1 NotS e numericOp1
    CmpS e1 e2 -> op2 CmpS e1 e2 compositionOp

op1
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => (Fix (AnnotatedAstF Type) -> OpF (Fix (AnnotatedAstF Type)))
  -> m TypeInfo
  -> Scheme
  -> m (AnnotatedAst Type, [TypeAssumption])
op1 con e1 sig = do
    (e1', t1, a1) <- e1
    beta <- varT <$> supply
    tell [Explicit (t1 `arrT` beta) sig]
    pure (annotated beta (OpS (con e1')), a1)

op2
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => (Fix (AnnotatedAstF Type) -> Fix (AnnotatedAstF Type) -> OpF (Fix (AnnotatedAstF Type)))
  -> m TypeInfo
  -> m TypeInfo
  -> Scheme
  -> m (AnnotatedAst Type, [TypeAssumption])
op2 con e1 e2 sig = do
    (e1', t1, a1) <- e1
    (e2', t2, a2) <- e2
    beta <- varT <$> supply
    tell [Explicit (t1 `arrT` (t2 `arrT` beta)) sig]
    pure (annotated beta (OpS (con e1' e2')), a1 <> a2)

inferPrim :: (Monad m) => Prim -> m Type
inferPrim = pure . \case
    Unit      -> tUnit
    Bool{}    -> tBool
    Int{}     -> tInt
    Integer{} -> tInteger
    Float{}   -> tFloat
    Char{}    -> tChar
    String{}  -> tString

dotOp :: Scheme
dotOp =
    Forall ["a", "b"]
    []
    (varT "a" `arrT` (varT "a" `arrT` varT "b") `arrT` varT "b")

compositionOp :: Scheme
compositionOp =
    Forall ["a", "b", "c"] []
    ((varT "b" `arrT` varT "c") `arrT` (varT "a" `arrT` varT "b") `arrT` (varT "a" `arrT` varT "c"))

numericOp1 :: Scheme
numericOp1 =
    Forall ["a"]
    [TyCl "Num" (varT "a")]
    (arrT (varT "a") (varT "a"))

numericOp2 :: Scheme
numericOp2 =
    Forall ["a"]
    [TyCl "Num" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") (varT "a")))

equalityOp :: Scheme
equalityOp =
    Forall ["a"]
    [TyCl "Eq" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

comparisonOp :: Scheme
comparisonOp =
    Forall ["a"]
    [TyCl "Ord" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

logicalOp :: Scheme
logicalOp =
    Forall [] []
    (arrT tBool (arrT tBool tBool))
