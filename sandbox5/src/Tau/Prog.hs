{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE StrictData            #-}
module Tau.Prog where

import Control.Monad.Except (MonadError, catchError, throwError, runExceptT)
import Control.Monad.Extra (allM, (||^))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Either.Combinators (rightToMaybe)
import Data.Either.Extra (eitherToMaybe)
import Data.Function ((&))
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first)
import Tau.Compiler.Error
import Tau.Compiler.Substitute
import Tau.Compiler.Unify
import Tau.Compiler.Unify
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Tooling
import Tau.Type
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

-- | Product type
data Product = Mul Name [Type]
    deriving (Show, Eq, Ord)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq, Ord)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data ClassInfo p a = ClassInfo 
    { classSignature  :: PredicateT p
    , classPredicates :: List (PredicateT p)
    , classMethods    :: List (Name, a)
    } deriving (Show, Eq)

-- Environments

type Context = Env (Set Name)

type TypeEnv = Env Scheme

type KindEnv = Env Kind

type ClassEnv = Env 
    ( ClassInfo Name Type                          -- Abstract interface
    , List (ClassInfo Type (Ast (TypeInfo ()))) )  -- Instances

type ConstructorEnv = Env (Set Name, Int)

type Instance = ClassInfo Type (Ast (TypeInfo ()))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

super :: ClassEnv -> Name -> [Name]
super env name = maybe [] (fmap predicateName . classPredicates . fst) 
                          (Env.lookup name env)

instances :: ClassEnv -> Name -> [Instance]
instances env name = fromMaybe [] (snd <$> Env.lookup name env)

bySuper :: ClassEnv -> Predicate -> [Predicate]
bySuper env self@(InClass name ty) =
    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

byInstance 
  :: (MonadError UnificationError m, MonadSupply Name m) 
  => ClassEnv 
  -> Predicate 
  -> m (Maybe [Predicate])
byInstance env self@(InClass name ty) = do
    r <- sequence [runExceptT (tryInstance i) | i <- instances env name]
    pure (msum (rightToMaybe <$> r))
  where
    tryInstance ClassInfo{..} = applyBoth <$> matchClass classSignature self 
                                          <*> pure classPredicates

entail 
  :: (MonadError UnificationError m, MonadSupply Name m) 
  => ClassEnv 
  -> [Predicate] 
  -> Predicate 
  -> m Bool
entail env cls0 cl = pure super ||^ instances
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instances = byInstance env cl >>= \case
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: Predicate -> Bool
isHeadNormalForm (InClass _ t) = 
    flip cata t $ \case
        TApp _ t1 _ -> t1
        TVar{}      -> True
        _           -> False

toHeadNormalForm 
  :: (MonadError UnificationError m, MonadSupply Name m) 
  => ClassEnv
  -> [Predicate] 
  -> m [Predicate]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = byInstance env tycl >>= \case
            Nothing  -> throwError ContextReductionFailed
            Just cls -> toHeadNormalForm env cls

simplify 
  :: (MonadError UnificationError m, MonadSupply Name m) 
  => ClassEnv 
  -> [Predicate] 
  -> m [Predicate]
simplify env = loop []
  where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        entailed <- entail env (qs <> ps) p
        loop (if entailed then qs else p:qs) ps

--        if entailed then loop qs ps 
--                    else loop (p:qs) ps

reduce
  :: (MonadSupply Name m) 
  => ClassEnv
  -> [Predicate] 
  -> m (Either UnificationError [Predicate])
reduce env cls = runExceptT (toHeadNormalForm env cls >>= simplify env) 


--simplify2 
--  :: (MonadError UnificationError m, MonadSupply Name m) 
--  => ClassEnv 
--  -> [Predicate] 
--  -> m [Predicate]
--simplify2 env = loop []
--  where
--    loop qs [] = pure qs
--    loop qs (p:ps) = do
--        entailed <- entail env (qs <> ps) p
--        if isVar (predicateType p) && entailed 
--            then loop qs ps 
--            else loop (p:qs) ps
--
--reduce2
--  :: (MonadSupply Name m) 
--  => ClassEnv
--  -> [Predicate] 
--  -> m (Either UnificationError [Predicate])
----reduce2 env cls = runExceptT (toHeadNormalForm env cls >>= simplify2 env) 
--reduce2 = runExceptT <$$> simplify2



--reduce2
--  :: (MonadSupply Name m) 
--  => ClassEnv
--  -> [Predicate] 
--  -> m (Either UnificationError [Predicate])
--reduce2 = runExceptT <$$> simplify 


unifyClass, matchClass 
  :: (MonadSupply Name m, MonadError UnificationError m) 
  => Predicate 
  -> Predicate 
  -> m (Substitution Type, Substitution Kind)
unifyClass = liftU unifyTypes
matchClass = liftU matchTypes

liftU 
  :: (MonadSupply Name m, MonadError UnificationError m) 
  => (Type -> Type -> m a) 
  -> Predicate 
  -> Predicate 
  -> m a
liftU m (InClass c1 t1) (InClass c2 t2)
    | c1 == c2  = m t1 t2
    | otherwise = throwError ClassMismatch

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

getClassEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ClassEnv
getClassEnv (e, _, _, _) = e

askClassEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ClassEnv
askClassEnv = asks getClassEnv

getTypeEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> TypeEnv
getTypeEnv (_, e, _, _) = e

askTypeEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m TypeEnv
askTypeEnv = asks getTypeEnv

getKindEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> KindEnv
getKindEnv (_, _, e, _) = e

askKindEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m KindEnv
askKindEnv = asks getKindEnv

getConstructorEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ConstructorEnv
getConstructorEnv (_, _, _, e) = e

askConstructorEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ConstructorEnv
askConstructorEnv = asks getConstructorEnv

inClassEnv 
  :: (ClassEnv -> ClassEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inClassEnv f (e1, e2, e3, e4) = (f e1, e2, e3, e4)

inTypeEnv 
  :: (TypeEnv -> TypeEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inTypeEnv f (e1, e2, e3, e4) = (e1, f e2, e3, e4)

inKindEnv 
  :: (KindEnv -> KindEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inKindEnv f (e1, e2, e3, e4) = (e1, e2, f e3, e4)

inConstructorEnv 
  :: (ConstructorEnv -> ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inConstructorEnv f (e1, e2, e3, e4) = (e1, e2, e3, f e4)

withClassInfo 
  :: (MonadError Error m, MonadSupply Text m)
  => (List (PredicateT Name) -> ClassInfo Type (Ast (TypeInfo ())) -> m a)
  -> Name 
  -> Type 
  -> ClassEnv
  -> m a
withClassInfo fn name ty env = do
    (ClassInfo{..}, insts) <- liftMaybe (MissingClass name) (Env.lookup name env)
    info <- sequence [tryMatch i | i <- insts]
    msum info & maybe (throwError (MissingInstance name ty)) (fn classPredicates)
  where
    tryMatch info@ClassInfo{..} = do
        sub <- eitherToMaybe <$> runExceptT (matchTypes (predicateType classSignature) ty)
        pure (applyBoth <$> sub <*> pure info)

lookupAllClassMethods
  :: (MonadSupply Name m, MonadError Error m)
  => Name
  -> Type
  -> ClassEnv
  -> m [(Name, Ast (TypeInfo ()))]
lookupAllClassMethods name ty env = withClassInfo collectAll name ty env 
  where 
    collectAll classPredicates ClassInfo{ classMethods = methods } = do
        super <- concat <$$> forM classPredicates $ \(InClass name _) ->
            lookupAllClassMethods name ty env
        pure (super <> methods)

lookupClassInstance
  :: (MonadSupply Name m, MonadError Error m)
  => Name
  -> Type
  -> ClassEnv
  -> m (ClassInfo Type (Ast (TypeInfo ())))
lookupClassInstance = withClassInfo (const pure) 

lookupAllClassX
  :: (MonadSupply Name m, MonadError Error m)
  => Name
  -> ClassEnv
  -> m [(Name, Type)]
lookupAllClassX name env = do
    (ClassInfo{..}, _) <- liftMaybe (MissingClass name) (Env.lookup name env)
    super <- concat <$$> forM classPredicates $ \(InClass name _) ->
        lookupAllClassX name env
    pure (super <> classMethods)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data TypeInfoT e t = TypeInfo
    { nodeErrors     :: e 
    , nodeType       :: t
    , nodePredicates :: List Predicate
    }

type TypeInfo e = TypeInfoT e Type

-- Type class instances 

deriving instance (Show e, Show t) => 
    Show (TypeInfoT e t)

deriving instance (Eq e, Eq t) => 
    Eq (TypeInfoT e t)

deriving instance Functor (TypeInfoT e)

instance (Typed t) => Typed (TypeInfoT e t) where
    typeOf = typeOf . nodeType 

instance (Typed t) => Typed (Binding t p) where
    typeOf = typeOf . bindingTag

instance Typed Void where
    typeOf _ = tVar kTyp "a" 

instance Typed () where
    typeOf _ = tVar kTyp "a" 

instance FreeIn TypeEnv where
    free = free . Env.elems

instance FreeIn (TypeInfo e) where
    free = free . nodeType

instance (Substitutable Type a) => Substitutable (TypeInfo e) a where
    apply sub = \case
        TypeInfo e ty ps -> TypeInfo e (apply sub ty) (apply sub ps)

instance (Substitutable Scheme t) => Substitutable TypeEnv t where
    apply = Env.map . apply 

instance (Substitutable Type t) => Substitutable (ClassInfo Type (Ast (TypeInfo e))) t where
    apply sub ClassInfo{..} =
        ClassInfo{ classPredicates = apply sub classPredicates
                 , classSignature  = apply sub classSignature
                 , .. }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

patternPredicates :: ProgPattern (TypeInfoT e t) -> [Predicate]
patternPredicates = nodePredicates . patternTag

exprPredicates :: ProgExpr (TypeInfoT e t) -> [Predicate]
exprPredicates = nodePredicates . exprTag

guardPredicates :: Guard (ProgExpr (TypeInfoT e t)) -> [Predicate]
guardPredicates (Guard es e) = exprPredicates e <> (exprPredicates =<< es)

clausePredicates :: ProgClause (TypeInfoT e t) -> [Predicate]
clausePredicates (Clause _ p gs) = patternPredicates p <> (guardPredicates =<< gs)

astPredicates :: Ast (TypeInfoT e t) -> [Predicate]
astPredicates = exprPredicates . getAst

constructorEnv :: [(Name, ([Name], Int))] -> ConstructorEnv
constructorEnv = Env.fromList . (first Set.fromList <$$>)

simplifyPredicates :: TypeInfo e -> TypeInfo e
simplifyPredicates (TypeInfo e ty ps) = TypeInfo e ty (nub (filter relevant ps))
  where
    freeVars = free ty
    relevant (InClass _ (Fix (TVar _ var))) 
        | var `notElem` (fst <$> freeVars) = False
    relevant _                             = True

addErrors :: [e] -> TypeInfoT [e] t -> TypeInfoT [e] t
addErrors errs TypeInfo{..} = TypeInfo{ nodeErrors = errs <> nodeErrors, .. }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

astTypeVars :: Ast (TypeInfo e) -> [(Name, Kind)]
astTypeVars (Ast expr) = nub (exprTypeVars expr)
  where
    exprTypeVars = cata $ \case
        EVar    t _            -> typeVars (typeOf t)
        ECon    t _ as         -> typeVars (typeOf t) <> concat as
        ELit    t _            -> typeVars (typeOf t)
        EApp    t as           -> typeVars (typeOf t) <> concat as
        ELet    t bind a1 a2   -> typeVars (typeOf t) <> bindingTypeVars bind <> a1 <> a2
        EFix    t _ a1 a2      -> typeVars (typeOf t) <> a1 <> a2
        ELam    t ps a         -> typeVars (typeOf t) <> concatMap patternTypeVars ps <> a
        EIf     t a1 a2 a3     -> typeVars (typeOf t) <> a1 <> a2 <> a3
        EPat    t a clauses    -> typeVars (typeOf t) <> a <> concatMap clauseTypeVars clauses
        EFun    t clauses      -> typeVars (typeOf t) <> concatMap clauseTypeVars clauses
        EOp1    t op a         -> typeVars (typeOf t) <> op1TypeVars op <> a
        EOp2    t op a b       -> typeVars (typeOf t) <> op2TypeVars op <> a <> b
        ETuple  t as           -> typeVars (typeOf t) <> concat as
        EList   t as           -> typeVars (typeOf t) <> concat as
        ERow    t _ a b        -> typeVars (typeOf t) <> a <> b
        EAnn    _ a            -> a

    bindingTypeVars = \case
        BPat    t p            -> typeVars (typeOf t) <> patternTypeVars p
        BFun    t _ ps         -> typeVars (typeOf t) <> concatMap patternTypeVars ps

    clauseTypeVars = \case
        Clause  t p gs         -> typeVars (typeOf t) <> patternTypeVars p
                                                      <> concatMap guardTypeVars gs
    guardTypeVars = \case
        Guard es e             -> concat es <> e

    patternTypeVars = cata $ \case
        PVar    t var          -> typeVars (typeOf t)
        PCon    t _ ps         -> typeVars (typeOf t) <> concat ps
        PLit    t _            -> typeVars (typeOf t)
        PAs     t _ p          -> typeVars (typeOf t) <> p
        POr     t p q          -> typeVars (typeOf t) <> p <> q
        PAny    t              -> typeVars (typeOf t)
        PTuple  t ps           -> typeVars (typeOf t) <> concat ps
        PList   t ps           -> typeVars (typeOf t) <> concat ps
        PRow    t _ p q        -> typeVars (typeOf t) <> p <> q
        PAnn    _ p            -> p

    op1TypeVars = \case
        ONeg    t              -> typeVars (typeOf t)
        ONot    t              -> typeVars (typeOf t)

    op2TypeVars = \case
        OEq     t              -> typeVars (typeOf t)
        ONeq    t              -> typeVars (typeOf t)
        OAnd    t              -> typeVars (typeOf t)
        OOr     t              -> typeVars (typeOf t)
        OAdd    t              -> typeVars (typeOf t)
        OSub    t              -> typeVars (typeOf t)
        OMul    t              -> typeVars (typeOf t)
        ODiv    t              -> typeVars (typeOf t)
        OPow    t              -> typeVars (typeOf t)
        OMod    t              -> typeVars (typeOf t)
        OLt     t              -> typeVars (typeOf t)
        OGt     t              -> typeVars (typeOf t)
        OLte    t              -> typeVars (typeOf t)
        OGte    t              -> typeVars (typeOf t)
        OLarr   t              -> typeVars (typeOf t)
        ORarr   t              -> typeVars (typeOf t)
        OFpipe  t              -> typeVars (typeOf t)
        OBpipe  t              -> typeVars (typeOf t)
        OOpt    t              -> typeVars (typeOf t)
