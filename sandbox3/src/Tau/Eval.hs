{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Reader
import Data.Function ((&))
import Data.List (zip)
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Prim
import Tau.Stuff
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Env as Env

type ValueEnv m = Env (Value m)

data Value m
    = Value Literal
    | Data Name [Value m]
    | Record [(Name, Value m)]
    | PrimFun Name Fun [Value m]
    | Closure Name (m (Value m)) ~(ValueEnv m)

instance Show (Value m) where
    show (Value lit) = 
        "Value " <> show lit
    show (Data name lit) = 
        "Data " <> show name <> " " <> show lit
    show (Record fields) =
        "Record " <> show fields
    show (PrimFun name _ args) =
        "PrimFun " <> show name <> " " <> show args
    show Closure{} =
        "<<function>>"

newtype Eval a = Eval { unEval :: ReaderT (ValueEnv Eval) Maybe a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFail
    , MonadReader (ValueEnv Eval) )

runEval :: Eval a -> ValueEnv Eval -> Maybe a
runEval = runReaderT . unEval 

evalExpr :: (Show t) => Expr t (Prep t) Name Name -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runEval . eval

eval 
  :: (Show t, MonadFail m, MonadReader (ValueEnv m) m) 
  => Expr t (Prep t) Name Name
  -> m (Value m)
eval = cata $ \case
    EVar _ var ->
        evalVar var

    ECon _ con exprs -> do
        foldl1 evalApp (evalVar con:exprs)

    ELit _ lit ->
        pure (Value lit)

    EApp _ exprs -> 
        foldl1 evalApp exprs

    ELet _ var expr1 expr2 -> do
        val <- expr1
        local (Env.insert var val) expr2

    ELam _ var expr ->
        asks (Closure var expr)

    EIf _ cond true false -> do
        Value (LBool isTrue) <- cond
        if isTrue then true else false

    EMat _ exs eqs -> 
        sequence exs >>= evalMatch eqs 

    EOp _ op ->
        evalOp op

    ERec _ fields -> do
        let (_, keys, vals) = unzip3 (fieldsInfo fields)
        Record . zip keys <$> sequence vals

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar var = do
    case Text.stripPrefix "@" var of
        Just prim ->
            case Env.lookup prim primEnv of
                Just fun -> pure (evalPrim prim fun [])
                Nothing  -> do
                    traceShowM ("No primitive function " <> Text.unpack prim)
                    fail ("No primitive function " <> Text.unpack prim)

        Nothing -> do
            env <- ask
            unless (Env.isMember var env) (traceShowM ("Unbound identifier " <> var))
            maybe (fail "Unbound identifier") pure (Env.lookup var env)

evalApp
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = fun >>= \case
    Closure var body closure -> do
        val <- arg
        local (Env.insert var val closure <>) body

    PrimFun name fun args -> do
        val <- arg
        pure (evalPrim name fun (val:args))

evalPrim 
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => Name -> Fun -> [Value m] -> Value m
evalPrim name fun args
    | arity fun == length args = Value (applyFun fun (literal <$> reverse args))
    | otherwise                = PrimFun name fun args
  where
    literal (Value lit) = lit
    literal _ = error "Implementation error (evalPrim)"

evalOp :: (MonadFail m, MonadReader (ValueEnv m) m) => Op (m (Value m)) -> m (Value m)
evalOp = \case 
    OEq a b -> do
        Value e1 <- a
        Value e2 <- b
        pure (Value (LBool (e1 == e2)))

    OAnd a b -> do
        Value (LBool e1) <- a
        Value (LBool e2) <- b
        pure (Value (LBool (e1 && e2)))

    OOr a b -> do
        Value (LBool e1) <- a
        Value (LBool e2) <- b
        pure (Value (LBool (e1 || e2)))

evalMatch
  :: (Show t, MonadFail m, MonadReader (ValueEnv m) m)
  => [Clause (Prep t) (m (Value m))]
  -> [Value m]
  -> m (Value m)
evalMatch [] _ = fail "Runtime error (evalMatch)"
evalMatch (Clause ps exs eq:eqs) vals = 
    case tryClause ps vals of
        Just pairs -> do
            conds <- traverse (local (Env.inserts pairs)) exs
            if and (toBool <$> conds) 
                then local (Env.inserts pairs) eq
                else next
        Nothing ->
            next
  where
    next = evalMatch eqs vals
    toBool (Value (LBool b)) = b
    toBool _ = error "Runtime error (toBool)"

tryClause 
  :: (Show t, MonadFail m, MonadReader (ValueEnv m) m) 
  => [Prep t] 
  -> [Value m] 
  -> Maybe [(Name, Value m)]
tryClause xs ys = cata alg (zip xs ys)
  where
    alg :: (Show t) => Algebra (ListF (Prep t, Value m)) (Maybe [(Name, Value m)])
    alg = \case 
        Cons (RVar _ var, val) xs -> 
            Just [(var, val)] <> xs

        Cons (RCon _ con1 ps, Data con2 args) xs 
            | con1 == con2 -> (<>) <$> Just (zip ps args) <*> xs
            | otherwise    -> Nothing

        Cons (RCon _ con ps, Record fields) xs -> do
            let ys = [(v, w) | (n, v) <- zip (labels con) ps, (p, w) <- fields, n == p]
            (<>) <$> Just ys <*> xs

        Cons x y -> do
            traceShowM x
            traceShowM y
            traceShowM "."
            error "Incompatible patterns"

        Nil -> 
            Just []

labels :: Name -> [Name]
labels tag = maybe [] (Text.split (== ',')) items
  where
    items = Text.stripPrefix "{" =<< Text.stripSuffix "}" tag

constructor :: (MonadReader (ValueEnv m) m) => Name -> Int -> Value m
constructor name 0 = Data name []
constructor name n = Closure v val mempty
  where
    vars@(v:vs) = 
        take n (nameSupply "%")
    val = (ini & foldr (\fun -> asks . Closure fun)) vs
    ini = do
        Env env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)
