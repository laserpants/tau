{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Reader
import Data.Char
import Data.Map.Strict (Map)
import Data.Text (pack, unpack)
import Tau.Core
import Tau.Env (Env(..))
import Tau.Eval.Prim
import Tau.Lang
import Tau.Tooling
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Env as Env

type ValueEnv m = Env (Value m)

-- | An expression evaluates to a literal value, a fully applied data
-- constructor, a primitive function, or a closure.
data Value m
    = Value Prim
    | Data Name [Value m]
    | PrimFun Name Fun [Value m]
    | Closure Name (m (Value m)) ~(ValueEnv m)
    | Fail String -- TODO temp

instance Show (Value m) where
    show (Value lit) = 
        "Value " <> show lit
    show (Data name lit) = 
        "Data " <> show name <> " " <> show lit
    show (PrimFun name _ args) =
        "PrimFun " <> show name <> " " <> show args
    show Closure{} =
        "<<function>>"
    show (Fail err) =
        err

instance Eq (Value m) where
    (==) (Value v) (Value w)             = v == w
    (==) (Data c vs) (Data d ws)         = c == d && vs == ws
    (==) (PrimFun f _ _) (PrimFun g _ _) = f == g
    (==) _ _                             = False

newtype Eval a = Eval { unEval :: ReaderT (ValueEnv Eval) Maybe a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFail
    , MonadReader (ValueEnv Eval) )

runEval :: Eval a -> ValueEnv Eval -> Maybe a
runEval = runReaderT . unEval 

evalExpr :: Core -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runEval . eval

eval 
  :: (MonadFail m, MonadReader (ValueEnv m) m) 
  => Core
  -> m (Value m)
eval = cata $ \case

    CVar var ->
        evalVar var

    CLit lit ->
        pure (Value lit)

    CApp exs -> 
        foldl1 evalApp exs

    CLet var e1 e2 -> do
        val <- e1
        local (Env.insert var val) e2 

    CLam var e1 ->
        asks (Closure var e1)

    CIf e1 e2 e3 -> do
        Value (TBool isTrue) <- e1
        if isTrue then e2 else e3

    CPat expr fields -> 
        expr >>= evalPat fields

getField :: (Monad m) => Name -> [Value m] -> m (Value m)
getField name [Data f (v:fs)]
    | f == ("{" <> name <> "}") = pure v
    | otherwise                 = getField name fs
--getField name [x] = do
--    traceShowM "$$$$$$$$$$$$$$$$$$$$$$$$$$$$"
--    -- temp
--    traceShowM name
--    traceShowM x
--    pure x
--getField x y = do
--    traceShowM x
--    traceShowM y
--    traceShowM "///////////"
--    undefined

closure :: (MonadReader (ValueEnv m) m) => Name -> m (Value m) -> m (Value m)
closure var a = pure (Closure var a mempty)

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar var = 
    case Text.stripPrefix "@" var of
        Just "#getField" ->
            closure "?a" $ do 
                Just (Value (TAtom name)) <- asks (Env.lookup "?a")
                closure "?b" $ do
                    Just (Data "#" fields) <- asks (Env.lookup "?b")
                    traceShowM "b****"
                    traceShowM name
                    traceShowM fields
                    traceShowM "e****"
                    traceShowM name
                    getField name fields

        Just prim ->
            case Env.lookup prim primEnv of
                Just fun -> evalPrim prim fun []
                Nothing  -> do
                    traceShowM ("No primitive function " <> Text.unpack prim)
                    -- fail ("No primitive function " <> Text.unpack prim)
                    pure (Fail ("No primitive function " <> Text.unpack prim))

        _ -> 
            asks (Env.lookup var) >>= \case
                Just value ->
                    pure value
                Nothing -> 
                    if isConstructor var 
                        then pure (Data var []) 
                        else do 
                            traceShowM ("Unbound identifier " <> var)
                            -- fail "Unbound identifier"
                            pure (Fail ("Unbound identifier '" <> unpack var <> "'"))

-- TODO
isConstructor :: Name -> Bool
isConstructor var
    | isLower init    = False
    | '_' == init     = False
    | '$' == init     = False
    | '{' == init     = True
    -- TODO
    | isUpper init    = True
    | "(::)" == var   = True
    | "(,)" == var    = True
    | "[]" == var     = True
    | "#" == var      = True
--    | isTupleCon var  = True
--    | isRecordCon var = True
    -- TODO
    | otherwise       = False
  where
    init = Text.head var

evalPrim 
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => Name 
  -> Fun 
  -> [Value m] 
  -> m (Value m)
evalPrim name fun args
    | arity fun == length args = 
        Value . applyFun fun <$> traverse literal (reverse args)
    | otherwise = 
        pure (PrimFun name fun args)
  where
    literal (Value lit) = pure lit
    literal _           = fail "Runtime error (evalPrim)"
    --literal _           = pure (Fail "Runtime error (evalPrim)")

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
        evalPrim name fun (val:args)

    Data con args -> do
        a <- arg
        pure (Data con (args <> [a]))

    err -> 
        pure err

evalPat 
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => [([Name], m (Value m))]
  -> Value m
  -> m (Value m)
--evalPat []            _ = fail "Runtime error (evalPat)"
evalPat []            _ = pure (Fail "Runtime error (evalPat)")
evalPat [(["$_"], e)] _ = e
evalPat ((ps@[p, _, _], e):_) val 
    | isRowCon p        = evalRowPat ps val >>= flip local e
  where
    isRowCon ""  = False
    isRowCon con = Text.head con == '{' && Text.last con == '}'
evalPat ((p:ps, e):eqs) val = 
    case val of
        Data con args | p == con ->
            local (Env.inserts (zip ps args)) e
        _ ->
            evalPat eqs val

--evalPat (([p, q, r], e):eqs) val | isRowCon p = do
--    case Map.lookup p zz of
--        Nothing -> 
--            fail "Runtime error (evalPat)"
--
--        Just (v:_) -> 
--            local (Env.inserts [(q, v), (r, fromMap (Map.delete p zz))]) e
--  where
--    zz = toMap val mempty
--
--    isRowCon ""  = False
--    isRowCon con = Text.head con == '{' && Text.last con == '}'
--
--    toMap :: Value m -> Map Name [Value m] -> Map Name [Value m]
--    toMap (Data "{}" [])    m = m
--    toMap (Data lab (v:vs)) m = foldr toMap (Map.insertWith (<>) lab [v] m) vs
--
--    fromMap :: Map Name [Value m] -> Value m
--    fromMap = Map.foldrWithKey (\k -> flip (foldr (\v m -> Data k [v, m]))) (Data "{}" [])  

evalRowPat :: (MonadFail m) => [Name] -> Value m -> m (Env (Value m) -> Env (Value m))
evalRowPat [p, q, r] val =
    case Map.lookup p pmap of
        Nothing -> 
            fail "Runtime error (evalPat)"
            --pure (Fail "Runtime error (evalPat)")

        Just (v:_) -> 
            pure (Env.inserts [(q, v), (r, fromMap (Map.delete p pmap))]) 
  where
    pmap = toMap val mempty

    toMap :: Value m -> Map Name [Value m] -> Map Name [Value m]
    toMap (Data "{}" [])    m = m
    toMap (Data lab (v:vs)) m = foldr toMap (Map.insertWith (<>) lab [v] m) vs

    fromMap :: Map Name [Value m] -> Value m
    fromMap = Map.foldrWithKey (\k -> flip (foldr (\v m -> Data k [v, m]))) (Data "{}" [])  


--evalPat [] _ = fail "Runtime error (evalPat)"
--evalPat [(["$_"], e)] _ = e
--evalPat ((p:ps, e):eqs) val =
--    case val of
--
--        Data con args | p == con ->
--            local (Env.inserts (zip ps args)) e
--
--        _ ->
--            evalPat eqs val

--constructor :: (MonadReader (ValueEnv m) m) => Name -> Int -> Value m
--constructor name 0 = Data name []
--constructor name n = Closure v val mempty
--  where
--    vars@(v:vs) = 
--        take n (nameSupply "%")
--    val = (ini & foldr (\fun -> asks . Closure fun)) vs
--    ini = do
--        Env env <- ask
--        let args = fmap (env Map.!) vars
--        pure (Data name args)
