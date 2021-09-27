{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Except
import Control.Monad.Fix
import Control.Monad.Reader
import Data.Char
import Data.Foldable
import Data.Functor.Foldable
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.Text (Text, pack, unpack)
import Debug.Trace
import Tau.Env (Env(..))
import Tau.Eval.Prim
import Tau.Misc
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Env as Env


--type ValueEnvX m = Env (m (ValueX m))
--
--newtype EvalX a = EvalX { unEvalX :: ReaderT (ValueEnvX EvalX) (Either Text) a } deriving
--    ( Functor
--    , Applicative
--    , Monad
--    , MonadError Text
--    , MonadReader (ValueEnvX EvalX) )
--
--runEvalX :: EvalX a -> ValueEnvX EvalX -> Either Text a
--runEvalX = runReaderT . unEvalX
--
--evalExprX :: Core -> ValueEnvX EvalX -> Either Text (ValueX EvalX)
--evalExprX = runEvalX . interpret
--
--data ValueX m
--    = ValueX Prim
--    | DataX Name [ValueX m]
--    | ClosureX Name (m (ValueX m)) (ValueEnvX m)
--    | PrimFunX Name Fun [m (ValueX m)]
--
--instance Eq (ValueX m) where
--    (==) (ValueX v) (ValueX w)             = v == w
--    (==) (DataX c vs) (DataX d ws)         = c == d && vs == ws
--    (==) (PrimFunX f _ _) (PrimFunX g _ _) = f == g
--    (==) _ _                               = False
--
--instance Show (ValueX m) where
--    show (ValueX prim)          = "Value "   <> "(" <> show prim <> ")"
--    show (DataX name vs)        = "Data "    <> show name <> " " <> show vs
--    show (PrimFunX name _ args) = "PrimFun " <> show name <> " " <> show (length args)
--    show (ClosureX f _ _)       = "<<function " <> show f <> ">>"
--
--interpret
--  :: (MonadError Text m, MonadReader (ValueEnvX m) m)
--  => Core
--  -> m (ValueX m)
--interpret = cata $ \case
--
--    CVar var -> traceShowM ("CVar " <> show var) >> evalVarX var
--    CLit lit -> traceShowM "CLit" >> pure (ValueX lit)
--    CApp exs -> traceShowM "CApp" >> foldl1 evalAppX exs
--
--    CLam var e1 -> traceShowM "CLam" >> 
--        asks (ClosureX var e1)
--
--    CLet var e1 e2 -> traceShowM "CLet" >>
--        local (Env.insert var e1) e2
--
--    CIf e1 e2 e3 -> traceShowM "CIf" >> e1 >>= \case 
--        ValueX (TBool isTrue) ->
--            if isTrue then e2 else e3
--        x -> do
--            traceShowM x
--            throwError "If clause: not a boolean"
--
--    CPat expr clauses -> traceShowM "CPat" >> 
--        evalPatX expr clauses 
--
----getFieldX :: (Monad m) => Name -> [Value m] -> m (Value m)
--getFieldX name [DataX f (v:fs)]
--    | f == ("{" <> name <> "}") = pure v
--    | otherwise                 = getFieldX name fs
--
----closureX :: (MonadReader (ValueEnv m) m) => Name -> m (Value m) -> m (Value m)
--closureX var a = pure (ClosureX var a mempty)
--
--evalVarX 
--  :: (MonadError Text m, MonadReader (ValueEnvX m) m) 
--  => Name 
--  -> m (ValueX m)
--evalVarX var =
--    case Text.stripPrefix "@" var of
--
--        Just "(!).getField" -> do
--            closureX "?a" $ do
--                env <- ask
--                x <- fromJust (Env.lookup "?a" env)
--                let (ValueX (TSymbol name)) = x
--                closureX "?b" $ do
--                    env <- ask
--                    x <- fromJust (Env.lookup "?b" env)
--                    let DataX "!" fields = x
--                    x <- getFieldX (withInitialLower_ name) fields
--                    let ClosureX var body _ = x
--                    local (Env.insert var (pure (ValueX TUnit))) body
--
--        Just "(#).getField" ->
--            closureX "?a" $ do
--                env <- ask
--                x <- fromJust (Env.lookup "?a" env)
--                let (ValueX (TSymbol name)) = x
--                closureX "?b" $ do
--                    env <- ask
--                    x <- fromJust (Env.lookup "?b" env)
--                    let DataX "#" fields = x
--                    getFieldX name fields
--                    --env <- ask
--                    --Data "#" fields <- fromJust (Env.lookup "?b" env)
--                    --getField name fields
--
--        Just prim ->
--            case Env.lookup prim primEnv of
--                Just fun -> do
--                    pure (PrimFunX prim fun [])
--                Nothing -> do
--                    throwError ("No primitive function " <> prim)
--
--        _ | ";pack" == var ->
--            closureX "?a" $ do
--                env <- ask
--                x <- fromJust (Env.lookup "?a" env)
--                let ValueX (TBig n) = x
--                pure (ValueX (TNat (max 0 n)))
--
--        _ | ";unpack" == var ->
--            closureX "?a" $ do
--                env <- ask
--                x <- fromJust (Env.lookup "?a" env)
--                let (ValueX (TNat n)) = x
--                pure (ValueX (TBig n))
--
--        _ | "zero" == var ->
--            pure (ValueX (TNat 0))
--
--        Nothing -> do
--            env <- ask
--            case Env.lookup var env of
--                Just value -> do
--                    value
--                _ ->
--                    if isConstructor var
--                        then pure (DataX var [])
--                        else 
--                            throwError ("Unbound identifier '" <> var <> "'")
--
--evalAppX
--  :: (MonadError Text m, MonadReader (ValueEnvX m) m)
--  => m (ValueX m)
--  -> m (ValueX m)
--  -> m (ValueX m)
--evalAppX fun arg = do
--    f <- fun
--    --traceShowM (">> " <> show f)
--    case f of
--        ClosureX var body closure -> do
--            env <- ask
--
--            let env0 = Env.insert var arg (closure <> env)  -- (Env.insert var arg closure <> env) ???
--            env1 <- traverse sequence (Env.toList env0)
--
--            local (const $ Env.fromList (pure <$$> env1)) body
--
--            --local (\env -> runEvalX $ boos var arg closure env) body
--
--        PrimFunX name fun args -> do
--            evalPrimX name fun args
--            --if arity fun == length args + 1
--            --    then do
--            --        let unValue (ValueX p) = p
--            --        xs <- fmap unValue . reverse <$> sequence (arg:args)
--            --        pure (ValueX (applyFun fun xs))
--            --    else
--            --        let unValue (ValueX p) = p
--            --        xs <- fmap unValue . reverse <$> sequence (arg:args)
--            --        pure (ValueX (applyFun fun xs))
--            --    else
----                    pure (PrimFunX name fun (arg:args))
--
--        DataX "succ" args -> do
--            a <- arg
--            pure $ case a of
--                ValueX (TNat n) -> ValueX (TNat (succ n))
--                _               -> DataX "succ" (args <> [a])
--
--        DataX con args -> do
--            a <- arg
--            pure (DataX con (args <> [a]))
--
--        v -> do
--            traceShowM v
--            error "??"
--
--
----            let unValue (ValueX p) = p
----            xs <- fmap unValue . reverse <$> sequence (arg:args)
----            pure (ValueX (applyFun fun xs))
----
----            --    else 
----            --        pure (PrimFunX name fun (arg:args))
----
----        _ -> do
----            traceShowM "&&&&&&&&&"
----            traceShowM f
----            undefined
--
--evalPrimX
--  :: (MonadError Text m, MonadReader (ValueEnvX m) m)
--  => Name
--  -> Fun
--  -> [m (ValueX m)]
--  -> m (ValueX m)
--evalPrimX name fun args
--    | arity fun == length args = do
--        one <- sequence args
--        two <- traverse literal (reverse one)
--        pure (ValueX (applyFun fun two))
--        -- ValueX . applyFun fun <$> traverse literal (reverse args)
--    | otherwise =
--        pure (PrimFunX name fun args)
--  where
--    literal (ValueX lit) = pure lit
--    literal _           = throwError "Runtime error (evalPrim)"
--
--            --if arity fun == length args + 1
--            --    then do
--            --        let unValue (ValueX p) = p
--            --        xs <- fmap unValue . reverse <$> sequence (arg:args)
--            --        pure (ValueX (applyFun fun xs))
--            --    else
--            --        let unValue (ValueX p) = p
--            --        xs <- fmap unValue . reverse <$> sequence (arg:args)
--            --        pure (ValueX (applyFun fun xs))
--            --    else
--
--
--isCatchAll :: [Name] -> Bool
--isCatchAll = (== ["$_"])
--
--evalPatX 
--  :: (MonadError Text m, MonadReader (ValueEnvX m) m) 
--  => m (ValueX m) 
--  -> CMatrix (m (ValueX m)) 
--  -> m (ValueX m)
--evalPatX val = \case
--
--    [] -> throwError "Implementation error (evalPat)"
--    [(c, e)] | isCatchAll c -> e
--
--    ((ps@[p, _, _], e):_) | isRowCon p -> do
--        env <- evalRowPatX ps val 
--        local env e
--
--    ((p:ps, e):eqs) ->
--        val >>= \case
--
--            ValueX (TNat m) | 0 /= m && p == "succ" ->
--                local (Env.insert (head ps) (pure (ValueX (TNat (pred m))))) e
--
--            ValueX (TNat 0) | p == "zero" ->
--                e
--        
--            DataX con args | p == con ->
--                --local (Env.inserts (zip ps args)) e
--                local (Env.inserts (zip ps (pure <$> args))) e
--
--            _ -> do
----                traceShowM "evalPatX"
--                evalPatX val eqs 
--
--evalRowPatX :: (Monad m, MonadError Text m) => [Name] -> m (ValueX m) -> m (Env (m (ValueX m)) -> Env (m (ValueX m)))
--evalRowPatX [p, q, r] val = do
--    pmap <- toMapX val mempty
--    case Map.lookup p pmap of
--        Nothing    -> throwError "Runtime error (evalPat)"
--        Just (v:_) -> pure (Env.inserts [(q, v), (r, fromMapX (Map.delete p pmap))])
--
--toMapX :: (Monad m, MonadError Text m) => m (ValueX m) -> Map Name [m (ValueX m)] -> m (Map Name [m (ValueX m)])
--toMapX zz m = zz >>= \case
--    DataX "{}" []    -> pure m
--    DataX lab (v:vs) -> foldrM toMapX (Map.insertWith (<>) lab [pure v] m) (pure <$> vs)
--
----fromMapX :: (MonadFail m) => Map Name [m (ValueX m)] -> m (ValueX m)
--fromMapX m = foldrM foo (DataX "{}" []) (Map.toList m) -- Map.foldrWithKey foo (Data "{}" []) m
--  where
--    foo (k, w) zz = foldrM zoo zz w -- foldrM (\v m -> pure (Data k [v, m])) w
--      where
--        zoo v m = do
--            vv <- v
--            pure (DataX k [vv, m])
--
--
--
---- =======================================================================================
---- =======================================================================================
---- =======================================================================================


--type ValueEnv m = Env (Value m)
type ValueEnv m = Env (m (Value m))

-- | An expression evaluates to a literal value, a fully applied data
-- constructor, a primitive function, or a closure.
data Value m
    = Value Prim
    | Data Name [Value m]
    | PrimFun Name Fun [Value m]
    | Closure Name (m (Value m)) (ValueEnv m)

instance Show (Value m) where
    show (Value lit)           = "Value "   <> "(" <> show lit <> ")"
    show (Data name lit)       = "Data "    <> show name <> " " <> show lit
    show (PrimFun name _ args) = "PrimFun " <> show name <> " " <> show args
    show Closure{}             = "<<function>>"

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
    , MonadFix
    , MonadReader (ValueEnv Eval) )

runEval :: Eval a -> ValueEnv Eval -> Maybe a
runEval = runReaderT . unEval

evalExpr :: Core -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runEval . eval

--foo 
--  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m)
--  => Name 
--  -> m (Value m)
--  -> m (Value m)
--foo = closure 

--gork 
--  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m)
--  => Value m
--  -> Value m
--gork val = 
--    undefined
--  where
----    zopp :: m (Value m)
--    zopp = closure "_" (pure val)

foo 
  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m)
  => Name 
  -> m (Value m)
  -> m (Value m) 
  -> m (Value m)
foo var val x = do
    a <- val
    local (\env -> Env.insert var (pure a) env) x

eval
  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m)
  => Core
  -> m (Value m)
eval = cata $ \case

    CVar var    -> evalVar var
    CLit lit    -> pure (Value lit)
    CApp exs    -> foldl1 evalApp exs
    CLam var e1 -> asks (Closure var e1)

    CLet var e1 e2 -> do
        e <- e1
        local (Env.insert var (pure e)) e2
        --val <- mfix (foo var) e1 --(\val -> local (\env -> Env.insert var val env)) e1)
        --local (Env.insert var (pure val)) e2

    CIf e1 e2 e3 -> do
        Value (TBool isTrue) <- e1
        if isTrue then e2 else e3

    CPat expr clauses ->
        evalPat clauses expr 

--eval
--  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m)
--  => Core
--  -> m (Value m)
--eval = cata $ \case
--
--    CVar var    -> evalVar var
--    CLit lit    -> pure (Value lit)
--    CApp exs    -> foldl1 evalApp exs
--    CLam var e1 -> asks (Closure var e1)
--
--    CLet var e1 e2 -> do
--        val <- e1
----        val <- mfix (\val -> local (Env.insert var (gork val)) e1)
--        local (Env.insert var val) e2
--
--    CIf e1 e2 e3 -> do
--        Value (TBool isTrue) <- e1
--        if isTrue then e2 else e3
--
--    CPat expr clauses ->
--        expr >>= evalPat clauses

getField :: (Monad m) => Name -> [Value m] -> m (Value m)
getField name [Data f (v:fs)]
    | f == ("{" <> name <> "}") = pure v
    | otherwise                 = getField name fs

closure :: (MonadReader (ValueEnv m) m) => Name -> m (Value m) -> m (Value m)
closure var a = pure (Closure var a mempty)

-- TODO: DRY
-- toLowerInitial
withInitialLower_ :: Name -> Name
withInitialLower_ name = toLower (Text.head name) `Text.cons` Text.tail name

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar var =
    case Text.stripPrefix "@" var of
        Just "(!).getField" ->
            closure "?a" $ do
                env <- ask
                Value (TSymbol name) <- fromJust (Env.lookup "?a" env)
                closure "?b" $ do
                    env <- ask
                    Data "!" fields <- fromJust (Env.lookup "?b" env)
                    Closure v body cl <- getField (withInitialLower_ name) fields
                    local (Env.insert v (pure (Value TUnit)) . (cl <>)) body

        Just "(#).getField" ->
            closure "?a" $ do
                env <- ask
                Value (TSymbol name) <- fromJust (Env.lookup "?a" env)
                closure "?b" $ do
                    env <- ask
                    Data "#" fields <- fromJust (Env.lookup "?b" env)
                    getField name fields

        Just prim -> do
            case Env.lookup prim primEnv of
                Just fun ->
                    evalPrim prim fun []
                Nothing -> do
                    traceShowM ("No primitive function " <> Text.unpack prim)
                    fail ("No primitive function " <> Text.unpack prim)
                    --pure (Fail ("No primitive function " <> Text.unpack prim))

        _ | ";pack" == var ->
            closure "?a" $ do
                env <- ask
                Value (TBig n) <- fromJust (Env.lookup "?a" env)
                pure (Value (TNat (max 0 n)))

        _ | ";unpack" == var ->
            closure "?a" $ do
                env <- ask
                Value (TNat n) <- fromJust (Env.lookup "?a" env)
                pure (Value (TBig n))

        _ | "zero" == var ->
            pure (Value (TNat 0))

        _ ->
            asks (Env.lookup var) >>= \case
                Just value ->
                    value
                Nothing ->
                    if isConstructor var
                        then pure (Data var [])
                        else do
                            traceShowM ("Unbound identifier " <> var)
                            fail ("Unbound identifier '" <> unpack var <> "'")
                            --pure (Fail ("Unbound identifier '" <> unpack var <> "'"))

--evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
--evalVar var =
--    case Text.stripPrefix "@" var of
--        Just "(!).getField" ->
--            closure "?a" $ do
--                Just (Value (TSymbol name)) <- asks (Env.lookup "?a")
--                closure "?b" $ do
--                    Just (Data "!" fields) <- asks (Env.lookup "?b")
--                    Closure var body _ <- getField (withInitialLower_ name) fields
--                    local (Env.insert var (Value TUnit)) body
--
--        Just "(#).getField" ->
--            closure "?a" $ do
--                Just (Value (TSymbol name)) <- asks (Env.lookup "?a")
--                closure "?b" $ do
--                    Just (Data "#" fields) <- asks (Env.lookup "?b")
--                    getField name fields
--
--        Just prim -> do
--            case Env.lookup prim primEnv of
--                Just fun ->
--                    evalPrim prim fun []
--                Nothing -> do
--                    traceShowM ("No primitive function " <> Text.unpack prim)
--                    fail ("No primitive function " <> Text.unpack prim)
--                    --pure (Fail ("No primitive function " <> Text.unpack prim))
--
--        _ | ";pack" == var ->
--            closure "?a" $ do
--                Just (Value (TBig n)) <- asks (Env.lookup "?a")
--                pure (Value (TNat (max 0 n)))
--
--        _ | ";unpack" == var ->
--            closure "?a" $ do
--                Just (Value (TNat n)) <- asks (Env.lookup "?a")
--                pure (Value (TBig n))
--
--        _ | "zero" == var ->
--            pure (Value (TNat 0))
--
--        _ ->
--            asks (Env.lookup var) >>= \case
--                Just value ->
--                    pure value
--                Nothing ->
--                    if isConstructor var
--                        then pure (Data var [])
--                        else do
--                            traceShowM ("Unbound identifier " <> var)
--                            fail ("Unbound identifier '" <> unpack var <> "'")
--                            --pure (Fail ("Unbound identifier '" <> unpack var <> "'"))

-- TODO
isConstructor :: Name -> Bool
isConstructor var
    | "succ" == var   = True
    | "succ'" == var  = True
    | "zero" == var   = True
    | "zero'" == var  = True
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
    | "!" == var      = True
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

evalApp
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = do
    val <- arg
    fun >>= \case 

        Closure var body closure -> 
            local (Env.insert var (pure val) . (closure <>)) body

    --        env <- ask
    --
    --        let env0 = Env.insert var arg (closure <> env)  -- (Env.insert var arg closure <> env) ???
    --        env1 <- traverse sequence (Env.toList env0)
    --
    --        local (const $ Env.fromList (pure <$$> env1)) body

        PrimFun name fun args -> 
            evalPrim name fun (val:args)

        Data "succ" args ->
            pure $ case val of
                Value (TNat n) -> Value (TNat (succ n))
                _              -> Data "succ" (args <> [val])

        Data con args -> 
            pure (Data con (args <> [val]))

        err ->
            pure err

--evalApp
--  :: (MonadFail m, MonadReader (ValueEnv m) m)
--  => m (Value m)
--  -> m (Value m)
--  -> m (Value m)
--evalApp fun arg = fun >>= \case
--
--    Closure var body closure -> do
--        val <- arg
--        local (Env.insert var val closure <>) body
--
--    PrimFun name fun args -> do
--        val <- arg
--        evalPrim name fun (val:args)
--
--    Data "succ" args -> do
--        --(Value (TNat n)) <- arg
--        a <- arg
--        case a of
--            Value (TNat n) ->
--                pure (Value (TNat (succ n)))
--            _ ->
--                pure (Data "succ" (args <> [a]))
--
--        --pure (Data "succ" (args <> [a]))
----        pure (Value (TNat (succ n)))
--
----        --Value (TNat n) <- arg
----        pure (Value (TNat 5))
--
--    Data con args -> do
--        a <- arg
--        pure (Data con (args <> [a]))
--
--    err ->
--        pure err


--evalRowPat :: (MonadFail m) => [Name] -> Value m -> m (Env (Value m) -> Env (Value m))

evalPat :: (MonadFail m, MonadReader (ValueEnv m) m) => CMatrix (m (Value m)) -> m (Value m) -> m (Value m)
evalPat []            _ = fail "Runtime error (evalPat)"
evalPat [(["$_"], e)] _ = e
evalPat ((ps@[p, _, _], e):_) val
    | isRowCon p = evalRowPat ps val >>= flip local e
evalPat ((p:ps, e):eqs) val =
    val >>= \case

        Value (TNat m) | 0 /= m && p == "succ" ->
            local (Env.insert (head ps) (pure (Value (TNat (pred m))))) e

        Value (TNat 0) | p == "zero" ->
            e

        Data con args | p == con ->
            local (Env.inserts (zip ps (pure <$> args))) e

        _ ->
            evalPat eqs val


--evalPat :: (MonadFail m, MonadReader (ValueEnv m) m) => CMatrix (m (Value m)) -> Value m -> m (Value m)
--evalPat []            _ = fail "Runtime error (evalPat)"
--evalPat [(["$_"], e)] _ = e
--evalPat ((ps@[p, _, _], e):_) val
--    | isRowCon p = do -- evalRowPat ps val >>= flip local e
--        xxx <- evalRowPat ps val
--        local undefined e
--evalPat ((p:ps, e):eqs) val =
--    case val of
--        Value (TNat m) | 0 /= m && p == "succ" ->
--            undefined -- local (Env.insert (head ps) (Value (TNat (pred m)))) e
--        Value (TNat 0) | p == "zero" ->
--            e
--        Data con args | p == con ->
--            undefined
--            -- local (Env.inserts (zip ps args)) e
--        _ ->
--            evalPat eqs val


--evalPat :: (MonadFail m, MonadReader (ValueEnv m) m) => CMatrix (m (Value m)) -> Value m -> m (Value m)
--evalPat []            _ = fail "Runtime error (evalPat)"
--evalPat [(["$_"], e)] _ = e
--evalPat ((ps@[p, _, _], e):_) val
--    | isRowCon p = evalRowPat ps val >>= flip local e
--evalPat ((p:ps, e):eqs) val =
--    case val of
--        Value (TNat m) | 0 /= m && p == "succ" ->
--            local (Env.insert (head ps) (Value (TNat (pred m)))) e
--        Value (TNat 0) | p == "zero" ->
--            e
--        Data con args | p == con ->
--            local (Env.inserts (zip ps args)) e
--        _ ->
--            evalPat eqs val

isRowCon :: Name -> Bool
isRowCon ""  = False
isRowCon con = Text.head con == '{' && Text.last con == '}'

--evalRowPat :: (MonadFail m) => [Name] -> Value m -> m (Env (Value m) -> Env (Value m))
--evalRowPat [p, q, r] val =
--    case Map.lookup p pmap of
--        Nothing    -> fail "Runtime error (evalPat)"
--        Just (v:_) -> pure (Env.inserts [(q, v), (r, fromMap (Map.delete p pmap))])
--  where
--    pmap = toMap val mempty

evalRowPat :: (MonadFail m) => [Name] -> m (Value m) -> m (Env (m (Value m)) -> Env (m (Value m)))
evalRowPat [p, q, r] val = do
    pmap <- toMap val mempty
    case Map.lookup p pmap of
        Nothing    -> fail "Runtime error (evalPat)"
        Just (v:_) -> pure (Env.inserts [(q, v), (r, fromMap (Map.delete p pmap))])

toMap :: (MonadFail m) => m (Value m) -> Map Name [m (Value m)] -> m (Map Name [m (Value m)])
toMap zz m = zz >>= \case

    Data "{}" []    -> pure m
    Data lab (v:vs) -> foldrM toMap (Map.insertWith (<>) lab [pure v] m) (pure <$> vs)

fromMap :: (MonadFail m) => Map Name [m (Value m)] -> m (Value m)
fromMap m = foldrM foo (Data "{}" []) (Map.toList m) -- Map.foldrWithKey foo (Data "{}" []) m
  where
    foo (k, w) zz = foldrM zoo zz w -- foldrM (\v m -> pure (Data k [v, m])) w
      where
        zoo v m = do
            vv <- v
            pure (Data k [vv, m])


--toMap :: Value m -> Map Name [Value m] -> Map Name [Value m]
--toMap (Data "{}" [])    m = m
--toMap (Data lab (v:vs)) m = foldr toMap (Map.insertWith (<>) lab [v] m) vs
--
--fromMap :: Map Name [Value m] -> Value m
--fromMap = Map.foldrWithKey (\k -> flip (foldr (\v m -> Data k [v, m]))) (Data "{}" [])
