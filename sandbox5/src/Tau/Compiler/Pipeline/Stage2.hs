{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage2 where

import Control.Monad.Except 
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Supply
import Data.Either (fromRight)
import Data.Foldable (foldlM, foldrM)
import Data.List (nub, tails, partition, find, groupBy)
import Data.Maybe (fromMaybe, fromJust)
import Data.Map (Map)
import Data.Tuple.Extra (first, second)
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Env (Env)
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tooling
import Tau.Type
import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Env as Env

type WorkingExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

runTranslate 
  :: ClassEnv 
  -> TypeEnv 
  -> KindEnv 
  -> ConstructorEnv 
  -> ReaderT (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) (Supply Name) e 
  -> e
runTranslate classEnv typeEnv kindEnv constructorEnv expr = 
    fromJust (evalSupply (runReaderT expr env) (numSupply "$dict"))
  where
    env = (classEnv, typeEnv, kindEnv, constructorEnv)

translate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [Error] (Maybe Type))
  -> m (WorkingExpr (Maybe Type))
translate expr = evalStateT (expandTypeClasses =<< translateLiterals expr) mempty

translateLiterals 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [e] (Maybe Type))
  -> StateT (Env [(Name, Name)]) m (WorkingExpr (TypeInfoT [e] (Maybe Type)))
translateLiterals = cata $ \case

    ELit t (TInt n) -> 
        pure (appExpr t 
            [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
            , litExpr (TypeInfo [] (Just tInteger) []) (TInteger (fromIntegral n)) ])

    ELit t (TInteger n) -> 
        pure (appExpr t 
            [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
            , litExpr (TypeInfo [] (Just tInteger) []) (TInteger (fromIntegral n)) ])

    -- TODO: FLoat, Double, etc.

    ELit    t prim       -> pure (litExpr t prim)
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
    ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2

expandTypeClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [e] (Maybe Type))
  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
expandTypeClasses expr = do -- insertArgsExpr <$> run expr <*> (nub . snd <$> getAndReset)
    e <- run expr
    s <- getAndReset
    insertArgsExpr e s

    -- insertArgsExpr <$> run expr <*> getAndReset

  where
    run = cata $ \case
        ELet t bind@BFun{} expr1 expr2 -> do
            e1 <- expr1
            vs <- getAndReset -- undefined -- nub . snd <$> getAndReset
            (xx, yy) <- insertArgsBinding (translateBinding bind) e1 vs
            letExpr (nodeType t) xx yy <$> expr2

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            vs <- getAndReset -- undefined -- nub . snd <$> getAndReset
            xx <- insertArgsExpr e1 vs
            letExpr (nodeType t) (translateBinding pat) xx <$> expr2

        EFix t var expr1 expr2 -> do
            e1 <- expr1
            vs <- getAndReset -- undefined -- nub . snd <$> getAndReset
            xx <- insertArgsExpr e1 vs
            fixExpr (nodeType t) var xx <$> expr2

        EVar t var -> do
            --classEnv <- askClassEnv
            --reduce2 classEnv (nodePredicates t) >>= \case
            --    Left  _  -> undefined   -- TODO
            --    Right ps -> do
            --        foldlM applyDicts (varExpr (nodeType t) var) (tails (reverse ps))

            let (xs, ys) = partition (isVar . predicateType) (nodePredicates t)

            let zmap = foldr (\(InClass n t) -> Map.insertWith (<>) t [n]) mempty ys
            classEnv <- askClassEnv
            zmap2 <- traverse (reduceSet classEnv) zmap

            let yys = Map.foldrWithKey (\k v vs -> [InClass vv k | vv <- v] <> vs) [] zmap2

            --let foo = groupBy (\a b -> predicateType a == predicateType b) ys

            --let fn2 (x:xs) = undefined

            --let zoo = fn2 <$> foo


            --classEnv <- askClassEnv
            --yys <- reduce classEnv ys
            --traceShowM ys
            --traceShowM yys
            --traceShowM "=============="
            --traceShowM "=============="

            baz1 <- foldlM applyXx1 (varExpr (nodeType t) var) (tails yys) -- (tails (reverse (nodePredicates t)))

            classEnv <- askClassEnv
            xxs <- fromRight (error "impl") <$> reduce classEnv xs  

            foldlM applyXx2 baz1 (tails xxs)
            --pure baz1

--            foldlM applyDicts (varExpr (nodeType t) var) (tails (reverse (nodePredicates t)))

        ELit   t lit       -> pure (litExpr (nodeType t) lit)
        ECon   t con es    -> conExpr (nodeType t) con <$> sequence es
        EApp   t es        -> appExpr (nodeType t) <$> sequence es
        ELam   t ps e      -> lamExpr (nodeType t) (translatePatterns <$> ps) <$> e
        EIf    t e1 e2 e3  -> ifExpr  (nodeType t) <$> e1 <*> e2 <*> e3
        EPat   t expr cs   -> patExpr (nodeType t) <$> expr <*> (translateClauses <$$> traverse sequence cs)

    translateClauses = \case
        SimplifiedClause t ps g -> 
            SimplifiedClause (nodeType t) (translatePatterns <$> ps) g

    translateBinding = \case
        BPat t p           -> BPat (nodeType t) (translatePatterns p)
        BFun t name ps     -> BFun (nodeType t) name (translatePatterns <$> ps)

    translatePatterns = cata $ \case
        PVar    t var      -> varPat   (nodeType t) var
        PCon    t con ps   -> conPat   (nodeType t) con ps
        PAs     t as p     -> asPat    (nodeType t) as p
        PLit    t prim     -> litPat   (nodeType t) prim
        PAny    t          -> anyPat   (nodeType t)
        POr     t p q      -> orPat    (nodeType t) p q
        PTuple  t ps       -> tuplePat (nodeType t) ps
        PList   t ps       -> listPat  (nodeType t) ps
        PRow    t lab p q  -> rowPat   (nodeType t) lab p q 

-- a0 => [(Eq, $dict1), (Show, $dict2)]
-- a1 => [(Eq, $dict3)]

insertArgsExpr 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (Maybe Type) 
  -> Env [(Name, Name)] 
  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
insertArgsExpr expr = foldrM fun expr . Env.toList 
  where
    fun 
      :: ( MonadSupply Name m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
      => (Name, [(Name, Name)]) 
      -> WorkingExpr (Maybe Type) 
      -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
    fun (var, vs) e = do
        classEnv <- askClassEnv
        set1 <- reduceSet classEnv (fst <$> vs)
        let set2 = [(x, b) | (a, b) <- vs, x <- super1 classEnv a, a `elem` set1]
--      traceShowM set1
--      traceShowM set2
--      traceShowM vs
--      traceShowM "==============="
--      traceShowM "==============="
        pure (foldr (fun2 set1 set2) e vs)

          where
            --fun2 
            --  :: (Name, Name) 
            --  -> WorkingExpr (Maybe Type) 
            --  -> WorkingExpr (Maybe Type)
            fun2 set1 set2 (name, dv) e = do

                --traceShow "^^^^^^^^^^^^^^^^^^" $
                --traceShow (pretty (typeOf <$> (workingExprTag e))) $
                --traceShow var $

                --case typeOf <$> (workingExprTag e) of
                --    Just x -> undefined
                --    Nothing -> undefined

                let
                    fnx t = var `elem` (fst <$> free t)

                -- TODO
                if Just False == (fnx . typeOf <$> (workingExprTag e))
                    then error "Ambiguity"
                    else if name `elem` set1
                              then do
                                  let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
                                  lamExpr (tArr <$> Just ty <*> workingExprTag e) 
                                          [varPat (Just ty) dv] e
                              else 
                                  replaceVar dv (fromJust (lookup name set2)) e

--              case ty of
--                  Fix (TApp _ _ (Fix TVar{})) -> 
--                      lamExpr (tArr <$> Just ty <*> workingExprTag e) 
--                              [varPat (Just ty) var] e


--insertArgsExpr expr = foldr fun expr . Env.toList 
--  where
--    fun :: (Name, [(Name, Name)]) -> WorkingExpr (Maybe Type) -> WorkingExpr (Maybe Type)
--    fun (var, vs) e = foldr fun2 e vs
--      where
--        set1 = undefined
--        set2 = undefined
--
--        fun2 :: (Name, Name) -> WorkingExpr (Maybe Type) -> WorkingExpr (Maybe Type)
--        fun2 (name, dv) e = do
--            let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
--            lamExpr (tArr <$> Just ty <*> workingExprTag e) 
--                    [varPat (Just ty) dv] e

--            case ty of
--                Fix (TApp _ _ (Fix TVar{})) -> 
--                    lamExpr (tArr <$> Just ty <*> workingExprTag e) 
--                            [varPat (Just ty) var] e


--insertArgsExpr :: WorkingExpr (Maybe Type) -> [(Name, Type)] -> WorkingExpr (Maybe Type)
--insertArgsExpr = foldr fun 
--  where
--    --fun (var, ty) e = 
--    --    lamExpr (tArr <$> Just ty <*> workingExprTag e) 
--    --            [varPat (Just ty) var] e
--
--    fun (var, ty) e = 
--        case ty of
--            Fix (TApp _ _ (Fix TVar{})) -> 
--                lamExpr (tArr <$> Just ty <*> workingExprTag e) 
--                        [varPat (Just ty) var] e
--            _ -> e

insertArgsBinding 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => ProgBinding (Maybe Type) 
  -> WorkingExpr (Maybe Type) 
  -> Env [(Name, Name)] 
  -> StateT (Env [(Name, Name)]) m (ProgBinding (Maybe Type), WorkingExpr (Maybe Type))
insertArgsBinding (BFun t name ps) expr env = do
    (t', ps', e) <- foldrM fun (t, ps, expr) (Env.toList env)
    pure (BFun t' name ps', e)
  where
    fun 
      :: ( MonadSupply Name m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
      => (Name, [(Name, Name)]) 
      -> (Maybe Type, [ProgPattern (Maybe Type)], WorkingExpr (Maybe Type)) 
      -> StateT (Env [(Name, Name)]) m (Maybe Type, [ProgPattern (Maybe Type)], WorkingExpr (Maybe Type))
    fun (var, vs) x = do
        classEnv <- askClassEnv
        set1 <- reduceSet classEnv (fst <$> vs)
        let set2 = [(x, b) | (a, b) <- vs, x <- super1 classEnv a, a `elem` set1]
        pure (foldr (fun2 set1 set2) x vs)
      where
--        fun2 
--          :: (Name, Name) 
--          -> (Maybe Type, [ProgPattern (Maybe Type)], WorkingExpr (Maybe Type)) 
--          -> (Maybe Type, [ProgPattern (Maybe Type)], WorkingExpr (Maybe Type))
        fun2 set1 set2 (name, dv) (t, ps, x) = do

            let
                fnx t = var `elem` (fst <$> free t)

            -- TODO
            if Just False == (fnx . typeOf <$> (workingExprTag x))
                then error "Ambiguity"
                else if name `elem` set1
                          then do
                              let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
                              (tArr ty <$> t, varPat (Just ty) dv:ps, x)
                          else 
                              (t, ps, replaceVar dv (fromJust (lookup name set2)) x)

replaceVar
  :: Name 
  -> Name
  -> WorkingExpr t
  -> WorkingExpr t
replaceVar from to = cata $ \case
    EVar t var | from == var -> varExpr t to
    e                       -> embed e

--insertArgsBinding (BFun t name ps) env = BFun t' name ps'
--  where
--    (t', ps') = foldr fun (t, ps) (Env.toList env)
--
--    fun :: (Name, [(Name, Name)]) -> (Maybe Type, [ProgPattern (Maybe Type)]) -> (Maybe Type, [ProgPattern (Maybe Type)])
--    fun (var, vs) e = foldr fun2 e vs
--      where
--        fun2 :: (Name, Name) -> (Maybe Type, [ProgPattern (Maybe Type)]) -> (Maybe Type, [ProgPattern (Maybe Type)])
--        fun2 (name, dv) (t, ps) = do
--            let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
--            (tArr ty <$> t, varPat (Just ty) var:ps)

--insertArgsBinding :: ProgBinding (Maybe Type) -> [(Name, Type)] -> ProgBinding (Maybe Type)
--insertArgsBinding (BFun t name ps) vs = BFun t' name ps'
--  where
--    (t', ps') = foldr fun (t, ps) vs
----    fun (var, ty) (t, ps) = (tArr ty <$> t, varPat (Just ty) var:ps)
--
--    fun (var, ty) (t, ps) = 
--        case ty of
--            Fix (TApp _ _ (Fix TVar{})) -> 
--                (tArr ty <$> t, varPat (Just ty) var:ps)
--            _ -> 
--                (t, ps)

----dictTVar :: (MonadSupply Name m) => Type -> StateT ([Predicate], [(Name, Type)]) m Name
--dictTVar xx ty = do
--    (_, map) <- get
--    case filter ((==) ty . snd) map of
--        p:_ -> pure (fst p)
--        _   -> do 
--            var <- supply
--            --modify ((var, ty) :)
--            modify (\(x1, x2) -> (xx:x1, (var, ty):x2))
--            pure var

applyXx1
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (Maybe Type)
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
applyXx1 e [] = pure e
applyXx1 expr (InClass name ty:ps) = do
    map <- allMethods
    case project expr of
        EVar t var -> 
            -- Is this a member function of the class?
            case lookup var map of
                Just e -> 
                    pure e
                Nothing -> 
                    pure (appExpr zz1
                        [ setWorkingExprTag (yy (InClass name ty) zz1) expr
                        , buildDict map ])
        _ -> 
            pure (appExpr (cod <$> workingExprTag expr) -- TODO
                [ expr -- setWorkingExprTag (Just (tCon kTyp "Xxx")) expr
                , buildDict map ])
  where
    cod (Fix (TArr _ t)) = t
    zz1 = foldr yy (workingExprTag expr) ps
    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz

    buildDict map = 
        conExpr (Just (tApp kTyp (tCon kFun name) ty)) "#" 
            [foldr fn (conExpr (Just tRowNil) "{}" []) map]
      where
        fn (name, expr) e = 
            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
             in rowExprCons row name expr e

    allMethods = do
        env <- askClassEnv
        fromRight (error ("No instance " <> show name <> " " <> show ty))   -- TODO
            <$> runExceptT (lookupAllClassMethods name ty env)
                >>= traverse (secondM translateMethod) 

    translateMethod = translate
        . Stage1.translate 
        . getAst 
        . fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)

--dictTVar xx ty = do
--    (_, map) <- get
--    case filter ((==) ty . snd) map of
--        p:_ -> pure (fst p)
--        _   -> do 
--            var <- supply
--            --modify ((var, ty) :)
--            modify (\(x1, x2) -> (xx:x1, (var, ty):x2))
--            pure var

-- a0 => "Eq" => ("$dict1", Eq a0)

--xxx 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
----  => (Env (Env Name) -> Env (Env Name))
--  => StateT (Env (Env Name)) m Name
--xxx = undefined

--xxx
--  :: Name
--  -> Name
--  -> Name
--  -> Env (Env Name) 
--  -> Env (Env Name)
--xxx var name dv = Env.alter f1 var
--  where
--    f1 :: Maybe (Env Name) -> Maybe (Env Name)
--    f1 Nothing = Just $ Env.fromList [(name, dv)]
--    f1 (Just env) = undefined
--
--    f2 :: Maybe Name -> Maybe Name
--    f2 = undefined

--xxx
--  :: Name
--  -> Name
--  -> Name
--  -> Env [(Name, Name)]
--  -> Env [(Name, Name)]
--xxx name dv = 

dictTVar2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Name
  -> TypeF Kind a Type
  -> StateT (Env [(Name, Name)]) m Name
dictTVar2 name (TVar _ var) = do
    info <- get
    classEnv <- askClassEnv
    maybe fresh pure (lookupVar info classEnv)
  where
    fresh = do
        dv <- supply
        modify (Env.alter (\vs -> Just $ (name, dv):fromMaybe [] vs) var)
        pure dv

    lookupVar info classEnv = do
        varEnv <- Env.lookup var info 
        snd <$> find (elem name . fst) (first (super1 classEnv) <$> varEnv)
        --varEnv <- Env.toList <$> Env.lookup var info 

applyXx2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (Maybe Type)
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
applyXx2 e [] = pure e
applyXx2 expr (InClass name ty:ps) = do
    tv <- dictTVar2 name (project ty) -- dictTVar (InClass name ty) (tApp kTyp (tCon kFun name) ty)
    let t1 = tApp kTyp (tCon kFun name) ty
--    traceShowM ">>>>>>>>>>>>>>>"
--    xx <- get
--    traceShowM (pretty xx)
--    traceShowM ">>>>>>>>>>>>>>>"
    case project expr of
        EVar t var -> do
            --tv  <- dictTVar (InClass name ty) (tApp kTyp (tCon kFun name) ty)
            all <- baz 
            let getType t = tAtom `tArr` t1 `tArr` t
            if var `elem` (fst <$> all) 
                then do
                    pure (appExpr (workingExprTag expr)
                        [ varExpr (getType <$> workingExprTag expr) "@#getField"
                        , litExpr (Just tAtom) (TAtom var) 
                        , varExpr (Just t1) tv 
                        ])
                else pure (appExpr zz1
                        [ setWorkingExprTag (yy (InClass name ty) zz1) expr
                        , varExpr (Just t1) tv 
                        ])
        _ -> do
            --tv  <- dictTVar (InClass name ty) (tApp kTyp (tCon kFun name) ty)
            --let t1 = tApp kTyp (tCon kFun name) ty
            pure (appExpr (cod <$> zz1)
                        [ expr
                        , varExpr (Just t1) tv ])
  where
    cod (Fix (TArr _ t)) = t
    zz1 = foldr yy (workingExprTag expr) ps
    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz

    baz = do
        env <- askClassEnv
        fromRight (error ("No class " <> show name))   -- TODO
            <$> runExceptT (lookupAllClassX name env)


--applyDicts
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (Maybe Type)
--  -> [Predicate]
--  -> StateT ([Predicate], [(Name, Type)]) m (WorkingExpr (Maybe Type))
--applyDicts e [] = pure e
--applyDicts expr (InClass name ty:ps) = do
--  
----    let t1 = tApp kTyp (tCon kFun name) ty    -- Dictionary type, e.g., Num Int
--
----    classEnv <- askClassEnv
----    ps <- fst <$> get
----
----    traceShowM "vvvvvvvvvvvvvvvvvvvvvv"
----    traceShowM (InClass name ty)
----    traceShowM ps
----    traceShowM "^^^^^^^^^^^^^^^^^^^^^^"
----
----    foo <- runExceptT (entail classEnv ps (InClass name ty))
----    case foo of
----        Right True -> 
----            pure expr
----        _ -> 
--            case project expr of
--                EVar t var 
--                    | isVar ty -> do
--
--                        tv  <- dictTVar (InClass name ty) (tApp kTyp (tCon kFun name) ty)
--
----                        traceShowM "++++++++++++++++"
----                        traceShowM name
----                        traceShowM ty
----                        traceShowM "++++++++++++++++"
--        
--                        all <- baz 
--                        let t1 = tApp kTyp (tCon kFun name) ty
--                            getType t = tAtom `tArr` t1 `tArr` t
--                        if var `elem` (fst <$> all) 
--                            then do
--                                pure (appExpr (workingExprTag expr)
--                                    [ varExpr (getType <$> workingExprTag expr) "@#getField"
--                                    , litExpr (Just tAtom) (TAtom var) 
--                                    , varExpr (Just t1) tv 
--                                    ])
--                            else pure (appExpr zz1
--                                    [ setWorkingExprTag (yy (InClass name ty) zz1) expr
--                                    , varExpr (Just t1) tv ])
--        
--                    | otherwise -> do
--                        map <- baz2 
--                        -- Is this a member function of the class?
--                        case lookup var map of
--                            Just e -> 
--                                pure e
--                            Nothing -> do
--                                pure (appExpr zz1
--                                    [ setWorkingExprTag (yy (InClass name ty) zz1) expr
--                                    , buildDict map ])
--        
--                _   | isVar ty -> do
--        
--                        tv  <- dictTVar (InClass name ty) (tApp kTyp (tCon kFun name) ty)
--                        --all <- baz 
--                        let t1 = tApp kTyp (tCon kFun name) ty
--                        --    getType t = tAtom `tArr` t1 `tArr` t
--                        --if var `elem` (fst <$> all) 
--                        --    then do
--                        --        pure (appExpr (workingExprTag expr)
--                        --            [ varExpr (getType <$> workingExprTag expr) "@#getField"
--                        --            , litExpr (Just tAtom) (TAtom var) 
--                        --            , varExpr (Just t1) tv 
--                        --            ])
--                        --pure (appExpr zz1
--                        --            [ setWorkingExprTag (yy (InClass name ty) zz1) expr
--                        --            , varExpr (Just t1) tv ])
--                        pure (appExpr (cod <$> zz1)
--                                    [ expr
--                                    , varExpr (Just t1) tv ])
--        
--        
--                        --pure expr
--        --                pure (appExpr zz1
--        --                    [ expr -- setWorkingExprTag (yy (InClass name ty) zz1) expr
--        --                    , varExpr zz1 "xx" ])
--        --                -- TODO
--                        --all <- baz 
--                        --map <- baz2
--        --                pure (setWorkingExprTag (Just (tCon kTyp "Xxx") ) expr)
--                        --pure (setWorkingExprTag (Just (tCon kTyp "XX")) expr)
--                        --all <- baz 
--                        --pure (appExpr (cod <$> workingExprTag expr) -- TODO
--                        --    [ expr
--                        --    , buildDict map ])
--                        --pure (appExpr zz1
--                        --    [ setWorkingExprTag (yy (InClass name ty) zz1) expr
--                        --    , varExpr (Just t1) tv ])
--        
--                    | otherwise -> do
--                        map <- baz2
--                        pure (appExpr (cod <$> workingExprTag expr) -- TODO
--                            [ expr
--                            , buildDict map ])
--
--  where
--    cod (Fix (TArr _ t)) = t
--
--    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz
--    zz1 = foldr yy (workingExprTag expr) ps
--
--    baz = do
--        env <- askClassEnv
--        fromRight (error ("No class " <> show name))   -- TODO
--            <$> runExceptT (lookupAllClassX name env)
--
--    baz2 = do
--        env <- askClassEnv
--        fromRight (error ("No instance " <> show name <> " " <> show ty))   -- TODO
--            <$> runExceptT (lookupAllClassMethods name ty env)
--            >>= traverse (secondM translateMethod) 
--
--    translateMethod = translate
--                    . Stage1.translate 
--                    . getAst 
--                    . translateTag 
--
--    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)
--
--    buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
--    buildDict map = conExpr (Just (tApp kTyp (tCon kFun name) ty)) "#" [row]
--      where
--        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
--        fn (name, expr) e = 
--            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
--             in rowExprCons row name expr e
--
----    t1 = undefined

--applyDicts
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => Predicate
--  -> (WorkingExpr (Maybe Type), Maybe Type)
--  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type), Maybe Type)
--applyDicts (InClass name ty) (expr, tx) = do
--    env <- askClassEnv
--    tv  <- dictTVar t1
--    case project expr of
--        EVar t var 
--            | isVar ty -> do
--                all <- baz env
--                if var `elem` (fst <$> all)
--                    then do
--                        let getType t = tAtom `tArr` t1 `tArr` t
--                        pure ( appExpr tx
--                                 [ varExpr (getType <$> workingExprTag expr) "@#getField"
--                                 , litExpr (Just tAtom) (TAtom var) 
--                                 , varExpr (Just t1) tv ]
--                             , tArr t1 <$> tx )
--                    else pure ( appExpr tx
--                                 [ setWorkingExprTag (tArr t1 <$> tx) expr
--                                 , varExpr (Just t1) tv ]
--                              , tArr t1 <$> tx )
--            | otherwise -> do
--                methods <- baz2 env
--                map <- traverse (secondM translateMethod) methods
--                -- Is this function a member of the class?
--                case lookup var map of
--                    Just e -> pure ( e, tArr t1 <$> tx )
--                    Nothing -> 
--                        pure ( appExpr tx
--                                 [ setWorkingExprTag (tArr t1 <$> tx) expr
--                                 , buildDict map ]
--                             , tArr t1 <$> tx )
--        _   | isVar ty -> do
--                undefined
--                --traceShowM "*****************"
--                --traceShowM e
--                --traceShowM ty
--                --traceShowM "*****************"
--                --methods <- baz2 env
--                --map <- traverse (secondM translateMethod) methods
--                --pure $ appExpr (workingExprTag expr)
--                --  [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                --  , buildDict map ]
--                --pure (varExpr (Just tInt) "TODO!")
--                --all <- baz env
--                --pure $ appExpr (workingExprTag expr) 
--                --    [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                --    ]
--                --    , buildDict map ]
--
--            | otherwise -> do
--                --traceShowM "==================="
--                --traceShowM "==================="
--                --traceShowM expr
--                --traceShowM "==================="
--                --traceShowM "==================="
----                pure (setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr)
----                pure (varExpr (Just tInt) "TODO!")
--                methods <- baz2 env
--                map <- traverse (secondM translateMethod) methods
--                pure ( appExpr tx
--                         [ setWorkingExprTag (tArr t1 <$> tx) expr
--                         , buildDict map ]
--                     , tArr t1 <$> tx )
--
--  where
--    t1 = tApp kTyp (tCon (kArr kTyp kTyp) name) ty
--    
--    baz env = fromRight noClassError <$> runExceptT (lookupAllClassX name env)
--    noClassError = error ("No class " <> show name)
--
--    baz2 env = fromRight noInstanceError <$> runExceptT (lookupAllClassMethods name ty env)
--    noInstanceError = error ("No instance " <> show name <> " " <> show ty)
--
--    translateMethod = translate
--                    . Stage1.translate 
--                    . getAst 
--                    . translateTag 
--
--    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)
--
--    buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
--    buildDict map =
--        conExpr (Just t1) "#" [row]
--      where
--        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
--        fn (name, expr) e = 
--            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
--             in rowExprCons row name expr e

--applyDicts
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => Predicate
--  -> WorkingExpr (Maybe Type)
--  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
--applyDicts (InClass name ty) expr = do
--    env <- askClassEnv
--    tv  <- dictTVar t1
--    case project expr of
--        EVar t var 
--            | isVar ty -> do
--                all <- baz env
--                if var `elem` (fst <$> all)
--                    then do
--                        let getType t = tAtom `tArr` t1 `tArr` t
--                        pure $ appExpr (workingExprTag expr) 
--                            [ varExpr (getType <$> workingExprTag expr) "@#getField"
--                            , litExpr (Just tAtom) (TAtom var) 
--                            , varExpr (Just t1) tv ]
--                    else pure $ appExpr (workingExprTag expr) 
--                            [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                            , varExpr (Just t1) tv ]
--            | otherwise -> do
--                methods <- baz2 env
--                map <- traverse (secondM translateMethod) methods
--                case lookup var map of
--                    Just e -> pure e
--                    Nothing -> 
--                        pure $ appExpr (workingExprTag expr)
--                            [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                            , buildDict map ]
--        e
--            | isVar ty -> do
--                undefined
--                --traceShowM "*****************"
--                --traceShowM e
--                --traceShowM ty
--                --traceShowM "*****************"
--                --methods <- baz2 env
--                --map <- traverse (secondM translateMethod) methods
--                --pure $ appExpr (workingExprTag expr)
--                --  [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                --  , buildDict map ]
--                --pure (varExpr (Just tInt) "TODO!")
--                --all <- baz env
--                --pure $ appExpr (workingExprTag expr) 
--                --    [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                --    ]
--                --    , buildDict map ]
--
--            | otherwise -> do
--                --traceShowM "==================="
--                --traceShowM "==================="
--                --traceShowM expr
--                --traceShowM "==================="
--                --traceShowM "==================="
----                pure (setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr)
----                pure (varExpr (Just tInt) "TODO!")
--                methods <- baz2 env
--                map <- traverse (secondM translateMethod) methods
--                pure $ appExpr (workingExprTag expr)
--                    [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                    , buildDict map -- varExpr (Just t1) "WHAT" 
--                    ]
--
--
--  where
--    t1 = tApp kTyp (tCon (kArr kTyp kTyp) name) ty
--    
--    baz env = fromRight noClassError <$> runExceptT (lookupAllClassX name env)
--    noClassError = error ("No class " <> show name)
--
--    baz2 env = fromRight noInstanceError <$> runExceptT (lookupAllClassMethods name ty env)
--    noInstanceError = error ("No instance " <> show name <> " " <> show ty)
--
--    translateMethod = translate
--                    . Stage1.translate 
--                    . getAst 
--                    . translateTag 
--
--    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)
--
--    buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
--    buildDict map =
--        conExpr (Just t1) "#" [row]
--      where
--        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
--        fn (name, expr) e = 
--            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
--             in rowExprCons row name expr e

--applyDicts (InClass name ty) expr
--
--    | isVar ty = do
--        tv <- dictTVar t1
--        pure (appExpr (workingExprTag expr) 
--          [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--          , varExpr (Just t1) tv ])
--
--    | otherwise = do
--        env <- askClassEnv
--        all <- runExceptT (lookupAllClassMethods name ty env)
--        --ins <- runExceptT (lookupClassInstance name ty env)
--        case all of
--            Left{} -> error ("No instance " <> show name <> " " <> show ty)
--            Right methods -> do
--                map <- traverse (secondM translateMethod) methods
--                case findIn map expr of
--                    Just e -> pure e
--                    Nothing -> 
--                        pure $ appExpr (workingExprTag expr)
--                          [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--                          , buildDict map ]
--
--                --pure (fromMaybe (buildDict map) (findIn map expr))
--                --pure (buildDict map)
--
----        traceShowM "vvvvvvvvvvvvv"
----        traceShowM expr
----        traceShowM "vvvvvvvvvvvvv"
----
----        case expr of
----            Fix (EVar _ var) -> do
----                traceShowM "*************"
----                traceShowM var
----            _ -> pure ()
----
----        pure foo
--
--        --pure (appExpr (workingExprTag expr)
--        --  [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
--        --  , foo ])
--
--        --methods <-- classMethods foo
--        --map <- traverse (secondM translateMethod) methods
--        --pure (fromMaybe (buildDict map) (findIn map expr))
--
----        case classMethods <$> lookupClassInstance name ty env of
----            Left e -> undefined
----        case classMethods <$> lookupClassInstance name ty env of
----        --    -- TODO
----        --    Left e -> error ("No instance " <> show name <> " " <> show ty)
----        --    -- TODO
----            Right methods -> do
----                map <- traverse (secondM translateMethod) methods
----                pure (fromMaybe (buildDict map) (findIn map expr))
--  where
--    t1 = tApp kClass (tCon (kArr kTyp kClass) name) ty
--
--    translateMethod = expandTypeClasses 
--                    . Stage1.translate 
--                    . getAst 
--                    . translateTag 
--
--    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)
--
--    findIn :: [(Name, WorkingExpr t)] -> WorkingExpr t -> Maybe (WorkingExpr t)
--    findIn map = project >>> \case
--        EVar _ var -> lookup var map
--        _          -> Nothing
--
--    buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
--    buildDict map = 
--        conExpr (Just t1) "#" [row]
--      where 
--        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
--        fn (name, expr) e = 
--            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
--             in rowExprCons row name expr e

setWorkingExprTag :: t -> WorkingExpr t -> WorkingExpr t
setWorkingExprTag t = project >>> \case
    EVar _ a     -> varExpr t a
    ECon _ a b   -> conExpr t a b
    ELit _ a     -> litExpr t a
    EApp _ a     -> appExpr t a
    ELet _ p a b -> letExpr t p a b
    EFix _ n a b -> fixExpr t n a b
    ELam _ p a   -> lamExpr t p a
    EIf  _ a b c -> ifExpr  t a b c
    EPat _ o a   -> patExpr t o a

workingExprTag :: WorkingExpr t -> t
workingExprTag = project >>> \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    ELet t _ _ _ -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EPat t _ _   -> t
