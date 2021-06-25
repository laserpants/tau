{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage2 where

import Control.Monad.Except 
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldlM, foldrM)
import Data.List (nub, tails)
import Data.Either (fromRight)
import Data.Maybe (fromMaybe, fromJust)
import Data.Tuple.Extra (second)
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Pretty
import Tau.Tooling
import Tau.Type
import qualified Data.Text as Text
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1

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
translate expr = evalStateT (expandTypeClasses =<< translateLiterals expr) []

translateLiterals 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [e] (Maybe Type))
  -> StateT [(Name, Type)] m (WorkingExpr (TypeInfoT [e] (Maybe Type)))
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
  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
expandTypeClasses expr =
    insertArgsExpr <$> run expr <*> (nub <$> pluck)
  where
    run = cata $ \case
        ELet t bind@BFun{} expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            letExpr (nodeType t) (insertArgsBinding (translateBinding bind) vs) e1 <$> expr2

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            letExpr (nodeType t) (translateBinding pat) (insertArgsExpr e1 vs) <$> expr2

        EFix t var expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            fixExpr (nodeType t) var (insertArgsExpr e1 vs) <$> expr2

        EVar t var -> do
            --fst <$> foldrM applyDicts (varExpr (nodeType t) var, nodeType t) (tails (nodePredicates t))
            --fst <$> foldlM applyDicts (varExpr (nodeType t) var, nodeType t) (tails (nodePredicates t)) 
            --when ("fn" == var) $ do
            --    traceShowM "////////////////"
            --    traceShowM "////////////////"
            --    traceShowM (tails (nodePredicates t))
            --    traceShowM "////////////////"
            --    traceShowM "////////////////"
            foldlM applyDicts (varExpr (nodeType t) var) (tails (reverse (nodePredicates t)))

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

insertArgsExpr :: WorkingExpr (Maybe Type) -> [(Name, Type)] -> WorkingExpr (Maybe Type)
insertArgsExpr = foldr fun 
  where
    --fun (var, ty) e = 
    --    lamExpr (tArr <$> Just ty <*> workingExprTag e) 
    --            [varPat (Just ty) var] e

    fun (var, ty) e = 
        case ty of
            Fix (TApp _ _ (Fix TVar{})) -> 
                lamExpr (tArr <$> Just ty <*> workingExprTag e) 
                        [varPat (Just ty) var] e
            _ -> e

insertArgsBinding :: ProgBinding (Maybe Type) -> [(Name, Type)] -> ProgBinding (Maybe Type)
insertArgsBinding (BFun t name ps) vs = BFun t' name ps'
  where
    (t', ps') = foldr fun (t, ps) vs
--    fun (var, ty) (t, ps) = (tArr ty <$> t, varPat (Just ty) var:ps)

    fun (var, ty) (t, ps) = 
        case ty of
            Fix (TApp _ _ (Fix TVar{})) -> 
                (tArr ty <$> t, varPat (Just ty) var:ps)
            _ -> 
                (t, ps)

dictTVar :: (MonadSupply Name m) => Type -> StateT [(Name, Type)] m Name
dictTVar ty = do
    map <- get
    case filter ((==) ty . snd) map of
        p:_ -> pure (fst p)
        _   -> do 
            var <- supply
            modify ((var, ty) :)
            pure var

applyDicts
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (Maybe Type)
  -> [Predicate]
  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
applyDicts e [] = pure e
applyDicts expr (InClass name ty:ps) = do
  
--    let t1 = tApp kTyp (tCon kFun name) ty    -- Dictionary type, e.g., Num Int

    case project expr of
        EVar t var 
            | isVar ty -> do
                tv  <- dictTVar (tApp kTyp (tCon kFun name) ty)
                all <- baz 
                let t1 = tApp kTyp (tCon kFun name) ty
                    getType t = tAtom `tArr` t1 `tArr` t
                if var `elem` (fst <$> all) 
                    then do
                        pure (appExpr (workingExprTag expr)
                            [ varExpr (getType <$> workingExprTag expr) "@#getField"
                            , litExpr (Just tAtom) (TAtom var) 
                            , varExpr (Just t1) tv 
                            ])
                    else pure (appExpr zz1
                            [ setWorkingExprTag (yy (InClass name ty) zz1) expr
                            , varExpr (Just t1) tv ])

            | otherwise -> do
                map <- baz2 
                -- Is this a member function of the class?
                case lookup var map of
                    Just e -> 
                        pure e
                    Nothing -> do
                        pure (appExpr zz1
                            [ setWorkingExprTag (yy (InClass name ty) zz1) expr
                            , buildDict map ])

        _   | isVar ty -> do
                undefined

            | otherwise -> do
                map <- baz2
                pure (appExpr (cod <$> workingExprTag expr) -- TODO
                    [ expr
                    , buildDict map ])

  where
    cod (Fix (TArr _ t)) = t

    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz
    zz1 = foldr yy (workingExprTag expr) ps

    baz = do
        env <- askClassEnv
        fromRight (error ("No class " <> show name))   -- TODO
            <$> runExceptT (lookupAllClassX name env)

    baz2 = do
        env <- askClassEnv
        fromRight (error ("No instance " <> show name <> " " <> show ty))   -- TODO
            <$> runExceptT (lookupAllClassMethods name ty env)
            >>= traverse (secondM translateMethod) 

    translateMethod = translate
                    . Stage1.translate 
                    . getAst 
                    . translateTag 

    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)

    buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
    buildDict map = conExpr (Just (tApp kTyp (tCon kFun name) ty)) "#" [row]
      where
        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
        fn (name, expr) e = 
            let row = tRow name <$> workingExprTag expr <*> workingExprTag e
             in rowExprCons row name expr e

--    t1 = undefined

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
