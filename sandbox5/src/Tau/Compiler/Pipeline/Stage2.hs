{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage2 where

import Control.Monad.Except 
import Control.Monad.Reader
import Control.Monad.Writer
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
import Tau.Util
import Tau.Type
import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Env as Env

type WorkingExpr t = Expr t t t t t t t t t Void Void Void Void Void Void Void
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
    fromJust (evalSupply (runReaderT expr env) (numSupply ""))
  where
    env = (classEnv, typeEnv, kindEnv, constructorEnv)

--translate 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (TypeInfoT [Error] (Maybe Type))
--  -> m (WorkingExpr (Maybe Type))

type Ti = TypeInfoT [Error] (Maybe Type)

translate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
  -> m (Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) [ProgPattern (Maybe Type)] (SimplifiedClause (Maybe Type) (ProgPattern (Maybe Type))))

translate expr = evalStateT (expandTypeClasses =<< translateLiterals =<< xxx expr) mempty

--xxx
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (TypeInfoT [e] (Maybe Type))
--  -> m (WorkingExpr (TypeInfoT [e] (Maybe Type)))
xxx
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
  -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti)))

xxx = cata $ \case

    EPat t expr clauses -> do
        e <- expr
        cs <- traverse sequence clauses >>= expandLitAndAnyPatterns 
        pure (patExpr t e cs)
        --compilePatterns e cs

    ELit    t prim       -> pure (litExpr t prim)
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
--    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
    ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2


--translateLambda
--  :: (MonadSupply Name m) 
--  => Maybe Type
--  -> [ProgPattern (Maybe Type)]
--  -> TargetExpr (Maybe Type)
--  -> m (TargetExpr (Maybe Type))
--translateLambda t [Fix (PVar _ var)] e = pure (lamExpr t var e)
--translateLambda t ps e = do
--    fst <$> foldrM fn (e, undefined e) ps
--  where
--    fn p (e, t) = do
--        let t' = tArr <$> xPatternTag p <*> t
--        var <- supply
--        pure (lamExpr t' var (patExpr t 
--                 (varExpr (xPatternTag p) var)
--                 [SimplifiedClause t [p] (Guard [] e)]), t')
--
--xPatternTag = undefined




expandLitAndAnyPatterns 
  :: (MonadSupply Name m) 
  => [SimplifiedClause (TypeInfoT [e] (Maybe Type)) (ProgPattern (TypeInfoT [e] (Maybe Type))) (WorkingExpr (TypeInfoT [e] (Maybe Type)))] 
  -> m [SimplifiedClause (TypeInfoT [e] (Maybe Type)) (ProgPattern (TypeInfoT [e] (Maybe Type))) (WorkingExpr (TypeInfoT [e] (Maybe Type)))]
expandLitAndAnyPatterns = traverse expandClause
  where
    expandClause (SimplifiedClause t ps (Guard exs e)) = do
        (qs, exs1) <- runWriterT (traverse expandPatterns ps)
        pure (SimplifiedClause t qs (Guard (exs <> exs1) e))

    expandPatterns = cata $ \case
        PLit t prim -> do
            var <- varSupply
            tell [ appExpr (TypeInfo [] (Just tBool) [])
                   [ varExpr (eqFunType <$$> t) ("(==)")
                   , varExpr (TypeInfo [] (nodeType t) []) var
                   , litExpr t prim ]]
            pure (varPat t var)
          where
            eqFunType t = t `tArr` t `tArr` tBool

        PAny   t          -> varPat t <$> varSupply
        PVar   t var      -> pure (varPat t var)
        PCon   t con ps   -> conPat t con <$> sequence ps
        PAs    t as p     -> asPat t as <$> p
        POr    t p q      -> orPat t <$> p <*> q
        PTuple t ps       -> tuplePat t <$> sequence ps
        PList  t ps       -> listPat t <$> sequence ps
        PRow   t lab p q  -> rowPat t lab <$> p <*> q 

    varSupply = ("$2.a" <>) <$> supply

--    traverse expandClause
--      where
--        expandClause (SimplifiedClause t ps (Guard exs e)) = do
--            (qs, exs1) <- runWriterT (traverse expandPatterns ps)
--            pure (SimplifiedClause t qs (Guard (exs <> exs1) e))
--
--        expandPatterns = cata $ \case
--            PLit t prim -> do
--                var <- supply
--                tell [ appExpr (Just tBool)
--                       [ varExpr (ty <$> t) ("@" <> primName prim <> ".(==)")
--                       , varExpr t var
--                       , litExpr t prim ]]
--                pure (varPat t var)
--              where
--                ty t = t `tArr` t `tArr` tBool
--
--            PAny t           -> varPat t <$> supply
--            PVar t var       -> pure (varPat t var)
--            PCon t con ps    -> conPat t con <$> sequence ps
--            PAs  t as p      -> asPat t as <$> p

--translateLiterals 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (TypeInfoT [e] (Maybe Type))
--  -> StateT (Env [(Name, Name)]) m (WorkingExpr (TypeInfoT [e] (Maybe Type)))

translateLiterals 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
  -> StateT (Env [(Name, Name)]) m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti)))

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

--    EPat t expr clauses -> do
--        e <- expr
--        cs <- traverse sequence clauses >>= expandLitAndAnyPatterns 
--        pure (patExpr t e cs)
--        --compilePatterns e cs

    ELit    t prim       -> pure (litExpr t prim)
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
    ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2

--expandTypeClasses
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (TypeInfoT [e] (Maybe Type))
--  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))

type StageX3Expr = Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) [ProgPattern (Maybe Type)] (SimplifiedClause (Maybe Type) (ProgPattern (Maybe Type)))

expandTypeClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
  -> StateT (Env [(Name, Name)]) m (Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) [ProgPattern (Maybe Type)] (SimplifiedClause (Maybe Type) (ProgPattern (Maybe Type))))

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

            let zmap :: Map Type [Name]
                zmap = foldr (\(InClass n t) -> Map.insertWith (<>) t [n]) mempty ys

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

--insertArgsExpr 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (Maybe Type) 
--  -> Env [(Name, Name)] 
--  -> StateT (Env [(Name, Name)]) m (WorkingExpr (Maybe Type))
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
--                if Just False == (fnx . typeOf <$> (workingExprTag e))
--                    then error "Ambiguity"
--                    else if name `elem` set1
                if name `elem` set1
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

--insertArgsBinding 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => ProgBinding (Maybe Type) 
--  -> WorkingExpr (Maybe Type) 
--  -> Env [(Name, Name)] 
--  -> StateT (Env [(Name, Name)]) m (ProgBinding (Maybe Type), WorkingExpr (Maybe Type))
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
  -> Expr t t t t t t t t t Void Void Void Void Void Void Void (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))
  -> Expr t t t t t t t t t Void Void Void Void Void Void Void (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))
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
        dv <- ("$dict" <>) <$> supply
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

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
    ----expandLitAndAnyPatterns2
    ----  :: (MonadSupply Name m) 
    ----  => [SimplifiedClause Ti (ProgPattern Ti) (WorkingExpr Ti)] 
    ----  -> m [SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void) (WorkingExpr Ti)]
    --
    --expandLitAndAnyPatterns2 
    --  :: (MonadSupply Name m) 
    --  => [SimplifiedClause Ti (ProgPattern Ti) ((Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void))))]
    --  -> m [SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void) (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))]
-------------------------------------------------------------------------------

--type StageX1Expr = Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void))
type StageX1Expr = (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (Binding Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))

type StageX1ExprXX t = (Expr t t t t t t t t t Void Void Void Void Void Void Void (Binding t (Pattern t t t Void Void t Void Void Void)) Name (SimplifiedClause t (Pattern t t t Void Void t Void Void Void)))

--runTranslate3 = undefined

-- runTranslate3
--   :: ClassEnv 
--   -> TypeEnv 
--   -> KindEnv 
--   -> ConstructorEnv 
--   -> Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti)) 
--   -> Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void))
-- runTranslate3 classEnv typeEnv kindEnv constructorEnv expr = 
--     fromJust (evalSupply (runReaderT (translate3 expr) env) (numSupply ""))
--   where
--     env = (classEnv, typeEnv, kindEnv, constructorEnv)

--runTranslate3
--  :: (MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m)
--  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti)) 
--  -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))
--runTranslate3 expr = do
--    --yo <- evalSupplyT (translate3 expr) (numSupply "")
--    pure (fromJust zz)
--    --fromJust (evalSupply (runReaderT (translate3 expr) env) (numSupply ""))
--  where
----    zz :: Maybe (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))
--    zz = evalSupply (translate3 expr) (numSupply "")

-- translate3
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--   => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
--   -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))
-- translate3 expr = translateLiteral2 =<< xxx2 =<< expandExpr expr

--translate2
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
--  -> m (Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) [ProgPattern (Maybe Type)] (SimplifiedClause (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void (Maybe Type) Void Void Void)))
--translate2 expr = evalStateT (compileTypeclasses =<< translateLiteral2 =<< xxx2 =<< expandExpr expr) mempty

foo123 expr = undefined -- xxx2 =<< expandExpr expr
--foo123 expr = expandExpr expr

--foo456 expr = translateLiteral3

--runTranslate3 classEnv typeEnv kindEnv constructorEnv expr = 
--     fromJust (evalSupply (runReaderT (foo123 expr) env) (numSupply ""))
--   where
--     env = (classEnv, typeEnv, kindEnv, constructorEnv)

runTranslate4 classEnv typeEnv kindEnv constructorEnv f = 
    fromJust (evalSupply (runReaderT f env) (numSupply ""))
  where
    env = (classEnv, typeEnv, kindEnv, constructorEnv)

runTranslate44 f = do
    env <- ask
    pure (fromJust (evalSupply (runReaderT f env) (numSupply "")))

type StageX1ExprYY = (Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void Void Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void)))

type StageX1ExprYYY t = (Expr t t t t t t t t Void Void Void Void Void Void Void Void Void Name (SimplifiedClause t (Pattern t t t Void Void Void Void Void Void)))

expandExpr
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  =>    Stage1.TargetExpr Ti -- Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))
  -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void Void Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void)))
expandExpr = cata $ \case

    ELet t bind e1 e2 -> do 
        a <- e1
        b <- e2
        translateLet2 t bind a b

    ELam t ps expr -> 
        expr >>= translateLambda3 t ps 

    EPat t expr clauses -> do
        e <- expr
        cs <- traverse sequence clauses
        fooz3 t e cs

    ELit    t prim       -> pure (litExpr t prim)
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    EApp    t es         -> appExpr t <$> sequence es
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3

translateLet2 t (BPat _ (Fix (PVar _ var))) e1 e2 = 
    pure (fixExpr t var e1 e2)
translateLet2 t bind e1 e2 = do
    (e, p) <- case bind of
                  -- TODO -- check that no literals appear in pattern
                  BPat _ pat  -> pure (e1, pat)
                  BFun t f ps -> do
                      e <- translateLambda3 t ps e1
                      pure (e, varPat t f)
    fooz3 t e [SimplifiedClause t [p] (Guard [] e2)]
    --pure xxx1 -- (patExpr t e [SimplifiedClause t [p] (Guard [] e2)])

translateLambda3 t [Fix (PVar _ var)] e = pure (lamExpr t var e)
translateLambda3 t ps e = fst <$> foldrM fn (e, fooExprTag e) ps
  where
    fn p (e, t) = do
        let t' :: TypeInfoT [Error] (Maybe Type)
            t' = TypeInfo [] (foot t) []

            foot t = tArr <$> nodeType (fooPatternTag p) <*> nodeType t

        var <- supply
        xxx1 <- fooz3 t (varExpr (fooPatternTag p) var) [SimplifiedClause t [p] (Guard [] e)]
        pure (lamExpr t' var xxx1, t')
--        pure (lamExpr t' var (patExpr t 
--                 (varExpr (fooPatternTag p) var)
--                 [SimplifiedClause t [p] (Guard [] e)]), t')

    fooExprTag = project >>> \case
        EVar    t _     -> t
        ECon    t _ _   -> t
        ELit    t _     -> t
        EApp    t _     -> t
        EFix    t _ _ _ -> t
        ELam    t _ _   -> t
        EIf     t _ _ _ -> t
        EPat    t _ _   -> t

    fooPatternTag = project >>> \case
        PVar    t _     -> t
        PCon    t _ _   -> t
        PLit    t _     -> t 
        PAs     t _ _   -> t
        POr     t _ _   -> t
        PAny    t       -> t
        PTuple  t _     -> t
        PList   t _     -> t
        PRow    t _ _ _ -> t

--translateLambda2
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => Ti
--  -> [Fix (PatternF Ti Ti Ti Ti Ti Ti Ti Ti Ti)]
--  -> Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (ProgPattern Ti))
--  -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (ProgPattern Ti)))
--translateLambda2 t [Fix (PVar _ var)] e = pure (lamExpr t var e)
--translateLambda2 t ps e = fst <$> foldrM fn (e, fooExprTag e) ps
--  where
--    fn p (e, t) = do
--        let t' :: TypeInfoT [Error] (Maybe Type)
--            t' = TypeInfo [] (foot t) []
--
--            foot t = tArr <$> nodeType (fooPatternTag p) <*> nodeType t
--
--        var <- supply
--        pure (lamExpr t' var (patExpr t 
--                 (varExpr (fooPatternTag p) var)
--                 [SimplifiedClause t [p] (Guard [] e)]), t')
--
--    fooExprTag = project >>> \case
--        EVar    t _     -> t
--        ECon    t _ _   -> t
--        ELit    t _     -> t
--        EApp    t _     -> t
--        ELet    t _ _ _ -> t
--        EFix    t _ _ _ -> t
--        ELam    t _ _   -> t
--        EIf     t _ _ _ -> t
--        EPat    t _ _   -> t
--
--    fooPatternTag = project >>> \case
--        PVar    t _     -> t
--        PCon    t _ _   -> t
--        PLit    t _     -> t 
--        PAs     t _ _   -> t
--        POr     t _ _   -> t
--        PAny    t       -> t
--        PTuple  t _     -> t
--        PList   t _     -> t
--        PRow    t _ _ _ -> t

fooz3 t expr clauses = do
    gg <- concat <$> traverse expandClausePatterns clauses
    pure (patExpr t expr gg)
  where
    expandClausePatterns (SimplifiedClause t ps (Guard es e)) = do
--        traceShowM "===============>>"
--        traceShowM (pretty ps)
--        traceShowM ps
--        traceShowM "===============>>"
        (qs, ds) <- runWriterT (traverse expandPatterns999 ps)
        pure (expandPatterns444 [SimplifiedClause t qs (Guard (es <> ds) e)])

--        pure (undefined [SimplifiedClause t qs (Guard (es <> ds) e)])
--        traceShowM (pretty qss)
--        traceShowM qss
--        traceShowM "===============>>"
--        pure [SimplifiedClause t qs (Guard (es <> ds) e) | qs <- qss]


    --let foo = expandOrPatterns gg

        --pure (SimplifiedClause t qs (Guard es e))

--fooz2 t expr clauses = 
--    patExpr t <$> expr <*> (traverse sequence clauses >>= traverse expandClausePatterns)
--  where
--    expandClausePatterns (SimplifiedClause t ps (Guard es e)) = do
--        (qs, ds) <- runWriterT (traverse expandPatterns2 ps)
--        pure (SimplifiedClause t qs (Guard (es <> ds) e))



--xxx2
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
----  => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (ProgPattern Ti))
--     =>  Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (ProgPattern Ti))
--  -> m (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (Binding Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))
--xxx2 = cata $ \case
--
--    EPat t expr clauses -> 
--        patExpr t <$> expr 
--                  <*> (traverse sequence clauses >>= traverse expandClausePatterns)
--
--    ELit    t prim       -> pure (litExpr t prim)
--    EVar    t var        -> pure (varExpr t var)
--    ECon    t con exs    -> conExpr t con <$> sequence exs
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    ELam    t name e     -> lamExpr t name <$> e
--    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
----    ELet    t bind e1 e2 -> letExpr t <$> expandBindingPatterns bind <*> e1 <*> e2
--
--  where
----    expandBindingPatterns = \case
----    expandBindingPatterns = \case
----        BPat t p         -> BPat t <$> expandPatterns1 p
----        BFun t name ps   -> BFun t name <$> traverse expandPatterns1 ps
----
----    expandClausePatterns (SimplifiedClause t ps (Guard es e)) = undefined
--    expandClausePatterns (SimplifiedClause t ps (Guard es e)) = do
--        (qs, ds) <- runWriterT (traverse expandPatterns2 ps)
--        pure (SimplifiedClause t qs (Guard (es <> ds) e))

--        qs <- traverse expandPatterns1 ps
----        rs <- runWriterT (traverse expandPatterns2 qs)
--        pure (SimplifiedClause t qs (Guard es e))


varSupply
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => m Name
varSupply = ("$2.a" <>) <$> supply

--expandPatterns1 
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => ProgPattern Ti
--  -> m (Pattern Ti Ti Ti Void Void Ti Void Void Void)
--
----expandPatterns1 
----  :: ( MonadSupply Name m
----     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
----  => ProgPattern Ti
----  -> m (Pattern Ti Ti Ti Ti Void Ti Void Void Void)
--expandPatterns1 = cata $ \case
--
--    -- TODO: comment
--    PTuple t ps -> 
--        conPat t (tupleCon (length ps)) <$> sequence ps
--
--    -- TODO: comment
--    PList t ps ->
--        foldr (listPatCons t) (conPat t "[]" []) <$> sequence ps
--
--    -- TODO: comment
--    PRow t lab p q  -> 
--        foldRowPat t lab <$> p <*> q
--
--    -- TODO: comment
--    PAny t          -> varPat t <$> varSupply
--    PVar t var      -> pure (varPat t var)
--    PCon t con ps   -> conPat t con <$> sequence ps
--    PAs  t as p     -> asPat t as <$> p
--    POr  t p q      -> orPat t <$> p <*> q


----expandPatterns 
----  :: ( MonadSupply Name m
----     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m 
----     )
----  => ProgPattern Ti
----  -> WriterT [Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti Ti (Binding Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)) [ProgPattern Ti] (SimplifiedClause Ti (ProgPattern Ti))] m (Pattern Ti Ti Ti Void Void Ti Void Void Void)
----expandPatterns2
----  :: ( MonadSupply Name m
----     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
----  => ProgPattern Ti -- Pattern Ti Ti Ti Ti Void Ti Void Void Void  -- Pattern Ti Ti Ti Ti Void Ti Void Void Void
----  -> WriterT [Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void (Binding Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void))] m (Pattern Ti Ti Ti Void Void Ti Void Void Void) -- (Pattern Ti Ti Ti Void Void Ti Void Void Void)

--expandPatterns333
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => ProgPattern Ti 
--  -> m (Pattern Ti Ti Ti Void Void Ti Void Void Void)
--expandPatterns333 =
--    undefined

type Foox = SimplifiedClause () (Pattern () () () Void Void () Void Void Void) (ProgExpr ())

-- (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void)

expandPatterns444
  :: [SimplifiedClause t (Pattern t t t Void Void t Void Void Void) a]
  -> [SimplifiedClause t (Pattern t t t Void Void Void Void Void Void) a]
expandPatterns444 = concatMap $ \(SimplifiedClause t ps g) ->
    [SimplifiedClause t qs g | qs <- traverse fn ps]
  where
    fn :: Pattern t t t Void Void t Void Void Void -> [Pattern t t t Void Void Void Void Void Void]
    fn = cata $ \case

        PVar t var       -> pure (varPat t var)
        PCon t con ps    -> conPat t con <$> sequence ps
        PAs  t name a    -> asPat t name <$> a
        POr  _ a b       -> a <> b

expandPatterns999
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => ProgPattern Ti 
  -> WriterT [Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void Void Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void))] m 
        (Pattern Ti Ti Ti Void Void Ti Void Void Void)
expandPatterns999 = cata $ \case

    PTuple t ps -> 
        conPat t (tupleCon (length ps)) <$> sequence ps

    PList t ps -> 
        foldr (listPatCons t) (conPat t "[]" []) <$> sequence ps

    PRow t lab p q -> 
        foldRowPat t lab <$> p <*> q

    PAny t -> 
        varPat t <$> varSupply

    PLit t prim -> do
        var <- varSupply
        tell [ appExpr (TypeInfo [] (Just tBool) [])
                 [ varExpr (eqFunType <$$> t) ("(==)")
                 , varExpr (TypeInfo [] (nodeType t) []) var
                 , litExpr t prim ] ]
        pure (varPat t var)
      where
        eqFunType t = t `tArr` t `tArr` tBool

    PVar t var       -> pure (varPat t var)
    PCon t con ps    -> conPat t con <$> sequence ps
    PAs  t name a    -> asPat t name <$> a
    POr  t a b       -> orPat t <$> a <*> b


expandPatterns2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => ProgPattern Ti -- Pattern Ti Ti Ti Ti Void Ti Void Void Void  -- Pattern Ti Ti Ti Ti Void Ti Void Void Void
  -> WriterT [Expr Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void Void Void Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void))] m 
        [Pattern Ti Ti Ti Void Void Void Void Void Void]

expandPatterns2 = cata $ \case

    PTuple t ps -> do
        pss <- sequence ps
        pure (conPat t (tupleCon (length ps)) <$> pss)

    PList t ps -> do
        pss <- sequence ps
        pure (foldr (listPatCons t) (conPat t "[]" []) <$> pss)

    PRow t lab p q -> do
        ps <- p
        qs <- q
        pure (foldRowPat t lab <$> ps <*> qs)

    PVar t var -> 
        pure [varPat t var]

    PAny t -> do
        var <- varSupply
        pure [varPat t var]

    PCon t con ps -> do
        pss <- sequence ps
        pure [conPat t con qs | qs <- pss]
        --pure (conPat t con <$> pss)

    PAs t as p -> do
        ps <- p
        pure (asPat t as <$> ps)

    POr t p q -> do 
        a <- p
        b <- q
        pure (a <> b)

    PLit t prim -> do
        var <- varSupply
        tell [ appExpr (TypeInfo [] (Just tBool) [])
                 [ varExpr (eqFunType <$$> t) ("(==)")
                 , varExpr (TypeInfo [] (nodeType t) []) var
                 , litExpr t prim ] ]
        pure [varPat t var]
      where
        eqFunType t = t `tArr` t `tArr` tBool

--    PTuple t ps -> do
--        -- conPat t (tupleCon (length ps)) <$> sequence ps
--        --qs <- sequence ps
--        --pure [ conPat t (tupleCon (length ps)) qs ] -- [conPat t (tupleCon (length ps)) qs]
--
--    -- TODO: comment
--    PList t ps ->
--        foldr (listPatCons t) (conPat t "[]" []) <$> sequence ps
--
--    -- TODO: comment
--    PRow t lab p q  -> 
--        foldRowPat t lab <$> p <*> q
--
--    -- TODO: 
--    PLit t prim -> do
--        var <- varSupply
--        tell [ appExpr (TypeInfo [] (Just tBool) [])
--                 [ varExpr (eqFunType <$$> t) ("(==)")
--                 , varExpr (TypeInfo [] (nodeType t) []) var
--                 , litExpr t prim ] ]
--        pure (varPat t var)
--      where
--        eqFunType t = t `tArr` t `tArr` tBool
--
--    -- TODO: comment
--    PAny t          -> varPat t <$> varSupply
--    PVar t var      -> pure (varPat t var)
--    PCon t con ps   -> conPat t con <$> sequence ps
--    PAs  t as p     -> asPat t as <$> p
--    POr  t p q      -> orPat t <$> p <*> q

--expandOrPatterns 
--  :: [SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void) x]
--  -> [SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Void Void Void Void) x]
--expandOrPatterns = concatMap $ \(SimplifiedClause t ps g) ->
--    [SimplifiedClause t qs g | qs <- traverse fn ps]
--  where
--    fn :: Pattern Ti Ti Ti Void Void Ti Void Void Void -> [Pattern Ti Ti Ti Void Void Void Void Void Void]
--    fn = cata $ \case
--
--        PVar t var       -> pure (varPat t var)
--        PCon t con ps    -> conPat t con <$> sequence ps
--        PAs  t name a    -> asPat t name <$> a
--        POr  _ a b       -> a <> b
--
--
----    PVar   t var      -> pure (varPat t var)
----    PCon   t con ps   -> conPat t con <$> sequence ps
----    PAs    t as p     -> asPat t as <$> p
----    POr    t p q      -> orPat t <$> p <*> q
--
----            -- TODO: comment
----            PTuple t ps -> 
----                conPat t (tupleCon (length ps)) <$> sequence ps
----
----            -- TODO: comment
----            PList t ps ->
----                foldr (listPatCons t) (conPat t "[]" []) <$> sequence ps
----
----            -- TODO: comment
----            PRow t lab p q  -> 
----                foldRowPat t lab <$> p <*> q
----
----            -- TODO: comment
----            PAny t          -> varPat t <$> varSupply
----            PVar t var      -> pure (varPat t var)
----            PCon t con ps   -> conPat t con <$> sequence ps
----            PAs  t as p     -> asPat t as <$> p
----            POr  t p q      -> orPat t <$> p <*> q

--type StageX2Expr = (Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (Binding Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void)))

translateLiteral3 :: StageX1ExprYY -> StageX1ExprYY
translateLiteral3 = cata $ \case

    ELit t (TInt n) -> appExpr t 
        [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
        , litExpr (TypeInfo [] (Just tInteger) []) (TInteger (fromIntegral n)) ]

    ELit t (TInteger n) -> appExpr t 
        [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
        , litExpr (TypeInfo [] (Just tInteger) []) (TInteger n) ]

    ELit t (TFloat r) -> appExpr t 
        [ varExpr (t{ nodeType = tArr tDouble <$> nodeType t }) "fromDouble"
        , litExpr (TypeInfo [] (Just tDouble) []) (TDouble (fromRational (toRational r))) ]

    ELit t (TDouble r) -> appExpr t 
        [ varExpr (t{ nodeType = tArr tDouble <$> nodeType t }) "fromDouble"
        , litExpr (TypeInfo [] (Just tDouble) []) (TDouble r) ]

    e -> embed e

--    ELit    t prim       -> litExpr t prim)
--    EVar    t var        -> varExpr t var
--    ECon    t con exs    -> conExpr t con exs
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    ELam    t name e     -> lamExpr t name <$> e
--    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
--    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
--    ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2


--translateLiteral2
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => ZZ
--  -> m ZZ
--translateLiteral2 = cata $ \case
--
--    ELit t (TInt n) -> 
--        pure (appExpr t 
--            [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
--            , litExpr (TypeInfo [] (Just tInteger) []) (TInteger (fromIntegral n)) ])
--
--    ELit t (TInteger n) -> 
--        pure (appExpr t 
--            [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
--            , litExpr (TypeInfo [] (Just tInteger) []) (TInteger n) ])
--
--    ELit t (TFloat r) -> 
--        pure (appExpr t 
--            [ varExpr (t{ nodeType = tArr tDouble <$> nodeType t }) "fromDouble"
--            , litExpr (TypeInfo [] (Just tDouble) []) (TDouble (fromRational (toRational r))) ])
--
--    ELit t (TDouble r) -> 
--        pure (appExpr t 
--            [ varExpr (t{ nodeType = tArr tDouble <$> nodeType t }) "fromDouble"
--            , litExpr (TypeInfo [] (Just tDouble) []) (TDouble r) ])
--
--    ELit    t prim       -> pure (litExpr t prim)
--    EVar    t var        -> pure (varExpr t var)
--    ECon    t con exs    -> conExpr t con <$> sequence exs
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    ELam    t name e     -> lamExpr t name <$> e
--    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
--    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
--    ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2

--compileTypeclasses
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--   => Expr Ti Ti Ti Ti Ti Ti Ti Ti Ti Void Void Void Void Void Void Void (ProgBinding Ti) Name (SimplifiedClause Ti (Pattern Ti Ti Ti Void Void Ti Void Void Void))
--   -> StateT (Env [(Name, Name)]) m (Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) Name (SimplifiedClause (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void (Maybe Type) Void Void Void)))

compileTypeclasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => StageX1ExprYY
  -> StateT (Env [(Name, Name)]) m (StageX1ExprYYY (Maybe Type))
compileTypeclasses expr = do
    e <- walk expr
    s <- getAndReset 
    insertArgsExpr2 e s
  where
    --walk
    --  :: ( MonadSupply Name m
    --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
    --  => StageX1ExprYY
    --  -> StateT (Env [(Name, Name)]) m (StageX1ExprYYY (Maybe Type)) -- (Expr (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void Void (ProgBinding (Maybe Type)) Name (SimplifiedClause (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void (Maybe Type) Void Void Void)))
    walk = cata $ \case 

--        ELam t name expr -> do
--            e <- expr
--            s <- getAndReset
--            lamExpr (nodeType t) name <$> insertArgsExpr2 e s

        EPat t expr cs -> do
            e <- expr
            s <- getAndReset
            patExpr (nodeType t) <$> insertArgsExpr2 e s <*> (translateClauses <$$> traverse sequence cs)

        EFix t var expr1 expr2 -> do
            e <- expr1
            s <- getAndReset
            fixExpr (nodeType t) var <$> insertArgsExpr2 e s <*> expr2

        EVar t var -> do
            let (vs, ts) = partition (isVar . predicateType) (nodePredicates t)

            classEnv <- askClassEnv
            fromType <- traverse (reduceSet classEnv) 
                (foldr (\(InClass n t) -> Map.insertWith (<>) t [n]) mempty ts)

            let ps = Map.foldrWithKey (\k ns ps -> [InClass n k | n <- ns] <> ps) [] fromType
            e1 <- foldlM applyNonVarPredicates (varExpr (nodeType t) var) (tails ps)

            qs <- fromRight (error "impl") <$> reduce classEnv vs  
            foldlM applyVarPredicates e1 (tails qs)

        ELit   t prim      -> pure (litExpr (nodeType t) prim)
        ECon   t con es    -> conExpr (nodeType t) con <$> sequence es
        EApp   t es        -> appExpr (nodeType t) <$> sequence es
        ELam   t name e    -> lamExpr (nodeType t) name <$> e
        EIf    t e1 e2 e3  -> ifExpr  (nodeType t) <$> e1 <*> e2 <*> e3
--        EPat   t expr cs   -> patExpr (nodeType t) <$> expr <*> (translateClauses <$$> traverse sequence cs)

    --translatePatterns 
    --  :: Pattern Ti Ti Ti Void Void Void Void Void Void 
    --  -> Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void
    translatePatterns = cata $ \case
        PVar   t var       -> varPat  (nodeType t) var
        PCon   t con ps    -> conPat  (nodeType t) con ps
        PAs    t as p      -> asPat   (nodeType t) as p

    translateClauses = \case
        SimplifiedClause t ps g -> 
            SimplifiedClause (nodeType t) (translatePatterns <$> ps) g

--zork
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => [Predicate]
--  -> m [Predicate]
--zork ts = do
--    --
--    -- Int    => ["Num", "Eq"]
--    -- String => ["Show"]
--    --
--    classEnv <- askClassEnv
--    fromType <- traverse (reduceSet classEnv) 
--        (foldr (\(InClass n t) -> Map.insertWith (<>) t [n]) mempty ts)
--    pure (Map.foldrWithKey (\k ns ps -> [InClass n k | n <- ns] <> ps) [] fromType)

dictTVar3 name (TVar _ var) = do
    info <- get
    classEnv <- askClassEnv
    maybe fresh pure (lookupVar info classEnv)
  where
    fresh = do
        dv <- ("$dict" <>) <$> supply
        modify (Env.alter (\vs -> Just $ (name, dv):fromMaybe [] vs) var)
        pure dv

    lookupVar info classEnv = do
        varEnv <- Env.lookup var info 
        snd <$> find (elem name . fst) (first (super1 classEnv) <$> varEnv)

applyVarPredicates
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => StageX1ExprYYY (Maybe Type)
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (StageX1ExprYYY (Maybe Type))
applyVarPredicates expr [] = pure expr
applyVarPredicates expr (InClass name ty:ps) = do
    tv <- dictTVar3 name (project ty)
    let t1 = tApp kTyp (tCon kFun name) ty
    case project expr of
        EVar t var -> do
            all <- baz 
            let getType t = tAtom `tArr` t1 `tArr` t
            if var `elem` (fst <$> all) 
                then do
                    pure (appExpr (workingExprTag2 expr)
                        [ varExpr (getType <$> workingExprTag2 expr) "@#getField"
                        , litExpr (Just tAtom) (TAtom var) 
                        , varExpr (Just t1) tv ])
                else pure (appExpr zz1
                        [ setWorkingExprTag2 (yy (InClass name ty) zz1) expr
                        , varExpr (Just t1) tv ])
        _ -> 
            pure (appExpr (cod <$> zz1)
                [ expr
                , varExpr (Just t1) tv ])

  where
    cod (Fix (TArr _ t)) = t

    zz1 = foldr yy (workingExprTag2 expr) ps

    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz

    baz = do
        env <- askClassEnv
        fromRight (error ("No class " <> show name))   -- TODO
            <$> runExceptT (lookupAllClassX name env)

applyNonVarPredicates
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => StageX1ExprYYY (Maybe Type)
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (StageX1ExprYYY (Maybe Type))
applyNonVarPredicates expr [] = pure expr
applyNonVarPredicates expr (InClass name ty:ps) = do
    dictMap <- collectMethods
    case project expr of
        EVar t var -> 
            -- Is this a member function of the class?
            case lookup var dictMap of
                Just e -> 
                    pure e

                Nothing -> 
                    pure (appExpr zz1
                        [ setWorkingExprTag2 (yy (InClass name ty) zz1) expr
                        , buildDict dictMap ])
        _ -> 
            pure (appExpr (cod <$> workingExprTag2 expr) -- TODO
                [ expr
                , buildDict dictMap ])
  where
    collectMethods = do
        env <- askClassEnv
        fromRight (error ("No instance " <> show name <> " " <> show ty))   -- TODO
            <$> runExceptT (lookupAllClassMethods name ty env)
                >>= traverse (secondM translateMethod) 

    cod (Fix (TArr _ t)) = t

    zz1 = foldr yy (workingExprTag2 expr) ps

    yy (InClass name ty) tz = tArr (tApp kTyp (tCon kFun name) ty) <$> tz

    buildDict map = 
        conExpr (Just (tApp kTyp (tCon kFun name) ty)) "#" 
            [foldr fn (conExpr (Just tRowNil) "{}" []) map]
      where
        fn (name, expr) e = 
            let row = tRow name <$> workingExprTag2 expr <*> workingExprTag2 e
             in rowExprCons row name expr e


translateMethod
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Ast (TypeInfo ())
  -> m (StageX1ExprYYY (Maybe Type))
translateMethod ast = do
    a <- translateLiteral3 <$> expandExpr (Stage1.translate expr)
    runTranslate44 (evalStateT (compileTypeclasses a) mempty)
  where
    expr = mapExprTag zzz (getAst ast)
    zzz (TypeInfo () ty ps) = TypeInfo [] (Just ty) ps


setWorkingExprTag2 :: t -> StageX1ExprYYY t -> StageX1ExprYYY t 
setWorkingExprTag2 t = project >>> \case
    EVar _ a     -> varExpr t a
    ECon _ a b   -> conExpr t a b
    ELit _ a     -> litExpr t a
    EApp _ a     -> appExpr t a
    EFix _ n a b -> fixExpr t n a b
    ELam _ n a   -> lamExpr t n a
    EIf  _ a b c -> ifExpr  t a b c
    EPat _ o a   -> patExpr t o a

workingExprTag2 :: StageX1ExprYYY t -> t
workingExprTag2 = project >>> \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EPat t _ _   -> t


-- workingExprTag



insertArgsExpr2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => StageX1ExprYYY (Maybe Type)
  -> Env [(Name, Name)] 
  -> StateT (Env [(Name, Name)]) m (StageX1ExprYYY (Maybe Type))
insertArgsExpr2 expr = foldrM fun expr . Env.toList
  where
    fun (var, vs) e = do
        classEnv <- askClassEnv
        set1 <- reduceSet classEnv (fst <$> vs)
        let set2 = [(x, b) | (a, b) <- vs, x <- super1 classEnv a, a `elem` set1]
        pure (foldr (fun2 set1 set2) e vs)
          where
            fun2 set1 set2 (name, dv) e = do
                let
                    fnx t = var `elem` (fst <$> free t)

                -- TODO
--                if Just False == (fnx . typeOf <$> (workingExprTag e))
--                    then error "Ambiguity"
--                    else if name `elem` set1
                if name `elem` set1
                              then do
                                  let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
                                  lamExpr (tArr <$> Just ty <*> workingExprTag2 e) dv e
                              else 
                                  replaceVar2 dv (fromJust (lookup name set2)) e


replaceVar2
  :: Name 
  -> Name
  -> StageX1ExprYYY (Maybe Type) 
  -> StageX1ExprYYY (Maybe Type) 
replaceVar2 from to = cata $ \case
    EVar t var | from == var -> varExpr t to
    e                       -> embed e

insertArgsBinding2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Binding (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void) 
  -> StageX1ExprYYY (Maybe Type) 
  -> Env [(Name, Name)] 
  -> StateT (Env [(Name, Name)]) m (Binding (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void Void Void), StageX1ExprYYY (Maybe Type)) -- StateT (Env [(Name, Name)]) m (a, StageX1ExprYYY (Maybe Type))
insertArgsBinding2 (BFun t name ps) expr env = do
    (t', ps', e) <- foldrM fun (t, ps, expr) (Env.toList env)
    pure (BFun t' name ps', e)
  where
    fun (var, vs) x = do
        classEnv <- askClassEnv
        set1 <- reduceSet classEnv (fst <$> vs)
        let set2 = [(x, b) | (a, b) <- vs, x <- super1 classEnv a, a `elem` set1]
        pure (foldr (fun2 set1 set2) x vs)
      where
        fun2 set1 set2 (name, dv) (t, ps, x) = do
            let
                fnx :: Type -> Bool
                fnx t = var `elem` (fst <$> free t)

            -- TODO
            if Just False == (fnx <$> workingExprTag2 x)
                then error "Ambiguity"
                else if name `elem` set1
                          then do
                              let ty = tApp kTyp (tCon kFun name) (tVar kTyp var)
                              (tArr ty <$> t, varPat (Just ty) dv:ps, x)
                          else 
                              (t, ps, replaceVar2 dv (fromJust (lookup name set2)) x)

