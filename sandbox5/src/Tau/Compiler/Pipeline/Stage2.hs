{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
module Tau.Compiler.Pipeline.Stage2 where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Tuple.Extra (second)
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type
import qualified Data.Text as Text
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1

type WorkingExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [Error] (Maybe Type))
  -> m (WorkingExpr (Maybe Type))
translate expr = evalStateT (expandTypeClasses expr) []

expandTypeClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [e] (Maybe Type))
  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
expandTypeClasses expr =
    insertDictArgs <$> run expr <*> (nub <$> pluck)
  where
    run = cata $ \case
        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            letExpr (nodeType t) (translateBinding pat) (insertDictArgs e1 vs) <$> expr2

        EFix t var expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            fixExpr (nodeType t) var (insertDictArgs e1 vs) <$> expr2

        EVar t var ->
            foldrM applyDicts (varExpr (nodeType t) var) (nodePredicates t)

        ELit t lit ->
            case lit of
                TInt     n -> undefined
                TInteger n -> undefined
                TFloat   f -> undefined
                TDouble  f -> undefined
                _          -> pure (litExpr (nodeType t) lit)

        ECon   t con es   -> conExpr (nodeType t) con <$> sequence es
        EApp   t es       -> appExpr (nodeType t) <$> sequence es
        ELam   t ps e     -> lamExpr (nodeType t) (translatePatterns <$> ps) <$> e
        EIf    t e1 e2 e3 -> ifExpr  (nodeType t) <$> e1 <*> e2 <*> e3
        EPat   t exprs clauses -> do
            es <- sequence exprs
            cs <- translateClauses <$$> traverse sequence clauses
            pure (patExpr (nodeType t) es cs)

    translateClauses = \case
        SimplifiedClause t ps g -> 
            SimplifiedClause (nodeType t) (translatePatterns <$> ps) g

    translateBinding = \case
        BLet t p         -> BLet (nodeType t) (translatePatterns p)
        BFun t name ps   -> BFun (nodeType t) name (translatePatterns <$> ps)

    translatePatterns = cata $ \case
        PVar    t var    -> varPat   (nodeType t) var
        PCon    t con ps -> conPat   (nodeType t) con ps
        PAs     t as p   -> asPat    (nodeType t) as p
        PLit    t prim   -> litPat   (nodeType t) prim
        PAny    t        -> anyPat   (nodeType t)
        POr     t p q    -> orPat    (nodeType t) p q
        PTuple  t ps     -> tuplePat (nodeType t) ps
        PList   t ps     -> listPat  (nodeType t) ps

insertDictArgs :: WorkingExpr (Maybe Type) -> [(Name, Type)] -> WorkingExpr (Maybe Type)
insertDictArgs expr = foldr fun expr
  where
    fun (var, ty) = lamExpr 
        (tArr <$> Just ty <*> workingExprTag expr) 
        [varPat (Just ty) var] 


-- alen : (Show a) -> a -> Int
-- alen x = length (show x)

-- alen x = length (show x)

applyDicts
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Predicate
  -> WorkingExpr (Maybe Type)
  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
applyDicts (InClass name ty) expr

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        undefined

    | otherwise = do
        env <- askClassEnv
        case classMethods <$> lookupClassInstance name ty env of
            Left e -> undefined -- throwError e
            Right methods -> do
                map <- traverse (secondM translateMethod) methods
                pure (fromMaybe (buildDict map) (findIn map expr))
  where
    translateMethod = expandTypeClasses 
                    . Stage1.translate 
                    . getAst 
                    . translateTag 

    translateTag = fmap (\(TypeInfo () ty ps) -> TypeInfo [] (Just ty) ps)

    findIn :: [(Name, WorkingExpr t)] -> WorkingExpr t -> Maybe (WorkingExpr t)
    findIn map = project >>> \case
        EVar _ var -> lookup var map
        _          -> Nothing

buildDict :: [(Name, WorkingExpr (Maybe Type))] -> WorkingExpr (Maybe Type)
buildDict map = undefined -- funExpr undefined (fmap fn map)

--    fn (name, expr) = SimplifiedClause (workingExprTag expr)
--        [litPat (Just tString) (TString name)]
--        (Guard [] expr)

workingExprTag :: WorkingExpr t -> t
workingExprTag = cata $ \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    ELet t _ _ _ -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EPat t _ _   -> t

    --translateMethod
    --  :: ( MonadSupply Name m
    --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
    --  => Ast (TypeInfoT () Type)
    --  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))

--expandTypeClasses
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => WorkingExpr (TypeInfoT [e] t)
--  -> StateT [(Name, Type)] m (WorkingExpr (TypeInfoT [e] t))
--expandTypeClasses expr = 
--    insertDictArgs <$> run expr <*> (nub <$> pluck)
--  where
--    run
--      :: ( MonadSupply Name m
--         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--      => WorkingExpr (TypeInfoT [e] t)
--      -> StateT [(Name, Type)] m (WorkingExpr (TypeInfoT [e] t))
--    run = cata $ \case
--        ELet t pat expr1 expr2 -> do
--            e1 <- expr1
--            vs <- nub <$> pluck
--            letExpr t pat (insertDictArgs e1 vs) <$> expr2
--
--        EFix t var expr1 expr2 -> do
--            e1 <- expr1
--            vs <- nub <$> pluck
--            fixExpr t var (insertDictArgs e1 vs) <$> expr2
--
--        EVar t var ->
--            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)
--
--        ELit t lit ->
--            case lit of
--                TInt     n -> undefined
--                TInteger n -> undefined
--                TFloat   f -> undefined
--                TDouble  f -> undefined
--                _          -> pure (litExpr t lit)
--
--        e ->
--            embed <$> sequence e
--
--insertDictArgs
--  :: WorkingExpr (TypeInfoT [e] t)
--  -> [(Name, Type)]
--  -> WorkingExpr (TypeInfoT [e] t)
--insertDictArgs expr = foldr fun expr
--  where
--    fun 
--      :: (Name, Type) 
--      -> WorkingExpr (TypeInfoT [e] t) 
--      -> WorkingExpr (TypeInfoT [e] t)
--    fun (var, ty) = lamExpr undefined [varPat undefined var] 
--
----    fun (a, b) = lamExpr (NodeInfo (tArr b (typeOf expr)) []) [varPat (NodeInfo b []) a] 
--
--applyDicts
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
--  => Predicate
--  -> WorkingExpr (TypeInfoT [e] t)
--  -> StateT [(Name, Type)] m (WorkingExpr (TypeInfoT [e] t))
--applyDicts (InClass name ty) expr
--
--    | isVar ty = do
--        tv <- Text.replace "a" "$d" <$> supply
--        undefined
--
--    | otherwise = do
--        env <- askClassEnv
--        case classMethods <$> lookupClassInstance name ty env of
--            Left e -> undefined -- throwError e
--            Right methods -> do
--                undefined
--
--setNodePredicates :: [Predicate] -> TypeInfoT [e] t -> TypeInfoT [e] t
--setNodePredicates ps info = info{ nodePredicates = ps }
--
--stripNodePredicates :: TypeInfoT [e] t -> TypeInfoT [e] t
--stripNodePredicates = setNodePredicates []

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

mapExpr :: (t -> u) -> WorkingExpr t -> WorkingExpr u
mapExpr f = cata $ \case
    EVar    t var          -> varExpr    (f t) var
    ECon    t con es       -> conExpr    (f t) con es
    ELit    t prim         -> litExpr    (f t) prim
    EApp    t es           -> appExpr    (f t) es
    EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
    ELam    t ps e         -> lamExpr    (f t) (mapPattern <$> ps) e
    EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
    EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
    ELet    t bind e1 e2   -> letExpr    (f t) (mapBind bind) e1 e2
  where
    mapBind = \case
        BLet    t p          -> BLet     (f t) (mapPattern p)
        BFun    t name ps    -> BFun     (f t) name (mapPattern <$> ps)

    mapClause = \case
        SimplifiedClause t ps g -> SimplifiedClause (f t) (mapPattern <$> ps) g

    mapPattern = cata $ \case
        PVar    t var        -> varPat   (f t) var
        PCon    t con ps     -> conPat   (f t) con ps
        PLit    t prim       -> litPat   (f t) prim
        PAs     t as p       -> asPat    (f t) as p
        POr     t p q        -> orPat    (f t) p q
        PAny    t            -> anyPat   (f t)
        PTuple  t ps         -> tuplePat (f t) ps
        PList   t ps         -> listPat  (f t) ps
--            PRecord t row        -> recordPat  (f t) row

