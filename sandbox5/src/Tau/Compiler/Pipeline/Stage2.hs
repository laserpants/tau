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
translate expr = evalStateT (expandTypeClasses =<< translateLiterals expr) []

translateLiterals 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => WorkingExpr (TypeInfoT [e] (Maybe Type))
  -> StateT [(Name, Type)] m (WorkingExpr (TypeInfoT [e] (Maybe Type)))
translateLiterals = cata $ \case
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse sequence cs

    ELit t (TInt n) -> 
        pure (appExpr t 
            [ varExpr (t{ nodeType = tArr tInteger <$> nodeType t }) "fromInteger"
            , litExpr (TypeInfo [] (Just tInteger) []) (TInteger (fromIntegral n)) ])

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

        ELit   t lit      -> pure (litExpr (nodeType t) lit)
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
insertDictArgs = foldr fun 
  where
    fun (var, ty) e = 
        lamExpr (tArr <$> Just ty <*> workingExprTag e) 
                [varPat (Just ty) var] e

dictTVar :: (MonadSupply Name m) => Type -> StateT [(Name, Type)] m Name
dictTVar ty = do
    map <- get
    case filter ((==) ty . snd) map of
        p:_ -> pure (fst p)
        _ -> do 
            var <- Text.replace "a" "$dict" <$> supply
            modify ((var, ty) :)
            pure var

applyDicts
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Predicate
  -> WorkingExpr (Maybe Type)
  -> StateT [(Name, Type)] m (WorkingExpr (Maybe Type))
applyDicts (InClass name ty) expr

    | isVar ty = do
        tv <- dictTVar t1
        pure (appExpr (workingExprTag expr) 
          [ setWorkingExprTag (tArr t1 <$> workingExprTag expr) expr
          , varExpr (Just t1) tv ])

    | otherwise = do
        env <- askClassEnv
        case classMethods <$> lookupClassInstance name ty env of
            Left e -> undefined -- throwError e
            Right methods -> do
                map <- traverse (secondM translateMethod) methods
                pure (fromMaybe (buildDict map) (findIn map expr))
  where
    t1 = tApp kTyp (tCon (kArr kTyp kClass) name) ty

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
    buildDict map = 
        conExpr (Just t1) "#" [row]
      where 
        row = foldr fn (conExpr (Just tRowNil) "{}" []) map
        fn (name, expr) e = 
            let row = tRowExtend name <$> workingExprTag expr <*> workingExprTag e
             in rowCons row name expr e

setWorkingExprTag :: t -> WorkingExpr t -> WorkingExpr t
setWorkingExprTag t = cata $ \case
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
