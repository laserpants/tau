{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StrictData           #-}
module Tau.Comp.Core where

import Control.Arrow
import Control.Monad.Error.Class (liftEither)
import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (nub)
import Data.List.Extra (groupSortOn)
import Data.Maybe (fromJust, fromMaybe)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (both, thd3)
import Data.Void
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution hiding (null)
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

--class TypeTag t where
--class (Eq t, Show t) => TypeTag t where
class (Eq t) => TypeTag t where
    tvar  :: Name -> t
    tarr  :: t -> t -> t
    tapp  :: t -> t -> t
    tbool :: t

instance TypeTag () where
    tvar _   = ()
    tarr _ _ = ()
    tapp _ _ = ()
    tbool    = ()

instance TypeTag Type where
    tvar  = tVar kTyp
    tarr  = tArr
    tapp  = tApp
    tbool = tBool

compileExpr
  :: (TypeTag t, MonadSupply Name m)
  => Expr t (Pattern t f) (Binding (Pattern t f)) [Pattern t f] Void Void
  -> m Core
compileExpr =
    expandFunPatterns
    >=> pure . desugarLists
    >=> unrollLets
    >=> simplify
    >=> toCore
    >=> optimizeCore

--compileExpr
--  :: (Pretty (Expr t (Prep t) Name Name Void Void), TypeTag t, MonadSupply Name m)
--  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] Void Void
--  -> m Core
--compileExpr e = do
--    a <- expandFunPatterns e
--    let aa = desugarLists a
--    --traceShowM (pretty a)
--    --traceShowM "1-------------------------------"
--    b <- unrollLets aa
--    traceShowM b
--    traceShowM "2-*-----------------------------"
--    c <- simplify b
--    traceShowM c
--    traceShowM "3-------------------------------"
--    d <- toCore c
--    traceShowM d
--    traceShowM "4-------------------------------"
--    pure d

expandFunPatterns
  :: (MonadSupply Name m)
  => Expr t (Pattern t f) q [Pattern t f] Void Void
  -> m (Expr t (Pattern t f) q [Pattern t f] Void Void)
expandFunPatterns = cata $ \case

    EPat t [] exs@(Clause ps _ e:_) -> do
        (_, exprs, pats) <- patternInfo varPat ps
        body <- e
        let e1 = patExpr (exprTag body) exprs
        lamExpr t pats . e1 <$> traverse sequence exs

    e ->
        embed <$> sequence e

unrollLets
  :: (TypeTag t, MonadSupply Name m)
  => Expr t p (Binding (Pattern t f)) [Pattern t f] Void Void
  -> m (Expr t p (Pattern t f) [Pattern t f] Void Void)
unrollLets = cata $ \case

    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    ELam t pat e1    -> lamExpr t pat <$> e1
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat t eqs exs   -> patExpr t <$> sequence eqs <*> traverse sequence exs
    EDot t e1 e2     -> dotExpr t <$> e1 <*> e2
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs

    ELet t (BLet pat) e1 e2 ->
        letExpr t pat <$> e1 <*> e2

    ELet t (BFun f ps) e1 e2 -> do
        vars <- supplies (length ps)
        expr <- e1
        let t1 = foldr tarr (exprTag expr) (patternTag <$> ps)
        letExpr t (varPat t1 f) (lamExpr t1 ps expr) <$> e2

simplify
  :: (TypeTag t, MonadSupply Name m)
  => Expr t (Pattern t f) (Pattern t f) [Pattern t f] Void Void
  -> m (Expr t (Prep t) Name Name Void Void)
simplify = cata $ \case
    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EDot t e1 e2     -> dotExpr t <$> e1 <*> e2
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs

    -- TODO: Check for disallowed patterns

    ELet t (Fix (PVar _ var)) e1 e2 ->
        letExpr t var <$> e1 <*> e2

    ELet _ pat e1 e2 -> do
        expr <- e1
        body <- e2
        exs <- expandPatterns [Clause [pat] [] body]
        compilePatterns [expr] exs

    ELam _ ps e1 -> do
        (vars, exprs, _) <- patternInfo varPat ps
        body <- e1
        expr <- expandPatterns [Clause ps [] body] >>= compilePatterns exprs
        let toLam v t e = lamExpr (tarr t (exprTag e)) v e
        pure (foldr (uncurry toLam) expr vars)

    EPat _ eqs exs -> do
        exs1 <- traverse sequence exs
        join (compilePatterns <$> sequence eqs <*> expandPatterns exs1)

expandPatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t f) (Expr t p q r n o)]
  -> m [Clause (Pattern t PatternsExpanded) (Expr t p q r n o)]
expandPatterns = (toExpanded <$$>) . expandLitPatterns . expandOrPatterns 
  where
    toExpanded (Clause ps exs e) = Clause (patternsExpanded <$> ps) exs e

expandLitPatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t f) (Expr t p q r n o)]
  -> m [Clause (Pattern t f) (Expr t p q r n o)]
expandLitPatterns = traverse expandClause
  where
    expandClause (Clause ps exs e) = do
        (qs, exs1) <- runWriterT (traverse expand1 ps)
        pure (Clause qs (exs <> exs1) e)

    expand1 = cata $ \case
        PLit t lit -> do
            var <- supply
            tell [appExpr tbool
                     [ varExpr (tarr t (tarr t tbool)) ("@" <> literalName lit <> ".(==)")
                     , varExpr t var
                     , litExpr t lit ]]
            pure (varPat t var)

        p ->
            embed <$> sequence p

expandOrPatterns :: [Clause (Pattern t f) a] -> [Clause (Pattern t f) a]
expandOrPatterns = concatMap $ \(Clause ps exs e) ->
    [Clause qs exs e | qs <- traverse fork ps]
  where
    -- TODO: cata??
    fork :: Pattern t f -> [Pattern t f]
    fork = project >>> \case
        PCon t con ps  -> conPat t con <$> traverse fork ps
        PTup t ps      -> tupPat t <$> traverse fork ps
        PRec t fields  -> recPat t <$> traverse fork fields
        PLst t ps      -> lstPat t <$> traverse fork ps
        PAs  t name a  -> asPat t name <$> fork a
        POr  _ a b     -> fork a <> fork b
        p              -> [embed p]

compilePatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name Void Void]
  -> [Clause (Pattern t PatternsExpanded) (Expr t (Prep t) Name Name Void Void)]
  -> m (Expr t (Prep t) Name Name Void Void)
compilePatterns us qs = matchAlgo us qs (varExpr (tvar "FAIL") "FAIL")

andExpr :: (TypeTag t) => Expr t p q r n o -> Expr t p q r n o -> Expr t p q r n o
andExpr a b = appExpr tbool [varExpr (tarr tbool (tarr tbool tbool)) "@(&&)", a, b]

-- | based on the pattern matching compilers described in [1] and [2] ...
--
-- References:
--
--   - [1] Augustsson L. (1985) Compiling pattern matching.
--   - [2] Peyton Jones, Simon & Lester, David. (2000). Implementing functional languages: a tutorial. 
--
-- In this stage ...
--
--   - ...
--   - List patterns [1, 2, 3] (so called list literals) are translated to 1 :: 2 :: 3 :: []
--
matchAlgo
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name Void Void]
  -> [Clause (Pattern t PatternsExpanded) (Expr t (Prep t) Name Name Void Void)]
  -> Expr t (Prep t) Name Name Void Void
  -> m (Expr t (Prep t) Name Name Void Void)
matchAlgo [] []                   c = pure c
matchAlgo [] (Clause [] []  e:_)  _ = pure e
matchAlgo [] (Clause [] exs e:qs) c =
    ifExpr (exprTag c) (foldr1 andExpr exs) e <$> matchAlgo [] qs c
matchAlgo (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] ->
            matchAlgo us (runSubst <$> eqs) c
          where
            runSubst (Clause (Fix (PVar t name):ps) exs e) =
                substitute name u <$> Clause ps exs e

            runSubst (Clause (Fix (PAs _ as (Fix (PVar t name))):ps) exs e) = 
                substitute name u . substitute as (varExpr t name) <$> Clause ps exs e

            runSubst (Clause (Fix (PAs _ as (Fix (PAny t))):ps) exs e) = 
                substitute as u <$> Clause ps exs e

            -- The remaining case is for wildcard and literal patterns
            runSubst (Clause (Fix _:ps) exs e) =
                Clause ps exs e

        [Constructor eqs@(Clause _ _ e:_)] -> do
            qs' <- traverse (toSimpleMatch c) (consGroups u eqs)
            pure $ case qs' <> [Clause [RCon (exprTag u) "$_" []] [] c | not (isError c)] of
                []   -> c
                qs'' -> patExpr (exprTag e) [u] qs''

          where
            toSimpleMatch c ConsGroup{..} = do
                (_, vars, pats) <- patternInfo (const id) consPatterns
                expr <- matchAlgo (vars <> us) consClauses c
                pure (Clause [RCon consType consName pats] [] expr)

            isError :: Expr t p q r n o -> Bool
            isError = cata $ \case
                EVar _ var | "FAIL" == var -> True
                _                          -> False

        mixed -> do
            foldrM (matchAlgo (u:us)) c (clauses <$> mixed)

data ConsGroup t n o f = ConsGroup 
    { consName     :: Name
    , consType     :: t
    , consPatterns :: [Pattern t f]
    , consClauses  :: [Clause (Pattern t f) (Expr t (Prep t) Name Name n o)]
    } deriving (Show, Eq)

consGroups :: Expr t (Prep t) Name Name n o -> [Clause (Pattern t f) (Expr t (Prep t) Name Name n o)] -> [ConsGroup t n o f]
consGroups u cs = concatMap grp (groupSortOn fst (info <$> cs))
  where
    grp all@((con, (t, ps, _)):_) =
        [ConsGroup con t ps (thd3 . snd <$> all)]

    info (Clause (p:qs) exs e) =
        case project (desugarPattern p) of
            PCon t con ps ->
                (con, (t, ps, Clause (ps <> qs) exs e))

            PAs _ as q ->
                info (Clause (q:qs) exs (substitute as u e))

desugarPattern :: Pattern t f -> Pattern t f
desugarPattern = cata $ \case
    PRec t (FieldSet fields) ->
        conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields)
    PTup t elems ->
        conPat t (tupleCon (length elems)) elems
    PLst t elems ->
        foldr (listConsPat t) (conPat t "[]" []) elems
    p ->
        embed p

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

labeledClause :: Clause (Pattern t f) a -> Labeled (Clause (Pattern t f) a)
labeledClause eq@(Clause (p:_) _ _) = f p where
    f = project >>> \case
        POr{}     -> error "Implementation error"
        PAs _ _ q -> f q
        PCon{}    -> Constructor eq
        PTup{}    -> Constructor eq
        PRec{}    -> Constructor eq
        PLst{}    -> Constructor eq
        PVar{}    -> Variable eq
        PAny{}    -> Variable eq
        PLit{}    -> Variable eq

clauseGroups :: [Clause (Pattern t f) a] -> [Labeled [Clause (Pattern t f) a]]
clauseGroups = cata alg . fmap labeledClause where
    alg Nil = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts)) = Variable (e:es):ts
    alg (Cons (Constructor e) ts) = Constructor [e]:ts
    alg (Cons (Variable e) ts) = Variable [e]:ts

patternInfo
  :: (MonadSupply Name m)
  => (t -> Name -> a)
  -> [Pattern t f]
  -> m ([(Name, t)], [Expr t p q r n o], [a])
patternInfo con pats = do
    vars <- supplies (length pats)
    let ts = patternTag <$> pats
        make c = uncurry c <$> zip ts vars
    pure (zip vars ts, make varExpr, make con)

substitute
  :: Name
  -> Expr t (Prep t) Name Name n o
  -> Expr t (Prep t) Name Name n o
  -> Expr t (Prep t) Name Name n o
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> letExpr t pat e1 e2'
      where
        e2' | name == pat = fst e2
            | otherwise   = snd e2

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EPat t exs eqs ->
        patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Clause ps _ _)
            | name `elem` (pats =<< ps) = fst <$> eq
            | otherwise                 = snd <$> eq
        pats (RCon _ _ ps) = ps

    expr -> snd <$> expr & \case
        EVar t var
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e

sequenceExs :: (Monad m) => [m Core] -> m Core
sequenceExs = (fun <$>) . sequence where 
    fun = \case 
        [e] -> e
        xs  -> cApp xs

toCore :: (MonadSupply Name m) => Expr t (Prep t) Name Name Void Void -> m Core
toCore = cata $ \case
    EVar _ var       -> pure (cVar var)
    ELit _ lit       -> pure (cLit lit)
    EIf  _ e1 e2 e3  -> cIf <$> e1 <*> e2 <*> e3
    EApp _ exs       -> sequenceExs exs
    ECon _ con exs   -> sequenceExs (pure (cVar con):exs)
    ELet _ var e1 e2 -> cLet var <$> e1 <*> e2
    EFix _ var e1 e2 -> cLet var <$> e1 <*> e2
    ELam _ var e1    -> cLam var <$> e1
    EDot _ e1 e2     -> sequenceExs [e2, e1]

    ERec _ (FieldSet fields) -> do
        exprs <- traverse fieldValue fields
        pure (cApp (cVar (recordCon (fieldName <$> fields)):exprs))

    ETup _ exs -> do
        exprs <- sequence exs
        pure (cApp (cVar (tupleCon (length exs)):exprs))

    EPat _ eqs exs -> do
        cs <- sequence eqs
        case cs of
            [expr] -> cPat expr <$> traverse desugarClause exs
            _      -> error "Implementation error"
  where
    desugarClause (Clause [RCon _ con ps] [] e) = 
        (,) (con:ps) <$> e
    desugarClause _ =
        error "Implementation error"

optimizeCore :: (MonadSupply Name m) => Core -> m Core
optimizeCore = cata $ \case

    CIf e1 e2 e3 -> do
        a <- project <$> e2
        b <- project <$> e3
        if a == b || CVar "FAIL" == b
            then e2
            else cIf <$> e1 <*> e2 <*> e3

    e -> embed <$> sequence e

desugarOperators :: Expr t p q r (Op1 t) (Op2 t) -> Expr t p q r Void Void
desugarOperators = cata $ \case

    EOp1 t op a -> 
        appExpr t [prefix1 op, a]

    EOp2 t op a b -> 
        appExpr t [prefix2 op, a, b]

    EVar t var       -> varExpr t var
    ECon t con exs   -> conExpr t con exs
    ELit t lit       -> litExpr t lit
    EApp t exs       -> appExpr t exs
    ELet t e1 e2 e3  -> letExpr t e1 e2 e3
    EFix t var e1 e2 -> fixExpr t var e1 e2
    ELam t pat e1    -> lamExpr t pat e1
    EIf  t e1 e2 e3  -> ifExpr  t e1 e2 e3
    EPat t eqs exs   -> patExpr t eqs exs
    EDot t name e1   -> dotExpr t name e1
    ERec t fields    -> recExpr t fields
    ETup t exs       -> tupExpr t exs
    ELst t exs       -> lstExpr t exs

  where
    prefix1 (ONeg t) = varExpr t "negate"
    prefix1 (ONot t) = varExpr t "not"
    prefix2 op = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")

desugarLists :: Expr t p q r n o -> Expr t p q r n o
desugarLists = cata $ \case
    ELst t exs -> foldr (listConsExpr t) (conExpr t "[]" []) exs
    e          -> embed e

-- ============================================================================
-- Type classes
-- ============================================================================

compileClasses 
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m)
  => Ast (NodeInfoT Type) Void Void f
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type) Void Void f) 
compileClasses expr = 
    insertDictArgs <$> run expr <*> collect
  where
    run = cata $ \case

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            xs <- collect
            letExpr t pat (insertDictArgs e1 xs) <$> expr2

        EVar t var -> 
            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)

        e -> 
            embed <$> sequence e

insertDictArgs :: Ast NodeInfo Void Void f -> [(Name, Type)] -> Ast NodeInfo Void Void f
insertDictArgs expr = foldr fun expr
  where
    fun (a, b) = lamExpr (NodeInfo (tArr b (typeOf expr)) []) [varPat (NodeInfo b []) a] 

collect :: (MonadState [(Name, Type)] m) => m [(Name, Type)]
collect = nub <$> acquireState

applyDicts
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m)
  => Predicate
  -> Ast (NodeInfoT Type) Void Void f
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type) Void Void f)
applyDicts (InClass name ty) expr 

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
            dict = varExpr (NodeInfo t []) tv
        modify ((tv, t) :)
        let expr' = setExprTag (NodeInfo (t `tArr` typeOf expr) []) expr
        pure (appExpr (exprTag expr) [expr', dict])

    | otherwise = do
        env <- asks fst
        case lookupClassInstance name ty env of
            Left e -> throwError e
            Right (_ , Instance{..}) -> do

                -- TODO: super-classes???

                dict <- compileClasses (desugarOperators instanceDict)

                let def = appExpr (exprTag expr) 
                            [ setExprTag (NodeInfo (typeOf dict `tArr` typeOf expr) []) expr
                            , dict ]

                pure $ case (project expr, project dict) of
                    (EVar _ var, ERec _ fields) -> 
                        maybe def snd (lookupField var fields)
                    _ -> 
                        def
                        
setNodeType :: Type -> NodeInfo -> NodeInfo
setNodeType ty info = info{ nodeType = ty }

setNodePredicates :: [Predicate] -> NodeInfoT a -> NodeInfoT a
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: NodeInfoT a -> NodeInfoT a
stripNodePredicates = setNodePredicates []

-- ============================================================================
-- Pattern anomalies check
-- ============================================================================

type ConstructorEnv = Env (Set Name)

constructorEnv :: [(Name, [Name])] -> ConstructorEnv
constructorEnv = Env.fromList . (Set.fromList <$$>)

headCons :: [[Pattern t f]] -> [(Name, [Pattern t f])]
headCons = (>>= fun) 
  where
    fun :: [Pattern t f] -> [(Name, [Pattern t f])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) = 
        case project p of
            PLit _ lit -> 
                [(prim lit, [])]

            PCon _ name rs -> 
                [(name, rs)]

            PRec t (FieldSet fields) ->
                fun (conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields):ps)

            PTup t elems ->
                fun (conPat t (tupleCon (length elems)) elems:ps)

            PLst t elems ->
                fun (foldr (listConsPat t) (conPat t "[]" []) elems:ps)

            PAs _ _ q -> 
                fun (q:ps)

            POr _ a b -> 
                fun (a:ps) <> fun (b:ps)

            _ -> 
                []

    prim (LBool True)  = "#True"
    prim (LBool False) = "#False"
    prim LUnit         = "#()"
    prim LInt{}        = "#Int"
    prim LInteger{}    = "#Integer"
    prim LFloat{}      = "#Float"
    prim LChar{}       = "#Char"
    prim LString{}     = "#String"

defaultMatrix :: [[Pattern t f]] -> [[Pattern t f]]
defaultMatrix = (fun =<<)
  where 
    fun :: [Pattern t f] -> [[Pattern t f]]
    fun (p:ps) =
        case project p of
            PCon{}    -> []
            PRec{}    -> []
            PTup{}    -> []
            PLst{}    -> []
            PLit{}    -> []
            PAs _ _ q -> fun (q:ps)
            POr _ q r -> fun (q:ps) <> fun (r:ps)
            _         -> [ps]

specialized :: Name -> [t] -> [[Pattern t f]] -> [[Pattern t f]]
specialized name ts = concatMap rec 
  where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ con rs
                | con == name -> [rs <> ps]
                | otherwise   -> []

            PRec t (FieldSet fields) -> do
                -- TODO: DRY
                let q = conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields)
                rec (q:ps)

            PTup t elems -> do
                -- TODO: DRY
                let q = conPat t (tupleCon (length elems)) elems
                rec (q:ps)

            PLst t elems -> do
                -- TODO: DRY
                let q = foldr (listConsPat t) (conPat t "[]" []) elems
                rec (q:ps)

            PAs _ _ q ->
                rec (q:ps)

            POr _ p1 p2 ->
                rec (p1:ps) <> rec (p2:ps)

            _ ->
                [(anyPat <$> ts) <> ps]

-- TODO: rename
data AType t f
    = ACon Name [Pattern t f] 
    | AOr (Pattern t f) (Pattern t f) 
    | AAny

getA :: Pattern t f -> AType t f
getA = project >>> \case
    PCon _ con rs -> 
        ACon con rs

    PRec t (FieldSet fields) -> 
        -- TODO: DRY
        getA (conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields))

    PTup t elems ->
        -- TODO: DRY
        getA (conPat t (tupleCon (length elems)) elems)

    PLst t elems ->
        -- TODO: DRY
        getA (foldr (listConsPat t) (conPat t "[]" []) elems)

    PAs _ _ a -> 
        getA a

    POr _ a b -> 
        AOr a b

    _ -> 
        AAny

-- |
--
-- References:
--
--   - http://moscova.inria.fr/~maranget/papers/warn/ 
--
useful :: (MonadReader ConstructorEnv m) => [[Pattern t f]] -> [Pattern t f] -> m Bool
useful [] _   = pure True   -- Zero rows (0x0 matrix)
useful (p1:_) qs 
    | null p1 = pure False  -- One or more rows but no columns
    | null qs = error "Implementation error (useful)"
useful pss (q:qs) =
    case getA q of
        ACon con rs  ->
            let special = specialized con (patternTag <$> rs)
             in useful (special pss) (head (special [q:qs]))
        AAny -> do
            let cs = headCons pss
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (patternTag <$> rs)
                     in useful (special pss) (head (special [q:qs]))) 
                else 
                    useful (defaultMatrix pss) qs
        AOr a b -> 
            useful pss (a:qs) ||^ useful pss (b:qs)
  where
    complete [] = pure False
    complete names@(name:_) = do
        defined <- ask
        pure (lookupCon (defined `Env.union` builtIn) name == Set.fromList names)
    lookupCon constructors con 
        | isTupleCon con || isRecordCon con = Set.singleton con
        | otherwise = Env.findWithDefaultEmpty con constructors

    builtIn = constructorEnv
        [ ("#True",     ["#True", "#False"])
        , ("#False",    ["#True", "#False"])
        , ("#()",       ["#()"])
        , ("#Int",      [])
        , ("#Integer",  [])
        , ("#Float",    [])
        , ("#Char",     [])
        , ("#String",   []) 
        , ("[]",        ["[]", "(::)"]) 
        , ("(::)",      ["[]", "(::)"]) 
        ]

isTupleCon :: Name -> Bool
isTupleCon con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

isRecordCon :: Name -> Bool
isRecordCon con = ("{", "}") == fstLst con
  where
    fstLst ""  = ("", "")
    fstLst con = both Text.singleton (Text.head con, Text.last con)

exhaustive :: (MonadReader ConstructorEnv m) => [[Pattern t f]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause (Pattern t f) a] -> m Bool
clausesAreExhaustive = exhaustive . concatMap toMatrix where
    toMatrix (Clause ps [] _) = [ps]
    toMatrix _                = []

checkExhaustive :: (MonadReader ConstructorEnv m) => Ast t (Op1 t) (Op2 t) f -> m Bool
checkExhaustive = cata $ \case
    ECon _ _ exprs           -> andM exprs
    EApp _ exprs             -> andM exprs
    ELet _ (BLet p) e1 e2    -> exhaustive [[p]] &&^ e1 &&^ e2
    ELet _ (BFun f ps) e1 e2 -> exhaustive [ps] &&^ e1 &&^ e2
    EFix _ _ e1 e2           -> e1 &&^ e2
    ELam _ ps e1             -> exhaustive [ps] &&^ e1
    EIf _ cond tr fl         -> cond &&^ tr &&^ fl
    EPat _ exs eqs           -> andM exs &&^ clausesAreExhaustive eqs
    EOp1 _ _ a               -> a
    EOp2 _ _ a b             -> a &&^ b
    EDot _ a b               -> a &&^ b
    ERec _ (FieldSet fields) -> andM (fieldValue <$> fields)
    ETup _ elems             -> andM elems
    ELst _ elems             -> andM elems
    --  | EAnn s a 
    _                        -> pure True

astApply :: Substitution -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f
astApply sub = mapTags (apply sub :: NodeInfo -> NodeInfo)

extractType :: Ast NodeInfo Void Void f -> Ast Type Void Void f
extractType = (mapTags :: (NodeInfo -> Type) -> Ast NodeInfo Void Void f -> Ast Type Void Void f) nodeType

--toUnitType :: Expr t (Prep t) Name Name Void Void -> Expr () (Prep ()) Name Name Void Void
--toUnitType = mapTags (const ())
