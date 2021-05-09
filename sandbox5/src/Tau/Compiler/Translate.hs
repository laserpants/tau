{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Tau.Compiler.Translate where

import Control.Arrow ((<<<), (>>>), (***), second)
import Control.Monad
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Void
import Tau.Compiler.Error
import Tau.Lang
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

--data Prep t = RCon t Name [Name]
--    deriving (Show, Eq)
--
--data Labeled a
--    = Constructor a
--    | Variable a
--    deriving (Show, Eq, Ord)

class InfoTag t where
    typeToTag  :: Type -> t
    tagToType  :: t -> Type
    updateType :: (Type -> Type) -> t -> t

instance InfoTag (TypeInfo [e]) where
    typeToTag t  = TypeInfo t [] []
    tagToType it = nodeType it
    updateType   = fmap 

instance InfoTag () where
    typeToTag _    = ()
    tagToType _    = tVar kTyp "a"
    updateType _ _ = ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data SimplifiedClause t p a = SimplifiedClause t [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''SimplifiedClause
deriveEq1   ''SimplifiedClause
deriveOrd1  ''SimplifiedClause

--type DesugaredPattern t = Pattern t t t t t t Void Void Void
--type DesugaredExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (DesugaredPattern t))
--
--type SimplifiedPattern t = Pattern t t t Void Void Void Void Void Void
--type SimplifiedExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t))

simplifyExpr 
  :: (Typed t, InfoTag t) 
  => ProgExpr t 
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
simplifyExpr = cata $ \case

    -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    --    ERecord t row        -> conExpr t "#Record" [desugarRow row]
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
    -- Expand pattern clause guards
    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
    EFun    t cs         -> let (t1, t2) = split t in lamExpr t "#0" (patExpr t2 [varExpr t1 "#0"] (expandClause =<< cs))
    -- Unroll lambdas
    ELam    t ps e       -> unrollLambda ps e
    -- Translate let expressions
    ELet    t bind e1 e2 -> desugarLet t bind e1 e2
    -- Remaining values are unchanged
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3

  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"

    expandClause (Clause t ps gs) = [SimplifiedClause t ps es e | Guard es e <- gs]

split :: (InfoTag t) => t -> (t, t)
split t = (updateType (const t1) t, updateType (const t2) t)
  where
    Fix (TArr t1 t2) = tagToType t

unrollLambda 
  :: (Typed t, InfoTag t) 
  => [ProgPattern t] 
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t)) 
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
unrollLambda ps e = fst (foldr f (e, tag e) ps)
  where
    f p (e, t) =
        let t' = updateType (tArr (typeOf (patternTag p))) t
         in (lamExpr t' "#0" (patExpr t [varExpr (patternTag p) "#0"] [SimplifiedClause t [p] [] e]), t')

    tag = cata $ \case
        EVar t _     -> t
        ECon t _ _   -> t
        ELit t _     -> t
        EApp t _     -> t
        EFix t _ _ _ -> t
        ELam t _ _   -> t
        EIf  t _ _ _ -> t
--        EPat t _ _   -> t

desugarLet 
  :: (Typed t, InfoTag t) 
  => t
  -> Binding t (ProgPattern t)
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t)) 
  -> Expr t t t t t t t Void t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
desugarLet t bind e1 e2 = patExpr t [e] [SimplifiedClause t [p] [] e2]
  where
    (e, p) = case bind of
        BLet _ pat   -> (e1, pat)
        BFun _ f ps  -> (unrollLambda ps e1, varPat t f)

--unrollLambda2
--  :: (Typed t, InfoTag t) 
--  => t 
--  -> [ProgPattern t] 
--  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t)) 
--  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
--unrollLambda2 = undefined


---- let f [x, y] = e in z
----
---- let f = \x y -> e in z
----
---- match \x y -> e with
----   | f => z
--
----unrollLambda t ps e
--
----  where
----    (e, p) = case bind of
----        BLet _ pat   -> (e1, pat)
----        BFun t f ps  -> (fst $ foldr unrollLambda (e1, t) ps, varPat t f)
--
--
----dom :: Type -> Type
----dom = project >>> \case
----    TArr a b -> a
----    t        -> error (show t) -- embed t
----
----
----cod :: Type -> Type
----cod = project >>> \case
----    TArr a b -> b
----    t        -> error (show t) -- embed t
--
----
----
----
----
--
--simplifyExpr :: (InfoTag ti) => ProgExpr ti -> SimplifiedExpr ti
--simplifyExpr = cata $ \case
--
-- -- Translate tuples, lists, and records
--    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
--    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
--    ERecord t row        -> conExpr t "#Record" [desugarRow row]
-- -- Translate operators to prefix form
--    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
--    EOp2    t op a b     -> appExpr t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
-- -- Expand pattern clause guards
--    EPat    t es cs      -> undefined
--    EFun    t cs         -> undefined
-- -- Unroll lambdas
--    ELam    t ps e       -> unrollLambda t ps e
-- -- Translate let expressions
--    ELet    t bind e1 e2 -> undefined
-- -- Remaining values are unchanged
--    EVar    t var        -> varExpr t var
--    ECon    t con es     -> conExpr t con es
--    ELit    t prim       -> litExpr t prim
--    EApp    t es         -> appExpr t es
--    EFix    t name e1 e2 -> fixExpr t name e1 e2
--    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
--
--  where
--    prefixOp1 (ONeg t) = varExpr t "negate"
--    prefixOp1 (ONot t) = varExpr t "not"
--
--    unrollLambda ti ps e = fst (foldr f (e, tagToType ti) ps)
--      where
--        f p (e, t) = (funExpr undefined [SimplifiedClause undefined [faz p] [] e], t)
--        -- f p (e, t) = (funExpr t [SimplifiedClause t [p] [] e], t)
--
--faz :: ProgPattern t -> SimplifiedPattern t -- Pattern t t t t t t t t t -> Pattern t t t Void Void Void Void Void Void
--faz = undefined
--
--desugarRow
--  :: (Functor clause, InfoTag t) 
--  => Row (Expr t t t t t t t t Void Void Void Void Void Void Void bind lam clause)
--  -> Expr t t t t t t t t Void Void Void Void Void Void Void bind lam clause
--desugarRow (Row map r) =
--    Map.foldrWithKey fun (fromMaybe (conExpr (typeToTag (tCon kRow "{}")) "{}" []) r) map
--  where
--    fun key = flip (foldr f)
--      where
--        field = "{" <> key <> "}"
--        f d e = conExpr (updateType (fun (tag e)) (tag d)) field [d, e]
--        fun s t = tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) field) t) (tagToType s)
--
--    tag = cata $ \case
--        EVar t _     -> t
--        ECon t _ _   -> t
--        ELit t _     -> t
--        EApp t _     -> t
--        EFix t _ _ _ -> t
--        ELam t _ _   -> t
--        EIf  t _ _ _ -> t
--        EPat t _ _   -> t
--
--
----simplifyExpr :: (Tag t, MonadSupply Name m) => ProgExpr t -> m (SimplifiedExpr t)
----simplifyExpr = simplifyExprPatterns <=< desugarExprPatterns <<< cata (\case
---- -- Translate tuples, lists, and records
----    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
----    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
----    ERecord t row        -> conExpr (rowTag (eTag <$> row)) "#Record" [desugarRow eTag conExpr row]
---- -- Translate operators to prefix form
----    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
----    EOp2    t op a b     -> appExpr t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
---- -- Expand pattern clause guards
----    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
----    EFun    t cs         -> funExpr t (expandClause =<< cs)
---- -- Unroll lambdas
----    ELam    t ps e       -> fst $ foldr unrollLambda (e, t) ps
---- -- Translate let expressions
----    ELet    t bind e1 e2 -> desugarLet t bind e1 e2
---- -- Remaining values are unchanged
----    EVar    t var        -> varExpr t var
----    ECon    t con es     -> conExpr t con es
----    ELit    t prim       -> litExpr t prim
----    EApp    t es         -> appExpr t es
----    EFix    t name e1 e2 -> fixExpr t name e1 e2
----    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3)
----  where
----    prefixOp1 (ONeg t) = varExpr t "negate"
----    prefixOp1 (ONot t) = varExpr t "not"
----
----    expandClause (Clause t ps gs) = [SimplifiedClause t ps es e | Guard es e <- gs]
----
----    desugarLet t bind e1 e2 = patExpr t [e] [SimplifiedClause t [p] [] e2]
----      where
----        (e, p) = case bind of
----            BLet _ pat   -> (e1, pat)
----            BFun t f ps  -> (fst $ foldr unrollLambda (e1, t) ps, varPat t f)
----
----    -- TODO
----    unrollLambda p (e, t) = (traceShow t $ funExpr t [SimplifiedClause t [p] [] e], t)
----
------        lamExpr undefined "$!" (patExpr undefined [varExpr undefined "$!"] [SimplifiedClause undefined [] [] e])
----
----
------    ELam    t ps e       -> foldr (\p e1 -> lamExpr (tarr (patternTag p) (eTag e1)) p e1) e ps
----
------            BFun t1 f ps -> (foldr (\p e -> lamExpr (tarr (patternTag p) (eTag e)) p e) e1 ps, varPat t1 f)
----
----    eTag = cata $ \case
----        EVar    t _      -> t
----        ECon    t _ _    -> t
----        ELit    t _      -> t
----        EApp    t _      -> t
----        EFix    t _ _ _  -> t
------        ELam    t _ _    -> t
----        EIf     t _ _ _  -> t
------        EPat    t _ _    -> t
----
------removeFunExprs 
------  :: (Tag t, MonadSupply Name m)
------  => Expr t t t t t t t t t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
------  -> m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t)))
------removeFunExprs = cata $ \case
------
------    EVar    t var        -> pure (varExpr t var)
------    ECon    t con es     -> conExpr t con <$> sequence es
--------    ELit    t prim       -> pure (litExpr t prim)
--------    EApp    t es         -> appExpr t <$> sequence es
--------    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--------    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
--------    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse translClause cs
--------    ELam    t p e        -> lamExpr t p <$> e
------
------    EFun    t cs         -> undefined
----
------  => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
----
----desugarExprPatterns
----  :: (Tag t, MonadSupply Name m)
----  => Expr t t t t t t t t t Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
----  -> m (DesugaredExpr t)
----desugarExprPatterns = cata $ \case
----
----    EVar    t var        -> pure (varExpr t var)
----    ECon    t con es     -> conExpr t con <$> sequence es
----    ELit    t prim       -> pure (litExpr t prim)
----    EApp    t es         -> appExpr t <$> sequence es
----    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
----    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
----    ELam    t p e        -> lamExpr t p <$> e
----
----    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse translClause cs
----    EFun    t clauses    -> do
----        cs <- traverse translClause clauses
----        let tags = clausePatterns (head cs)
----            vars = (`varExpr` "#0") <$> tags
----
----        pure (foldr (\p e -> lamExpr (eTag e) "#0" e) (patExpr t vars cs) tags)
----
------        let tags = split cs
------        let vars = (`varExpr` "#0") <$> tags
------        pure (foldr (\p e -> lamExpr (tarr p (eTag e)) "#0" e) (patExpr t vars cs) tags)
----  where
----    translClause (SimplifiedClause t ps es e) =
----        SimplifiedClause t (desugarPatterns <$> ps) <$> sequence es <*> e
----
----    clausePatterns (SimplifiedClause _ ps _ _) = pTag <$> ps
----
----    eTag = cata $ \case
----        EVar    t _          -> t
----        ECon    t _ _        -> t
----        ELit    t _          -> t
----        EApp    t _          -> t
----        EFix    t _ _ _      -> t
----        EIf     t _ _ _      -> t
----        ELam    t _ _        -> t
----        EPat    t _ _        -> t
----
----    pTag = cata $ \case
----        PVar    t _          -> t
----        PCon    t _ _        -> t
----        PLit    t _          -> t
----        PAs     t _ _        -> t
----        POr     t _ _        -> t
----        PAny    t            -> t
----
----rowTag :: (Tag t) => Row t -> t
----rowTag row = tapp (typeToTag tRecordCon) (rowToTag row)
----
----desugarPatterns :: (Tag t) => ProgPattern t -> DesugaredPattern t
----desugarPatterns = cata $ \case
----
----    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
----    PList   t ps         -> foldr (listConsPat t) (conPat t "[]" []) ps
----    PRecord t row        -> conPat (rowTag (pTag <$> row)) "#Record" [desugarRow pTag conPat row]
----
----    PVar    t var        -> varPat t var
----    PCon    t con ps     -> conPat t con ps
----    PLit    t prim       -> litPat t prim
----    PAs     t as p       -> asPat  t as p
----    POr     t p q        -> orPat  t p q
----    PAny    t            -> anyPat t
----  where
----    pTag = cata $ \case
----        PVar    t _          -> t
----        PCon    t _ _        -> t
----        PLit    t _          -> t
----        PAs     t _ _        -> t
----        POr     t _ _        -> t
----        PAny    t            -> t
----
----desugarRow :: (Tag t) => (a -> t) -> (t -> Name -> [a] -> a) -> Row a -> a
----desugarRow untag con (Row map r) = Map.foldrWithKey fun (initl r) map
----  where
----    initl = fromMaybe (con (tcon kRow "{}") "{}" [])
----    fun key =
----        let kind  = kArr kTyp (kArr kRow kRow)
----            field = "{" <> key <> "}"
----            ty e es = tapp (tapp (tcon kind field) (untag e)) (untag es)
----         in flip (foldr (\e es -> con (ty e es) field [e, es]))
----
----simplifyExprPatterns :: (Tag t, MonadSupply Name m) => DesugaredExpr t -> m (SimplifiedExpr t)
----simplifyExprPatterns = cata $ \case
----
----    EVar    t var        -> pure (varExpr t var)
----    ECon    t con es     -> conExpr t con <$> sequence es
----    ELit    t prim       -> pure (litExpr t prim)
----    EApp    t es         -> appExpr t <$> sequence es
----    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
----    ELam    t var e      -> lamExpr t var <$> e
----    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
----    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse expandPatterns cs
----
----expandPatterns
----  :: (Tag t, MonadSupply Name m) 
----  => SimplifiedClause t (DesugaredPattern t) (m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t))))
----  -> m (SimplifiedClause t (SimplifiedPattern t) (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t))))
----expandPatterns clause = do
----    SimplifiedClause t ps es e <- sequence clause
----    qs <- concat <$> traverse splitOrs ps
----    pure (SimplifiedClause t qs es e)
----
------data SimplifiedClause t p a = SimplifiedClause t [p] [a] a
----
-------- expandPatterns
--------   :: [SimplifiedClause t (DesugaredPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (SimplifiedClause t (SimplifiedPattern t)))]
--------   -> [SimplifiedClause t (SimplifiedPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (SimplifiedClause t (SimplifiedPattern t)))]
--------expandPatterns
--------  :: [SimplifiedClause t (DesugaredPattern t) (Expr t t t t t t t t t Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t)))]
--------  -> [SimplifiedClause t (SimplifiedPattern t) (Expr t t t t t t t t t Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t)))]
------expandPatterns 
------  :: (Tag t, MonadSupply Name m) 
------  => [SimplifiedClause t (DesugaredPattern t) (m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t))))]
------  -> m [SimplifiedClause t (SimplifiedPattern t) (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (SimplifiedPattern t)))]
------expandPatterns xs = do
------    zoom <- traverse sequence xs
------    foo <- traverse bobbo zoom
------    pure (concat foo)
----
------bobbo 
------  :: (MonadSupply Name m) 
------  => SimplifiedClause t0 (DesugaredPattern t) a 
------  -> m [SimplifiedClause t0 (SimplifiedPattern t) a]
------bobbo (SimplifiedClause t ps es e) = do
------    qs <- concat <$> traverse splitOrs ps
------    pure [SimplifiedClause t qs es e]
----
------    pure [SimplifiedClause t qs es e] -- [SimplifiedClause t qs es e | qs <- traverse splitOrs ps]
----
------data Clause t p a = Clause t [p] [Guard a] 
----
------expandPatterns = concatMap $ \(SimplifiedClause t ps es e) -> do
------    undefined
------    [SimplifiedClause t qs es e | qs <- traverse splitOrs ps]
----
----splitOrs 
----  :: (MonadSupply Name m) 
----  => DesugaredPattern t 
----  -> m [SimplifiedPattern t]
----splitOrs = cata $ \case
----    PVar    t var        -> pure [varPat t var]
----    PCon    t con ps     -> do
----        zoo <- concat <$> sequence ps
----        pure [conPat t con zoo]
------    PLit    t prim       -> undefined -- pure (litPat t prim)
----    PAs     t name a     -> do -- asPat t name <$> a
----        undefined -- pure [asPat t name zoo]
------    POr     _ a b        -> a <> b
----    PAny    t            -> pure [varPat t "#_"]
----
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
----
----compilePatterns (u:us) qs c =
----    case clauseGroups qs of
----        [Variable eqs] ->
----            undefined
----
----        [Constructor eqs] -> do
----            undefined
----
----        mixed ->
----            undefined
----
----clauses :: Labeled a -> a
----clauses (Constructor eqs) = eqs
----clauses (Variable    eqs) = eqs
----
----clauseGroups
----  :: [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]
----  -> [Labeled [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]]
----clauseGroups = cata alg . fmap labeledClause where
----
----    alg Nil                                        = []
----    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
----    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
----    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
----    alg (Cons (Variable e) ts)                     = Variable [e]:ts
----
----labeledClause
----  :: Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a
----  -> Labeled (Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a)
----labeledClause eq@(Clause _ (p:_) _) = flip cata p $ \case
----
----    PCon{}    -> Constructor eq
----    PTuple{}  -> Constructor eq
----    PRecord{} -> Constructor eq
----    PList{}   -> Constructor eq
----    PVar{}    -> Variable eq
----    PAny{}    -> Variable eq
----    PLit{}    -> Variable eq
----    PAs _ _ q -> q

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--stage1
--  :: ProgExpr t 
--  -> Expr t t t t t t t t t Void Void Void Void Void Void (Binding t (ProgPattern t)) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

stage1 :: ProgExpr (TypeInfo t) -> Stage1Expr (TypeInfo t)
stage1 = cata $ \case

    -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    -- ERecord TODO

    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [prefixOp2 op, a, b]

    -- Other exprs. do not change
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    ELam    t ps e       -> lamExpr t ps e
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
    EFun    t cs         -> lamExpr t [varPat undefined "#0"] (patExpr undefined [varExpr undefined "#0"] (expandClause =<< cs))
    ELet    t bind e1 e2 -> letExpr t bind e1 e2

  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"

    prefixOp2 op = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")

    expandClause (Clause t ps gs) = [SimplifiedClause t ps es e | Guard es e <- gs]

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Stage1Expr t = Expr t t t t t t t t t Void Void Void Void Void Void (Binding t (ProgPattern t)) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

compileClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadError Error m ) 
  => Stage1Expr (TypeInfo t) 
  -> StateT [(Name, Type)] m (Stage1Expr (TypeInfo t))
compileClasses expr = 
    insertDictArgs <$> run expr <*> (nub <$> pluck)
  where
    run 
      :: ( MonadSupply Name m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
         , MonadError Error m ) 
      => Stage1Expr (TypeInfo t) 
      -> StateT [(Name, Type)] m (Stage1Expr (TypeInfo t))
    run = cata $ \case

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            letExpr t pat (insertDictArgs e1 vs) <$> expr2

        EVar t var -> 
            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)

        e -> 
            embed <$> sequence e

insertDictArgs :: Stage1Expr (TypeInfo t) -> [(Name, Type)] -> Stage1Expr (TypeInfo t)
insertDictArgs expr = 
    undefined

applyDicts 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadError Error m ) 
  => Predicate 
  -> Stage1Expr (TypeInfo t) 
  -> StateT [(Name, Type)] m (Stage1Expr (TypeInfo t))
applyDicts (InClass name ty) expr 

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        undefined

    | otherwise = do
        env <- askClassEnv
        case classMethods <$> lookupClassInstance name ty env of
            Left e -> throwError e
            Right methods -> do
                undefined

setNodePredicates :: [Predicate] -> TypeInfo t -> TypeInfo t
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: TypeInfo t -> TypeInfo t
stripNodePredicates = setNodePredicates []
