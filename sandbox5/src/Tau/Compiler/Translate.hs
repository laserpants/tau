{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Tau.Compiler.Translate where

import Control.Monad.Writer
import Control.Arrow ((<<<), (>>>), (***), (&&&), second)
import Control.Comonad.Cofree
import Control.Monad
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (nub)
import Data.List.Extra (groupSortOn)
import Data.Maybe (fromMaybe, fromJust)
import Data.Tuple.Extra
import Data.Void
import Tau.Compiler.Error
import Tau.Core
import Tau.Lang
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

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

instance Typed (Maybe Type) where
    typeOf (Just t) = t
    typeOf Nothing  = tVar (kVar "k") "a"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data Prep t = RCon t Name [Name]
    deriving (Show, Eq)

data SimplifiedClause t p a = SimplifiedClause t [p] (Guard a)
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
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (Pattern t t t t t t t t t))
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

    -- TODO TODO
--    EFix    t name e1 e2 -> desugarLet t (BLet t (varPat t name)) e1 e2

    -- Remaining values are unchanged
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
--    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3

  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"

    expandClause (Clause t ps gs) = [SimplifiedClause t ps g | g <- gs]

split :: (InfoTag t) => t -> (t, t)
split t = (updateType (const t1) t, updateType (const t2) t)
  where
    Fix (TArr t1 t2) = tagToType t

unrollLambda
  :: (Typed t, InfoTag t)
  => [ProgPattern t]
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
unrollLambda ps e = fst (foldr f (e, tag e) ps)
  where
    f p (e, t) =
        let t' = updateType (tArr (typeOf (patternTag p))) t
         --in (lamExpr t' "#0" (patExpr t [varExpr (patternTag p) "#0"] [SimplifiedClause t [p] [] e]), t')
         in (lamExpr t' "#0" (patExpr t [varExpr (patternTag p) "#0"] [SimplifiedClause t [p] (Guard [] e)]), t')

    tag = cata $ \case
        EVar t _     -> t
        ECon t _ _   -> t
        ELit t _     -> t
        EApp t _     -> t
        EFix t _ _ _ -> t
        ELam t _ _   -> t
        EIf  t _ _ _ -> t

desugarLet
  :: (Typed t, InfoTag t)
  => t
  -> ProgBinding t
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
  -> Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (SimplifiedClause t (ProgPattern t))
desugarLet t (BLet _ (Fix (PVar _ var))) e1 e2 = fixExpr t var e1 e2
desugarLet t bind e1 e2 = patExpr t [e] [SimplifiedClause t [p] (Guard [] e2)]
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
--
--clauses :: Labeled a -> a
--clauses (Constructor eqs) = eqs
--clauses (Variable    eqs) = eqs
--
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
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Stage1Expr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t)
    [ProgPattern t]
    (SimplifiedClause t (ProgPattern t))

stage1
  :: ProgExpr (TypeInfoT [Error] (Maybe Type))
  -> Stage1Expr (TypeInfoT [Error] (Maybe Type))
stage1 = cata $ \case
    -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [prefixOp2 op, a, b]
    -- Expand pattern clause guards
    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
    EFun    t cs         -> translateFunExpr t (expandClause =<< cs)
    -- Other expressions do not change, except sub-expressions
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    ELam    t ps e       -> lamExpr t ps e
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
    ELet    t bind e1 e2 -> letExpr t bind e1 e2
  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"
    prefixOp2 op       = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")

    --expandClause (Clause t ps gs) = [SimplifiedClause t ps es e | Guard es e <- gs]
    expandClause (Clause t ps gs) = [SimplifiedClause t ps g | g <- gs]

translateFunExpr
  :: TypeInfoT [Error] (Maybe Type)
  -> [SimplifiedClause (TypeInfoT [Error] (Maybe Type)) (ProgPattern (TypeInfoT [Error] (Maybe Type))) (Stage1Expr (TypeInfoT [Error] (Maybe Type)))]
  -> Stage1Expr (TypeInfoT [Error] (Maybe Type))
translateFunExpr t =
    lamExpr t [varPat t1 "#0"] <<< patExpr t2 [varExpr t1 "#0"]
  where
    t1 = TypeInfo (get cod) (nodePredicates t) []
    t2 = TypeInfo (get dom) (nodePredicates t) []

    get :: (TypeF Kind Void Type -> Type) -> Maybe Type
    get f = fmap (f . project) (nodeType t)

    cod (TArr t1 _) = t1
    dom (TArr _ t2) = t2

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- TODO
type Stage2Expr t = Stage1Expr t

stage2
  :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
  -> Stage2Expr (TypeInfoT [Error] (Maybe Type))
stage2 = undefined

compileClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Stage1Expr (TypeInfoT [e] t)
  -> StateT [(Name, Type)] m (Stage1Expr (TypeInfoT [e] t))
compileClasses expr =
    insertDictArgs <$> run expr <*> (nub <$> pluck)
  where
    run
      :: ( MonadSupply Name m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
      => Stage1Expr (TypeInfoT [e] t)
      -> StateT [(Name, Type)] m (Stage1Expr (TypeInfoT [e] t))
    run = cata $ \case

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            vs <- nub <$> pluck
            letExpr t pat (insertDictArgs e1 vs) <$> expr2

--        EFix t var expr1 expr2 -> do
--            undefined

        EVar t var ->
            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)

--        ELit t lit ->
--            undefined

        e ->
            embed <$> sequence e

insertDictArgs
  :: Stage1Expr (TypeInfoT [e] t)
  -> [(Name, Type)]
  -> Stage1Expr (TypeInfoT [e] t)
insertDictArgs expr _ =
    expr
    -- TODO
--    undefined

applyDicts
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Predicate
  -> Stage1Expr (TypeInfoT [e] t)
  -> StateT [(Name, Type)] m (Stage1Expr (TypeInfoT [e] t))
applyDicts (InClass name ty) expr

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        undefined

    | otherwise = do
        env <- askClassEnv
        case classMethods <$> lookupClassInstance name ty env of
            Left e -> undefined -- throwError e
            Right methods -> do
                undefined

setNodePredicates :: [Predicate] -> TypeInfoT [e] t -> TypeInfoT [e] t
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: TypeInfoT [e] t -> TypeInfoT [e] t
stripNodePredicates = setNodePredicates []

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Stage3Expr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void
    Name
    (SimplifiedClause t (ProgPattern t))

stage3
  :: Stage2Expr (TypeInfoT [Error] (Maybe Type))
  -> Stage3Expr (TypeInfoT [Error] (Maybe Type))
stage3 = cata $ \case
    ELam    t ps e       -> unrollLambda2 t ps e
    ELet    t bind e1 e2 -> unrollLet2 t bind e1 e2
    -- Other expressions do not change, except sub-expressions
    EPat    t es cs      -> patExpr t es cs
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3

unrollLet2
  :: t
  -> ProgBinding t
  -> Stage3Expr t
  -> Stage3Expr t
  -> Stage3Expr t
unrollLet2 t (BLet _ (Fix (PVar _ var))) e1 e2 = fixExpr t var e1 e2
unrollLet2 t bind e1 e2 = patExpr t [e] [SimplifiedClause t [p] (Guard [] e2)]
  where
    (e, p) = case bind of
        BLet _ pat   -> (e1, pat)
        BFun t f ps  -> (unrollLambda2 t ps e1, varPat t f)

unrollLambda2
  :: t
  -> [ProgPattern t]
  -> Stage3Expr t
  -> Stage3Expr t
unrollLambda2 t [Fix (PVar _ var)] e = lamExpr t var e
unrollLambda2 t [p] e = lamExpr t' "#0" (patExpr t [varExpr (patternTag p) "#0"] [SimplifiedClause t [p] (Guard [] e)])
  where
    t' = undefined

unrollLambda2 t (p:ps) e = undefined

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Stage4Expr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void
    Name
    (SimplifiedClause t (Pattern t t t t t t Void Void Void))

stage4
  :: Stage3Expr (TypeInfoT [Error] (Maybe Type))
  -> Stage4Expr (TypeInfoT [Error] (Maybe Type))
stage4 = cata $ \case
    ELam    t ps e       -> lamExpr t ps e
    EPat    t es cs      -> patExpr t es (compileClause <$> cs)
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
  where
    compileClause
      :: SimplifiedClause t (ProgPattern t) a
      -> SimplifiedClause t (Pattern t t t t t t Void Void Void) a
    compileClause (SimplifiedClause t ps g) =
        SimplifiedClause t (stage4Patterns <$> ps) g

stage4Patterns :: ProgPattern t -> Pattern t t t t t t Void Void Void
stage4Patterns = cata $ \case
    -- Translate tuples, lists, and record patterns
    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
    PList   t ps         -> foldr (listPatCons t) (conPat t "[]" []) ps
    -- Remaining patterns stay the same, except sub-patterns
    PVar    t var        -> varPat   t var
    PCon    t con ps     -> conPat   t con ps
    PLit    t prim       -> litPat   t prim
    PAs     t as p       -> asPat    t as p
    POr     t p q        -> orPat    t p q
    PAny    t            -> anyPat   t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Stage5Expr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void
    Name
    (SimplifiedClause t (Pattern t t t t t t Void Void Void))

-- remove remaining patterns

--data PatternF t1 t2 t3 t4 t5 t6 t7 t8 t9 a
--    = PVar    t1 Name                    -- ^ Variable pattern
--    | PCon    t2 Name [a]                -- ^ Constuctor pattern
--    | PAs     t3 Name a                  -- ^ As-pattern
--    | PLit    t4 Prim                    -- ^ Literal pattern
--    | POr     t5 a a                     -- ^ Or-pattern
--    | PAny    t6                         -- ^ Wildcard pattern
--    | PTuple  t7 [a]                     -- ^ Tuple pattern
--    | PList   t8 [a]                     -- ^ List pattern
----    | PRecord t9 (Row a)                 -- ^ Record pattern

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- TargetExpr
type Stage6Expr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void
    Name
    (SimplifiedClause t (Prep t))

type Stage6Pattern t =
    Pattern t t t Void Void Void Void Void Void

type Stage6PatternClause t =
    SimplifiedClause t (Pattern t t t Void Void Void Void Void Void)

type Stage6PrepClause t =
    SimplifiedClause t (Prep t)

type Info = Maybe Type -- TypeInfoT [Error] (Maybe Type)

stage6 :: (MonadSupply Name m) => Stage5Expr Info -> m (Stage6Expr Info)
stage6 = cata $ \case
    EPat t exprs clauses -> do
        cs <- traverse sequence clauses 
            >>= expandLitAndAnyPatterns 
              . expandOrPatterns 
        es <- sequence exprs
        compilePatterns es cs

    EVar    t var        -> pure (varExpr t var)
    ELit    t prim       -> pure (litExpr t prim)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3

expandLitAndAnyPatterns 
  :: (MonadSupply Name m) 
  => [SimplifiedClause Info (Pattern Info Info Info Info Info Void Void Void Void) (Stage6Expr Info)] 
  -> m [SimplifiedClause Info (Stage6Pattern Info) (Stage6Expr Info)] 
expandLitAndAnyPatterns = traverse expandClause
  where
    expandClause (SimplifiedClause t ps (Guard exs e)) = do
        (qs, exs1) <- runWriterT (traverse expandOne ps)
        pure (SimplifiedClause t qs (Guard (exs <> exs1) e))

    expandOne = cata $ \case
        PLit t prim -> do
            var <- supply
            tell [ appExpr (Just tBool)
                   [ varExpr (ty <$> t) ("@" <> literalName prim <> ".(==)")
                   , varExpr t var
                   , litExpr t prim ]]

            --let t1 = case nodeType t of
            --       Nothing -> Nothing
            --       Just ty -> Just (tArr ty (tArr ty tBool))
--            tell [ appExpr (TypeInfo (Just tBool) [] [])
--                   [ varExpr (TypeInfo t1 [] []) ("@" <> literalName prim <> ".(==)")
--                   , varExpr t var
--                   , litExpr t prim ]]

            pure (varPat t var)
          where
            ty t = t `tArr` t `tArr` tBool

        PAny t           -> varPat t <$> supply
        PVar t var       -> pure (varPat t var)
        PCon t con ps    -> conPat t con <$> sequence ps
        PAs  t as p      -> asPat t as <$> p

expandOrPatterns 
  :: [SimplifiedClause t (Pattern t t t t t t Void Void Void) (Stage6Expr t)] 
  -> [SimplifiedClause t (Pattern t t t t t Void Void Void Void) (Stage6Expr t)] 
expandOrPatterns = concatMap $ \(SimplifiedClause t ps g) ->
    [SimplifiedClause t qs g | qs <- traverse fn ps]
  where
    fn :: Pattern t t t t t t Void Void Void -> [Pattern t t t t t Void Void Void Void]
    fn = cata $ \case 
        PVar t var       -> pure (varPat t var)
        PCon t con ps    -> conPat t con <$> sequence ps
        PAs  t name a    -> asPat t name <$> a
        PLit t prim      -> pure (litPat t prim)
        PAny t           -> pure (anyPat t)
        POr  _ a b       -> a <> b

compilePatterns
  :: (MonadSupply Name m)
  => [Stage6Expr Info]
  -> [Stage6PatternClause Info (Stage6Expr Info)]
  -> m (Stage6Expr Info)
compilePatterns us qs = 
    matchAlgo us qs (varExpr (Just (tVar (kVar "FAIL") "FAIL")) "FAIL")

--    matchAlgo us qs (varExpr (TypeInfo (Just (tVar (kVar "FAIL") "FAIL")) [] []) "FAIL")

data Labeled a
    = Constructor a
    | Variable a
    deriving (Show, Eq, Ord)

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

andExpr :: Stage6Expr Info -> Stage6Expr Info -> Stage6Expr Info
andExpr a b =
    appExpr (Just tBool)
        [ varExpr (Just (tArr tBool (tArr tBool tBool))) "@(&&)"
        , a
        , b ]

--    appExpr (TypeInfo (Just tBool) [] [])
--        [ varExpr (TypeInfo (Just (tArr tBool (tArr tBool tBool))) [] []) "@(&&)"
--        , a
--        , b ]

matchAlgo
  :: (MonadSupply Name m)
  => [Stage6Expr Info]
  -> [Stage6PatternClause Info (Stage6Expr Info)]
  -> Stage6Expr Info
  -> m (Stage6Expr Info)
matchAlgo [] []                                       c = pure c
matchAlgo [] (SimplifiedClause _ [] (Guard [] e):_)   _ = pure e
matchAlgo [] (SimplifiedClause _ [] (Guard exs e):qs) c =
    ifExpr (stage6ExprTag e) (foldr1 andExpr exs) e <$> matchAlgo [] qs c
matchAlgo (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] ->
            matchAlgo us (runSubst <$> eqs) c
          where
            runSubst (SimplifiedClause t (p:ps) g) =
                let clause = SimplifiedClause t ps g
                 in case project p of
                    PVar t1 name ->
                        substitute name u <$> clause
                    PAs _ as (Fix (PVar t1 name)) ->
                        substitute name u . substitute as (varExpr t1 name) <$> clause
                    PAs _ as (Fix (PAny t)) ->
                        substitute as u <$> clause
                    -- The remaining case is for wildcard and literal patterns
                    _ -> clause

        [Constructor eqs@(SimplifiedClause t _ (Guard _ e):_)] -> do
            qs' <- traverse (toSimpleMatch2 t us c) (consGroups u eqs)
            let rs = [SimplifiedClause t [RCon (stage6ExprTag u) "$_" []] (Guard [] c) | not (isError c)]
            pure $ case qs' <> rs of
                []   -> c
                qs'' -> patExpr (stage6ExprTag e) [u] qs''
          where
            isError :: Stage6Expr t -> Bool
            isError = cata $ \case
                EVar _ var | "FAIL" == var -> True
                _                          -> False

        mixed -> do
            foldrM (matchAlgo (u:us)) c (clauses <$> mixed)

toSimpleMatch2
  :: (MonadSupply Name m)
  => Info
  -> [Stage6Expr Info]
  -> Stage6Expr Info
  -> ConsGroup Info
  -> m (Stage6PrepClause Info (Stage6Expr Info))
toSimpleMatch2 t us c ConsGroup{..} = do
    (_, vars, pats) <- patternInfo (const id) consPatterns
    expr <- matchAlgo (vars <> us) consClauses c
    pure (SimplifiedClause t [RCon consType consName pats] (Guard [] expr))

stage6ExprTag :: Stage6Expr t -> t
stage6ExprTag = cata $ \case
    EVar    t _     -> t
    ECon    t _ _   -> t
    ELit    t _     -> t
    EApp    t _     -> t
    EFix    t _ _ _ -> t
    ELam    t _ _   -> t
    EIf     t _ _ _ -> t
    EPat    t _ _   -> t

clauseGroups :: [Stage6PatternClause t a] -> [Labeled [Stage6PatternClause t a]]
clauseGroups = cata alg . fmap labeledClause where
    alg Nil                                        = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
    alg (Cons (Variable e) ts)                     = Variable [e]:ts

patternInfo
  :: (MonadSupply Name m)
  => (t -> Name -> a)
  -> [Stage6Pattern t ]
  -> m ([(Text, t)], [Stage6Expr t], [a])
patternInfo con pats = do
    vars <- supplies (length pats)
    let ts = pTag <$> pats
        make c = uncurry c <$> zip ts vars
    pure (zip vars ts, make varExpr, make con)
  where
   pTag = cata $ \case
       PVar    t _   -> t
       PCon    t _ _ -> t
       PAs     t _ _ -> t

labeledClause :: Stage6PatternClause t a -> Labeled (Stage6PatternClause t a)
labeledClause eq@(SimplifiedClause _ (p:_) _) = flip cata p $ \case
    PCon{}    -> Constructor eq
    PVar{}    -> Variable eq
    PAs _ _ q -> q

data ConsGroup t = ConsGroup
    { consName     :: Name
    , consType     :: t
    , consPatterns :: [Stage6Pattern t]
    , consClauses  :: [Stage6PatternClause t (Stage6Expr t)]
    } deriving (Show, Eq)

consGroups
  :: Stage6Expr t
  -> [Stage6PatternClause t (Stage6Expr t)]
  -> [ConsGroup t]
consGroups u cs = concatMap group_ (groupSortOn fst (info u <$> cs))
  where
    group_ all@((con, (t, ps, _)):_) = 
        [ConsGroup { consName     = con
                   , consType     = t
                   , consPatterns = ps
                   , consClauses  = thd3 . snd <$> all }]

info
  :: Stage6Expr t
  -> Stage6PatternClause t (Stage6Expr t)
  -> ( Name
     , ( t
       , [Stage6Pattern t]
       , Stage6PatternClause t (Stage6Expr t)
       )
     )
info u (SimplifiedClause t (p:qs) (Guard exs e)) =
    case project p of
        PCon _ con ps -> (con, (t, ps, SimplifiedClause t (ps <> qs) (Guard exs e)))
        PAs  _ as q   -> info u (SimplifiedClause t (q:qs) (Guard exs (substitute as u e)))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

toCore
  :: (Monad m)
  => Stage6Expr t
  -> m Core
toCore = cata $ \case
    EVar _ var       -> pure (cVar var)
    ELit _ lit       -> pure (cLit lit)
    EApp _ exs       -> sequenceExs exs
    EFix _ var e1 e2 -> cLet var <$> e1 <*> e2
    ELam _ var e1    -> cLam var <$> e1
    EIf  _ e1 e2 e3  -> cIf <$> e1 <*> e2 <*> e3
    ECon _ con exs   -> sequenceExs (pure (cVar con):exs)
--    EPat _ eqs exs   -> do
--        xxx <- sequence eqs
--        case xxx of
--            [expr] -> cPat expr <$> traverse desugarClause exs
--            _      -> error "Implementation error"
--  where
--    desugarClause (SimplifiedClause t [RCon _ con ps] [] e) = do -- (Clause [RCon _ con ps] [Guard [] e]) =
--        foo <- e
--        pure (con:ps, e)

sequenceExs :: (Monad m) => [m Core] -> m Core
sequenceExs = (fun <$>) . sequence
  where
    fun = \case
        [e] -> e
        es  -> cApp es

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

optimizeCore = undefined

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

substitute :: Name -> Stage6Expr t -> Stage6Expr t -> Stage6Expr t
substitute name subst = para $ \case

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EPat t exs eqs ->
        patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq
          :: SimplifiedClause t (Prep t) (Stage6Expr t, Stage6Expr t)
          -> SimplifiedClause t (Prep t) (Stage6Expr t)
        substEq eq@(SimplifiedClause _ ps _)
            | name `elem` (pats =<< ps) = fst <$> eq
            | otherwise                 = snd <$> eq
        pats (RCon _ _ ps) = ps

    expr -> snd <$> expr & \case
        EVar t var
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e
