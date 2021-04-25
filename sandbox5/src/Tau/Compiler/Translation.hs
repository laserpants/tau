{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Tau.Compiler.Translation where

import Control.Arrow ((<<<), (>>>), (***), second)
import Control.Monad
import Control.Monad.Supply
import Data.Maybe (fromMaybe)
import Data.Void
import Tau.Compiler.Error
import Tau.Lang
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map

data ClauseA t p a = ClauseA t [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''ClauseA
deriveEq1   ''ClauseA
deriveOrd1  ''ClauseA

data Prep t = RCon t Name [Name]
    deriving (Show, Eq)

data Labeled a
    = Constructor a
    | Variable a
    deriving (Show, Eq, Ord)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type DesugaredPattern t = Pattern t t t t t t Void Void Void
type DesugaredExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (DesugaredPattern t))

type SimplifiedPattern t = Pattern t t t Void Void Void Void Void Void
type SimplifiedExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t))

--abc :: ProgExpr (TypeInfo e) -> ProgExpr (TypeInfoT e (Maybe Type))
--abc expr = e where Ast e = Just <$$> Ast expr

simplifyExpr :: ProgExpr (Maybe (TypeInfo [e])) -> SimplifiedExpr (Maybe (TypeInfo [e]))
simplifyExpr = cata $ \case

 -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listConsExpr t) (conExpr t "[]" []) exprs
    ERecord t row        -> conExpr t "#Record" [desugarRow row]
 -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
 -- Expand pattern clause guards
    EPat    t es cs      -> undefined
    EFun    t cs         -> undefined
 -- Unroll lambdas
    ELam    t ps e       -> undefined
 -- Translate let expressions
    ELet    t bind e1 e2 -> undefined
 -- Remaining values are unchanged
    EVar    t var        -> varExpr t var
    ECon    t con es     -> undefined
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> undefined
    EFix    t name e1 e2 -> undefined
    EIf     t e1 e2 e3   -> undefined

  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"

desugarRow
  :: Row (SimplifiedExpr (Maybe (TypeInfo [e])))
  -> SimplifiedExpr (Maybe (TypeInfo [e]))
desugarRow (Row map r) =
    Map.foldrWithKey fun (fromMaybe (conExpr (Just (TypeInfo (tCon kRow "{}") [] [])) "{}" []) r) map
  where
    fun key = flip (foldr f)
      where
        f d e = conExpr (getTypeInfo (tag d) e) field [d, e]

        field = "{" <> key <> "}"
        kind  = kArr kTyp (kArr kRow kRow)
        tapp t ti = ti{ nodeType = tApp (tApp (tCon kind field) t) (nodeType ti) }

        getTypeInfo :: Maybe Type -> SimplifiedExpr (Maybe (TypeInfo [e])) -> Maybe (TypeInfo [e])
        getTypeInfo s = cata $ \case
            EVar t _     -> tapp <$> s <*> t
            ECon t _ _   -> tapp <$> s <*> t

        tag = cata $ \case
            EVar t _     -> typeOf <$> t
            ECon t _ _   -> typeOf <$> t
            ELit t _     -> typeOf <$> t
            EApp t _     -> typeOf <$> t
            EFix t _ _ _ -> typeOf <$> t
            ELam t _ _   -> typeOf <$> t
            EIf  t _ _ _ -> typeOf <$> t
            EPat t _ _   -> typeOf <$> t

--        f d (xx@(Fix (EVar ti v))) = conExpr (zapp2 xx) field [d, xx]
--        f d (Fix (ECon (Just ti) con e)) = 
--            let t = Just (ti{ nodeType = tapp (nodeType ti) }) 
--             in conExpr t field [d, conExpr (Just ti) con e]
--        f d e = conExpr Nothing field [d, e]
--        run d (Just ti, e) = let t = Just (ti{ nodeType = tapp (nodeType ti) }) 
--                              in (t, conExpr t field [d, e]) 

--desugarRow2
--  :: Row (SimplifiedExpr (TypeInfo [e])) 
--  -> SimplifiedExpr (TypeInfo [e])
--desugarRow2 (Row map r) = snd (Map.foldrWithKey fun (eTag initv, initv) map)
--  where
--    initv = 
--        case r of
--            Nothing -> varExpr (TypeInfo (tCon kRow "{}") [] []) "{}" -- ( tCon kRow "{}", varExpr (TypeInfo (tCon kRow "{}") [] []) "{}" )
--            Just v  -> v -- ( typeOf (eTag v), v )
--
--    fun key = flip (foldr run)
--      where
--        field = "{" <> key <> "}"
--
--        run a (t, b) = ( tApp (tCon (kArr kTyp (kArr kRow kRow)) field) t, conExpr (TypeInfo t [] []) field [a, b] )
--
--    eTag = cata $ \case
--        EVar    t _      -> typeOf t
--        ECon    t _ _    -> typeOf t
--        ELit    t _      -> typeOf t
--        EApp    t _      -> typeOf t
--        EFix    t _ _ _  -> typeOf t
--        ELam    t _ _    -> typeOf t
--        EIf     t _ _ _  -> typeOf t
--        EPat    t _ _    -> typeOf t

--desugarRow 
--  :: Row (SimplifiedExpr (Maybe (TypeInfo [e]))) 
--  -> SimplifiedExpr (Maybe (TypeInfo [e]))
--desugarRow (Row map r) = snd (Map.foldrWithKey fun initv map)
--  where
--    initv = 
--        case r of
--            Nothing -> (tCon kRow "{}", varExpr (Just (TypeInfo (tCon kRow "{}") [] [])) "{}")
--
--    fun key a (t, z) = foldr run (t, z) a
--      where
--        field = "{" <> key <> "}"
--
--        run a (t, b) = ( tApp (tCon (kArr kTyp (kArr kRow kRow)) field) t, conExpr (Just (TypeInfo t [] [])) field [a, b])


--    initl = conExpr (Just (TypeInfo (ttCon kRow "{}") [] [])) "{}" []
--    fun key =
--        let kind  = kArr kTyp (kArr kRow kRow)
--            field = "{" <> key <> "}"
--            --ty e es = tApp (tApp (tCon kind field) undefined) undefined
--            ti2 = TypeInfo { nodeType       = tInt
--                           , nodePredicates = []
--                           , nodeErrors     = [] }
--         in
--            --flip (foldr (\e es -> undefined (ty e es) field [e, es]))
--            flip (foldr (\e es -> 
--                    let xxx = eTag e -- :: SimplifiedExpr (Maybe (TypeInfo [e2]))
--                     in conExpr (Just ti2) field [e, es]))
----              where
----                foo e es = case (undefined e, undefined es) of
----                    (Just xx, Just yy) -> undefined
--    eTag = cata $ \case
--        EVar    t _          -> t

--  where
--    initl = fromMaybe (con (tcon kRow "{}") "{}" [])
--    fun key =
--        let kind  = kArr kTyp (kArr kRow kRow)
--            field = "{" <> key <> "}"
--            ty e es = tapp (tapp (tcon kind field) (untag e)) (untag es)
--         in flip (foldr (\e es -> con (ty e es) field [e, es]))


--simplifyExpr :: (Tag t, MonadSupply Name m) => ProgExpr t -> m (SimplifiedExpr t)
--simplifyExpr = simplifyExprPatterns <=< desugarExprPatterns <<< cata (\case
-- -- Translate tuples, lists, and records
--    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
--    EList   t exprs      -> foldr (listConsExpr t) (conExpr t "[]" []) exprs
--    ERecord t row        -> conExpr (rowTag (eTag <$> row)) "#Record" [desugarRow eTag conExpr row]
-- -- Translate operators to prefix form
--    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
--    EOp2    t op a b     -> appExpr t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
-- -- Expand pattern clause guards
--    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
--    EFun    t cs         -> funExpr t (expandClause =<< cs)
-- -- Unroll lambdas
--    ELam    t ps e       -> fst $ foldr unrollLambda (e, t) ps
-- -- Translate let expressions
--    ELet    t bind e1 e2 -> desugarLet t bind e1 e2
-- -- Remaining values are unchanged
--    EVar    t var        -> varExpr t var
--    ECon    t con es     -> conExpr t con es
--    ELit    t prim       -> litExpr t prim
--    EApp    t es         -> appExpr t es
--    EFix    t name e1 e2 -> fixExpr t name e1 e2
--    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3)
--  where
--    prefixOp1 (ONeg t) = varExpr t "negate"
--    prefixOp1 (ONot t) = varExpr t "not"
--
--    expandClause (Clause t ps gs) = [ClauseA t ps es e | Guard es e <- gs]
--
--    desugarLet t bind e1 e2 = patExpr t [e] [ClauseA t [p] [] e2]
--      where
--        (e, p) = case bind of
--            BLet _ pat   -> (e1, pat)
--            BFun t f ps  -> (fst $ foldr unrollLambda (e1, t) ps, varPat t f)
--
--    -- TODO
--    unrollLambda p (e, t) = (traceShow t $ funExpr t [ClauseA t [p] [] e], t)
--
----        lamExpr undefined "$!" (patExpr undefined [varExpr undefined "$!"] [ClauseA undefined [] [] e])
--
--
----    ELam    t ps e       -> foldr (\p e1 -> lamExpr (tarr (patternTag p) (eTag e1)) p e1) e ps
--
----            BFun t1 f ps -> (foldr (\p e -> lamExpr (tarr (patternTag p) (eTag e)) p e) e1 ps, varPat t1 f)
--
--    eTag = cata $ \case
--        EVar    t _      -> t
--        ECon    t _ _    -> t
--        ELit    t _      -> t
--        EApp    t _      -> t
--        EFix    t _ _ _  -> t
----        ELam    t _ _    -> t
--        EIf     t _ _ _  -> t
----        EPat    t _ _    -> t
--
----removeFunExprs 
----  :: (Tag t, MonadSupply Name m)
----  => Expr t t t t t t t t t Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
----  -> m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)))
----removeFunExprs = cata $ \case
----
----    EVar    t var        -> pure (varExpr t var)
----    ECon    t con es     -> conExpr t con <$> sequence es
------    ELit    t prim       -> pure (litExpr t prim)
------    EApp    t es         -> appExpr t <$> sequence es
------    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
------    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
------    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse translClause cs
------    ELam    t p e        -> lamExpr t p <$> e
----
----    EFun    t cs         -> undefined
--
----  => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
--
--desugarExprPatterns
--  :: (Tag t, MonadSupply Name m)
--  => Expr t t t t t t t t t Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
--  -> m (DesugaredExpr t)
--desugarExprPatterns = cata $ \case
--
--    EVar    t var        -> pure (varExpr t var)
--    ECon    t con es     -> conExpr t con <$> sequence es
--    ELit    t prim       -> pure (litExpr t prim)
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
--    ELam    t p e        -> lamExpr t p <$> e
--
--    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse translClause cs
--    EFun    t clauses    -> do
--        cs <- traverse translClause clauses
--        let tags = clausePatterns (head cs)
--            vars = (`varExpr` "#0") <$> tags
--
--        pure (foldr (\p e -> lamExpr (eTag e) "#0" e) (patExpr t vars cs) tags)
--
----        let tags = gork cs
----        let vars = (`varExpr` "#0") <$> tags
----        pure (foldr (\p e -> lamExpr (tarr p (eTag e)) "#0" e) (patExpr t vars cs) tags)
--  where
--    translClause (ClauseA t ps es e) =
--        ClauseA t (desugarPatterns <$> ps) <$> sequence es <*> e
--
--    clausePatterns (ClauseA _ ps _ _) = pTag <$> ps
--
--    eTag = cata $ \case
--        EVar    t _          -> t
--        ECon    t _ _        -> t
--        ELit    t _          -> t
--        EApp    t _          -> t
--        EFix    t _ _ _      -> t
--        EIf     t _ _ _      -> t
--        ELam    t _ _        -> t
--        EPat    t _ _        -> t
--
--    pTag = cata $ \case
--        PVar    t _          -> t
--        PCon    t _ _        -> t
--        PLit    t _          -> t
--        PAs     t _ _        -> t
--        POr     t _ _        -> t
--        PAny    t            -> t
--
--rowTag :: (Tag t) => Row t -> t
--rowTag row = tapp (fromType tRecordCon) (rowToTag row)
--
--desugarPatterns :: (Tag t) => ProgPattern t -> DesugaredPattern t
--desugarPatterns = cata $ \case
--
--    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
--    PList   t ps         -> foldr (listConsPat t) (conPat t "[]" []) ps
--    PRecord t row        -> conPat (rowTag (pTag <$> row)) "#Record" [desugarRow pTag conPat row]
--
--    PVar    t var        -> varPat t var
--    PCon    t con ps     -> conPat t con ps
--    PLit    t prim       -> litPat t prim
--    PAs     t as p       -> asPat  t as p
--    POr     t p q        -> orPat  t p q
--    PAny    t            -> anyPat t
--  where
--    pTag = cata $ \case
--        PVar    t _          -> t
--        PCon    t _ _        -> t
--        PLit    t _          -> t
--        PAs     t _ _        -> t
--        POr     t _ _        -> t
--        PAny    t            -> t
--
--desugarRow :: (Tag t) => (a -> t) -> (t -> Name -> [a] -> a) -> Row a -> a
--desugarRow untag con (Row map r) = Map.foldrWithKey fun (initl r) map
--  where
--    initl = fromMaybe (con (tcon kRow "{}") "{}" [])
--    fun key =
--        let kind  = kArr kTyp (kArr kRow kRow)
--            field = "{" <> key <> "}"
--            ty e es = tapp (tapp (tcon kind field) (untag e)) (untag es)
--         in flip (foldr (\e es -> con (ty e es) field [e, es]))
--
--simplifyExprPatterns :: (Tag t, MonadSupply Name m) => DesugaredExpr t -> m (SimplifiedExpr t)
--simplifyExprPatterns = cata $ \case
--
--    EVar    t var        -> pure (varExpr t var)
--    ECon    t con es     -> conExpr t con <$> sequence es
--    ELit    t prim       -> pure (litExpr t prim)
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    ELam    t var e      -> lamExpr t var <$> e
--    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
--    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse expandPatterns cs
--
--expandPatterns
--  :: (Tag t, MonadSupply Name m) 
--  => ClauseA t (DesugaredPattern t) (m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t))))
--  -> m (ClauseA t (SimplifiedPattern t) (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t))))
--expandPatterns clause = do
--    ClauseA t ps es e <- sequence clause
--    qs <- concat <$> traverse splitOrs ps
--    pure (ClauseA t qs es e)
--
----data ClauseA t p a = ClauseA t [p] [a] a
--
------ expandPatterns
------   :: [ClauseA t (DesugaredPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (ClauseA t (SimplifiedPattern t)))]
------   -> [ClauseA t (SimplifiedPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (ClauseA t (SimplifiedPattern t)))]
------expandPatterns
------  :: [ClauseA t (DesugaredPattern t) (Expr t t t t t t t t t Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t)))]
------  -> [ClauseA t (SimplifiedPattern t) (Expr t t t t t t t t t Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t)))]
----expandPatterns 
----  :: (Tag t, MonadSupply Name m) 
----  => [ClauseA t (DesugaredPattern t) (m (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t))))]
----  -> m [ClauseA t (SimplifiedPattern t) (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (SimplifiedPattern t)))]
----expandPatterns xs = do
----    zoom <- traverse sequence xs
----    foo <- traverse bobbo zoom
----    pure (concat foo)
--
----bobbo 
----  :: (MonadSupply Name m) 
----  => ClauseA t0 (DesugaredPattern t) a 
----  -> m [ClauseA t0 (SimplifiedPattern t) a]
----bobbo (ClauseA t ps es e) = do
----    qs <- concat <$> traverse splitOrs ps
----    pure [ClauseA t qs es e]
--
----    pure [ClauseA t qs es e] -- [ClauseA t qs es e | qs <- traverse splitOrs ps]
--
----data Clause t p a = Clause t [p] [Guard a] 
--
----expandPatterns = concatMap $ \(ClauseA t ps es e) -> do
----    undefined
----    [ClauseA t qs es e | qs <- traverse splitOrs ps]
--
--splitOrs 
--  :: (MonadSupply Name m) 
--  => DesugaredPattern t 
--  -> m [SimplifiedPattern t]
--splitOrs = cata $ \case
--    PVar    t var        -> pure [varPat t var]
--    PCon    t con ps     -> do
--        zoo <- concat <$> sequence ps
--        pure [conPat t con zoo]
----    PLit    t prim       -> undefined -- pure (litPat t prim)
--    PAs     t name a     -> do -- asPat t name <$> a
--        undefined -- pure [asPat t name zoo]
----    POr     _ a b        -> a <> b
--    PAny    t            -> pure [varPat t "#_"]
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--compilePatterns (u:us) qs c =
--    case clauseGroups qs of
--        [Variable eqs] ->
--            undefined
--
--        [Constructor eqs] -> do
--            undefined
--
--        mixed ->
--            undefined
--
--clauses :: Labeled a -> a
--clauses (Constructor eqs) = eqs
--clauses (Variable    eqs) = eqs
--
--clauseGroups
--  :: [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]
--  -> [Labeled [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]]
--clauseGroups = cata alg . fmap labeledClause where
--
--    alg Nil                                        = []
--    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
--    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
--    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
--    alg (Cons (Variable e) ts)                     = Variable [e]:ts
--
--labeledClause
--  :: Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a
--  -> Labeled (Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a)
--labeledClause eq@(Clause _ (p:_) _) = flip cata p $ \case
--
--    PCon{}    -> Constructor eq
--    PTuple{}  -> Constructor eq
--    PRecord{} -> Constructor eq
--    PList{}   -> Constructor eq
--    PVar{}    -> Variable eq
--    PAny{}    -> Variable eq
--    PLit{}    -> Variable eq
--    PAs _ _ q -> q
