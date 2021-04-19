{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Compiler.Translation where

import Control.Monad.Supply
import Data.Maybe (fromMaybe)
import Data.Void
import Tau.Lang
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

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

class (Show t, Eq t) => TypeTag t where
    tvar     :: Name -> t
    tarr     :: t -> t -> t
    tapp     :: t -> t -> t
    fromType :: Type -> t

instance TypeTag () where
    tvar _     = ()
    tarr _ _   = ()
    tapp _ _   = ()
    fromType _ = ()

instance TypeTag Type where
    tvar  = tVar kTyp
    tarr  = tArr
    tapp  = tApp
    fromType = id

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type DesugaredPattern t = Pattern t t t t t t Void Void Void

type DesugaredExpr a s t = Expr t t t t t t t t Void Void Void Void Void Void Void a s (ClauseA t (DesugaredPattern t))

-- type SimplifiedPattern t = Pattern t t t Void Void Void Void Void Void
type SimplifiedPattern t = Pattern t t t t Void Void Void Void Void

desugarExpr
  :: (TypeTag t)
  => Expr t t t t t t t t t t t t t t t (Binding t (ProgPattern t)) [ProgPattern t] (Clause t (ProgPattern t))
  -> DesugaredExpr Void Name t
desugarExpr = desugarExprPatterns . cata (\case

    -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listConsExpr t) (conExpr t "[]" []) exprs
    ERecord t row        -> desugarRow conExpr row 
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr  t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr  t [varExpr (op2Tag op) ("(" <> op2Symbol op <> ")"), a, b]
    -- Expand pattern clause guards
    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
    EFun    t cs         -> funExpr t (expandClause =<< cs)
    -- Unroll lambdas
    ELam    t ps e       -> foldr (\p e1 -> unrollLambda undefined p e1) e ps
    -- Translate let expressions
    ELet    t bind e1 e2 -> desugarLet t bind e1 e2

    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3)
  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"

    expandClause (Clause t ps gs) = [ClauseA t ps es e | Guard es e <- gs]

    desugarLet t bind e1 e2 = patExpr t [e3] [ClauseA t [p3] [] e2]
      where 
        (e3, p3) = case bind of
            BLet _ pat   -> (e1, pat)
            BFun t f ps  -> (foldr (\p e -> unrollLambda undefined p e) e1 ps, varPat t f)

    unrollLambda t p e = 
        lamExpr t "$!" (patExpr undefined [varExpr undefined "$!"] [ClauseA undefined [] [] e])

--    ELam    t ps e       -> foldr (\p e1 -> lamExpr (tarr (patternTag p) (eTag e1)) p e1) e ps

--            BFun t1 f ps -> (foldr (\p e -> lamExpr (tarr (patternTag p) (eTag e)) p e) e1 ps, varPat t1 f)

--    eTag = cata $ \case
--        EVar    t _      -> t
--        ECon    t _ _    -> t
--        ELit    t _      -> t
--        EApp    t _      -> t
--        EFix    t _ _ _  -> t
----        ELam    t _ _    -> t
--        EIf     t _ _ _  -> t
----        EPat    t _ _    -> t

desugarExprPatterns
  :: (TypeTag t) 
  => Expr t t t t t t t t t Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))
  -> DesugaredExpr Void Name t
desugarExprPatterns = cata $ \case

    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
    EPat    t es cs      -> patExpr t es (translClause <$> cs)
  where
    translClause (ClauseA t ps es e) = ClauseA t (desugarPatterns <$> ps) es e

--    ELet    t bind e1 e2 -> letExpr t (translBinding bind) e1 e2
--    ELam    t p e        -> lamExpr t (desugarPatterns p) e

--    translBinding (BLet t p)    = BLet t (desugarPatterns p)
--    translBinding (BFun t f ps) = BFun t f (desugarPatterns <$> ps)

desugarPatterns :: (TypeTag t) => ProgPattern t -> DesugaredPattern t 
desugarPatterns = cata $ \case

    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
    PList   t ps         -> foldr (listConsPat t) (conPat t "[]" []) ps
    PRecord t row        -> desugarRow conPat row 

    PVar    t var        -> varPat t var
    PCon    t con ps     -> conPat t con ps
    PLit    t prim       -> litPat t prim
    PAs     t as p       -> asPat  t as p
    POr     t p q        -> orPat  t p q
    PAny    t            -> anyPat t

desugarRow :: (TypeTag t) => (t -> Name -> [a] -> a) -> Row a -> a
desugarRow con (Row map r) = Map.foldrWithKey fun (initl r) map
  where
    initl = fromMaybe (con (fromType (tCon kRow "{}")) "{}" []) 
    fun key = 
        let kind  = kArr kTyp (kArr kRow kRow)
            field = "{" <> key <> "}"
         in flip (foldr (\e es -> con (fromType (tCon kind field)) field [e, es]))

--translateLetExprs 
--  :: (TypeTag t, MonadSupply Name m) 
----  => DesugaredExpr (Binding t (Pattern t t t t t t () () ())) t
--  => DesugaredExpr (Binding t (Pattern t t t t t t Void Void Void)) t
--  -> m (DesugaredExpr Void t)
--translateLetExprs = cata $ \case
--
--    EVar    t var        -> pure $ varExpr t var
--    ECon    t con es     -> conExpr t con <$> sequence es
--    ELit    t prim       -> pure $ litExpr t prim
--    EApp    t es         -> appExpr t <$> sequence es
--    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
--    ELam    t p e        -> lamExpr t p <$> e
--    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
--    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse sequence cs
--
--    -- Unroll lets expressions
--
--    ELet t (BLet _ pat) expr1 expr2 -> do
--        e1 <- expr1
--        e2 <- expr2
--        pure (patExpr t [e1] [ClauseA t [pat] [] e2])
--
--    -- let f (Some x) (Some y) = z in e
--    --
--    -- let f = \(Some x) => \(Some y) => z in e
--
--    ELet t (BFun _ f ps) expr1 expr2 -> do
--        --vars <- supplies (length ps)
--        e1 <- expr1
--        e2 <- expr2
--        let zzz = foldr (\p e -> lamExpr (tarr (pTag p) (eTag e)) p e) e1 ps
--        pure (patExpr t [e1] [ClauseA t [varPat undefined f] [] e2])
--        --let zzz = foldr undefined undefined ps
--        
--        --pure (lamExpr undefined undefined undefined)
--
----        foldrM (\x y -> do
----                v <- supply
----                undefined
----            ) e1 ps
----
----        undefined
--        --let t1 = foldr tarr (eTag e1) (pTag <$> ps)
--        --undefined
--        --pure (patExpr t [lamExpr t1 ps e1] [ClauseA t [varPat t1 f] [] e2])
--
----    ELam    t ps e       -> foldr (\p e1 -> lamExpr (tarr (patternTag p) (eTag e1)) p e1) e ps
--
--  where
--    eTag = cata $ \case
--        EVar    t _      -> t
------        ECon    t _ _    -> t
------        ELit    t _      -> t
------        EApp    t _      -> t
------        EFix    t _ _ _  -> t
--------        ELam    t _ _    -> t
------        EIf     t _ _ _  -> t
------        EPat    t _ _    -> t
--
--    pTag = cata $ \case
--        PVar    t _      -> t
----        PCon    t _ _    -> t
----        PLit    t _      -> t
----        PAs     t _ _    -> t
----        POr     t _ _    -> t
----        PAny    t        -> t

-- \(Some x) => y
--
-- \z => match z with
--         | Some x => y

--yyy 
--  :: DesugaredExpr Void t 
----  -> Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (ClauseA t (SimplifiedPattern t))
--  -> Expr t t t t Void t Void t t Void Void Void Void Void Void Void Void (ClauseA t (SimplifiedPattern t))
--yyy = cata $ \case 
--    EVar    t var        -> varExpr t var
--    ECon    t con es     -> conExpr t con es
--    ELit    t prim       -> litExpr t prim
--    EApp    t es         -> appExpr t es
--    EFix    t name e1 e2 -> fixExpr t name e1 e2
------    ELam    t ps e       -> lamExpr t (splitOrs =<< ps) e
----
--    ELam    t (Fix (PVar _ var)) e    -> undefined
--    ELam    t p e                     -> undefined -- lamExpr t (undefined p) e
----
--    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
--    EPat    t es cs      -> patExpr t es (expandPatterns cs)

-- expandPatterns 
--   :: [ClauseA t (DesugaredPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (ClauseA t (SimplifiedPattern t)))]
--   -> [ClauseA t (SimplifiedPattern t) (Expr t t t t t t t t t t () () () () () (SimplifiedPattern t) [SimplifiedPattern t] (ClauseA t (SimplifiedPattern t)))]
expandPatterns 
  :: [ClauseA t (DesugaredPattern t) (Expr t t t t Void t Void t t Void Void Void Void Void Void Void Void (ClauseA t (SimplifiedPattern t)))]
  -> [ClauseA t (SimplifiedPattern t) (Expr t t t t Void t Void t t Void Void Void Void Void Void Void Void (ClauseA t (SimplifiedPattern t)))]
expandPatterns = concatMap $ \(ClauseA t ps es e) ->
    [ClauseA t qs es e | qs <- traverse splitOrs ps]

splitOrs :: DesugaredPattern t -> [SimplifiedPattern t]
splitOrs = cata $ \case
    PVar    t var        -> pure (varPat t var)
    PCon    t con ps     -> conPat t con <$> sequence ps
    PLit    t prim       -> pure (litPat t prim)
    PAs     t name a     -> asPat t name <$> a
    POr     _ a b        -> a <> b
    PAny    t            -> pure (varPat t "$*")

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

compilePatterns (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] ->
            undefined

        [Constructor eqs] -> do
            undefined

        mixed -> 
            undefined

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

clauseGroups 
  :: [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a] 
  -> [Labeled [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]]
clauseGroups = cata alg . fmap labeledClause where

    alg Nil                                        = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
    alg (Cons (Variable e) ts)                     = Variable [e]:ts

labeledClause 
  :: Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a 
  -> Labeled (Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a)
labeledClause eq@(Clause _ (p:_) _) = flip cata p $ \case

    PCon{}    -> Constructor eq
    PTuple{}  -> Constructor eq
    PRecord{} -> Constructor eq
    PList{}   -> Constructor eq
    PVar{}    -> Variable eq
    PAny{}    -> Variable eq
    PLit{}    -> Variable eq
    PAs _ _ q -> q
