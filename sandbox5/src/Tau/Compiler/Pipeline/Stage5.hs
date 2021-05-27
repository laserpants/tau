{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
module Tau.Compiler.Pipeline.Stage5 where

import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List.Extra (groupSortOn)
import Data.Tuple.Extra
import Data.Void
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Tool
import Tau.Type

type SourceExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (Pattern t t t t t t Void Void Void))

type TargetExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (SimplifiedPattern t))

type TargetPattern t =
    Pattern t t t Void Void Void Void Void Void

type TargetPatternClause t =
    SimplifiedClause t (Pattern t t t Void Void Void Void Void Void)

type TargetSimplifiedPatternClause t =
    SimplifiedClause t (SimplifiedPattern t)

data Labeled a
    = Constructor a
    | Variable a

data ConsGroup t = ConsGroup
    { consName     :: Name
    , consType     :: t
    , consPatterns :: [TargetPattern t]
    , consClauses  :: [TargetPatternClause t (TargetExpr t)] }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

deriving instance (Show a) => Show (Labeled a)
deriving instance (Eq   a) => Eq   (Labeled a)
deriving instance (Ord  a) => Ord  (Labeled a)

deriving instance (Show t) => Show (ConsGroup t)
deriving instance (Eq   t) => Eq   (ConsGroup t)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate :: (MonadSupply Name m) => SourceExpr (Maybe Type) -> m (TargetExpr (Maybe Type))
translate = cata $ \case
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

  where
    expandLitAndAnyPatterns 
      :: (MonadSupply Name m) 
      => [SimplifiedClause (Maybe Type) (Pattern (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void Void) (TargetExpr (Maybe Type))] 
      -> m [SimplifiedClause (Maybe Type) (TargetPattern (Maybe Type)) (TargetExpr (Maybe Type))] 
    expandLitAndAnyPatterns = traverse expandClause
      where
        expandClause (SimplifiedClause t ps (Guard exs e)) = do
            (qs, exs1) <- runWriterT (traverse expandPatterns ps)
            pure (SimplifiedClause t qs (Guard (exs <> exs1) e))

        expandPatterns = cata $ \case
            PLit t prim -> do
                var <- supply
                tell [ appExpr (Just tBool)
                       [ varExpr (ty <$> t) ("@" <> literalName prim <> ".(==)")
                       , varExpr t var
                       , litExpr t prim ]]
                pure (varPat t var)
              where
                ty t = t `tArr` t `tArr` tBool

            PAny t           -> varPat t <$> supply
            PVar t var       -> pure (varPat t var)
            PCon t con ps    -> conPat t con <$> sequence ps
            PAs  t as p      -> asPat t as <$> p

    expandOrPatterns 
      :: [SimplifiedClause t (Pattern t t t t t t Void Void Void) (TargetExpr t)] 
      -> [SimplifiedClause t (Pattern t t t t t Void Void Void Void) (TargetExpr t)] 
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
  => [TargetExpr (Maybe Type)]
  -> [TargetPatternClause (Maybe Type) (TargetExpr (Maybe Type))]
  -> m (TargetExpr (Maybe Type))
compilePatterns us qs = 
    compileMatch us qs (varExpr (Just (tVar (kVar "FAIL") "FAIL")) "FAIL")
  where
    compileMatch [] []                                       c = pure c
    compileMatch [] (SimplifiedClause _ [] (Guard [] e):_)   _ = pure e
    compileMatch [] (SimplifiedClause _ [] (Guard exs e):qs) c =
        ifExpr (stage6ExprTag e) (foldr1 andExpr exs) e <$> compileMatch [] qs c
    compileMatch (u:us) qs c =
        case clauseGroups qs of
            [Variable eqs] ->
                compileMatch us (runSubst <$> eqs) c
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
                        -- The remaining case is for wildcards and literal patterns
                        _ -> clause

            [Constructor eqs@(SimplifiedClause t _ (Guard _ e):_)] -> do
                qs' <- traverse (toSimpleMatch t us c) (consGroups u eqs)
                let rs = [SimplifiedClause t [SCon (stage6ExprTag u) "$_" []] (Guard [] c) | not (isError c)]
                pure $ case qs' <> rs of
                    []   -> c
                    qs'' -> patExpr (stage6ExprTag e) [u] qs''
              where
                isError :: TargetExpr t -> Bool
                isError = cata $ \case
                    EVar _ var | "FAIL" == var -> True
                    _                          -> False

            mixed -> do
                foldrM (compileMatch (u:us)) c (clauses <$> mixed)

    clauses :: Labeled a -> a
    clauses (Constructor eqs) = eqs
    clauses (Variable    eqs) = eqs

    andExpr :: TargetExpr (Maybe Type) -> TargetExpr (Maybe Type) -> TargetExpr (Maybe Type)
    andExpr a b =
        appExpr (Just tBool)
            [ varExpr (Just (tArr tBool (tArr tBool tBool))) "@(&&)"
            , a
            , b ]

    toSimpleMatch
      :: (MonadSupply Name m)
      => Maybe Type
      -> [TargetExpr (Maybe Type)]
      -> TargetExpr (Maybe Type)
      -> ConsGroup (Maybe Type)
      -> m (TargetSimplifiedPatternClause (Maybe Type) (TargetExpr (Maybe Type)))
    toSimpleMatch t us c ConsGroup{..} = do
        (_, vars, pats) <- patternInfo (const id) consPatterns
        expr <- compileMatch (vars <> us) consClauses c
        pure (SimplifiedClause t [SCon consType consName pats] (Guard [] expr))

    stage6ExprTag :: TargetExpr t -> t
    stage6ExprTag = cata $ \case
        EVar    t _     -> t
        ECon    t _ _   -> t
        ELit    t _     -> t
        EApp    t _     -> t
        EFix    t _ _ _ -> t
        ELam    t _ _   -> t
        EIf     t _ _ _ -> t
        EPat    t _ _   -> t

    clauseGroups :: [TargetPatternClause t a] -> [Labeled [TargetPatternClause t a]]
    clauseGroups = cata alg . fmap labeledClause where
        alg Nil                                        = []
        alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
        alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
        alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
        alg (Cons (Variable e) ts)                     = Variable [e]:ts

    patternInfo
      :: (MonadSupply Name m)
      => (t -> Name -> a)
      -> [TargetPattern t ]
      -> m ([(Text, t)], [TargetExpr t], [a])
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

    labeledClause :: TargetPatternClause t a -> Labeled (TargetPatternClause t a)
    labeledClause eq@(SimplifiedClause _ (p:_) _) = flip cata p $ \case
        PCon{}    -> Constructor eq
        PVar{}    -> Variable eq
        PAs _ _ q -> q

    consGroups
      :: TargetExpr t
      -> [TargetPatternClause t (TargetExpr t)]
      -> [ConsGroup t]
    consGroups u cs = concatMap group_ (groupSortOn fst (info u <$> cs))
      where
        group_ all@((con, (t, ps, _)):_) = 
            [ConsGroup { consName     = con
                       , consType     = t
                       , consPatterns = ps
                       , consClauses  = thd3 . snd <$> all }]

    info
      :: TargetExpr t
      -> TargetPatternClause t (TargetExpr t)
      -> (Name, (t, [TargetPattern t], TargetPatternClause t (TargetExpr t)))
    info u (SimplifiedClause t (p:qs) (Guard exs e)) =
        case project p of
            PCon _ con ps -> (con, (t, ps, SimplifiedClause t (ps <> qs) (Guard exs e)))
            PAs  _ as q   -> info u (SimplifiedClause t (q:qs) (Guard exs (substitute as u e)))

substitute :: Name -> TargetExpr t -> TargetExpr t -> TargetExpr t
substitute name subst = para $ \case
    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EPat t exs eqs ->
        patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq
          :: TargetSimplifiedPatternClause t (TargetExpr t, TargetExpr t)
          -> TargetSimplifiedPatternClause t (TargetExpr t)
        substEq eq@(SimplifiedClause _ ps _)
            | name `elem` (pats =<< ps) = fst <$> eq
            | otherwise                 = snd <$> eq
        pats (SCon _ _ ps) = ps

    expr -> snd <$> expr & \case
        EVar t var
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e
