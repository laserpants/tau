{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE StrictData       #-}
module Tau.Expr.Patterns where

import Control.Arrow
import Control.Monad
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Maybe (fromJust)
import Data.Function ((&))
import Data.List.Extra (groupSortOn)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (fst3, thd3)
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Util

simplify :: (Eq t, MonadSupply Name m) => RepExpr t -> m (SimpleExpr t)
simplify = cata alg where
    alg = \case 
        EVar t var -> pure (tagVar t var)
        ELit t lit -> pure (tagLit t lit)
        EApp t exs -> tagApp t <$> sequence exs
        --
        --  Expressions like  : let Just x = y in f x
        --  get translated to : match y with | Just x => f x
        --
        ELet _ rep e1 e2 -> do
            exp <- e1
            ret <- e2
            compileMatch [exp] [Equation [rep] [] ret] eErr
        --
        --  Lambda expressions like : \Just x => f x
        --  get translated to       : \z => match z with | Just x => f x in z
        --  where z is a fresh variable
        --
        ELam t rep ex -> do
            fresh <- supply
            ret <- ex
            ex1 <- compileMatch [tagVar t fresh] [Equation [rep] [] ret] eErr
            pure (tagLam t (sVar t fresh) ex1)

        EMatch _ exs eqs -> 
            join (compileMatch <$> sequence exs 
                               <*> traverse sequenceEqExprs eqs 
                               <*> pure eErr)

    sequenceEqExprs
      :: (Eq t, MonadSupply Name m) 
      => Equation (Rep t) (m (SimpleExpr t)) 
      -> m (SimpleEq t)
    sequenceEqExprs (Equation ps exs e) = 
        Equation ps <$> sequence exs <*> e

compileMatch
  :: (Eq t, MonadSupply Name m)
  => [SimpleExpr t]
  -> [SimpleEq t]
  -> SimpleExpr t
  -> m (SimpleExpr t)
compileMatch [] [] d = pure d
compileMatch [] qs d = case qs of
    (Equation [] [] e:_)  -> pure e
    (Equation [] cs e:qs) -> tagIf (getTag e) (foldr1 eAnd cs) e <$> compileMatch [] qs d
compileMatch (u:us) qs d = 
    foldrM run d (equationGroups qs)
  where
    run (ConHead, eqs) def = do
        eqs' <- traverse fn (conGroups eqs)
        case eqs' <> [Equation [sVar (getTag u) "$_"] [] def | eErr /= def] of
            []                      -> pure def
            clss@(Equation _ _ e:_) -> pure (tagMatch (getTag e) [u] clss)
      where
        fn (name, rs, t, eqs') = do
            vars <- traverse (\r -> tagVar (getRepTag r) <$> supply) rs
            expr <- compileMatch (vars <> us) eqs' def
            pure (Equation [sCon t name (varName <$> vars)] [] expr)

    run (VarHead, eqs) def = 
        compileMatch us (fn <$> eqs) def
      where
        fn (Equation (Fix (RVar _ name):rs) c e) =
            substitute name u <$> Equation rs c e 
        fn eq = eq

    varName (Fix (EVar _ name)) = name

substitute :: Name -> SimpleExpr t -> SimpleExpr t -> SimpleExpr t
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> tagLet t pat e1 e2'
      where 
        e2' | name `elem` free pat = fst e2
            | otherwise            = snd e2

    ELam t pat expr -> tagLam t pat expr'
      where
        expr' | name `elem` free pat = fst expr
              | otherwise            = snd expr

    EMatch t exs eqs ->
        tagMatch t (snd <$> exs) (substEq <$> eqs)

    expr -> snd <$> expr & \case
        EVar t var -> tagVar t var
        ELit t lit -> tagLit t lit
        EApp t exs -> tagApp t exs

  where
    substEq 
      :: Equation (SimpleRep t) (SimpleExpr t, SimpleExpr t) 
      -> Equation (SimpleRep t) (SimpleExpr t)
    substEq (Equation ps exs e) =
        Equation ps (get <$> exs) (get e)
          where
            get | name `elem` unions (free <$> ps) = fst
                | otherwise                        = snd

--desugar :: (MonadSupply Name m) => PatternExpr t -> m (RepExpr t)
--desugar = cata $ \case
--    EVar t var       -> pure (tagVar t var)
--    ELit t lit       -> pure (tagLit t lit)
--    EApp t exs       -> tagApp t <$> sequence exs
--    ELet t rep e1 e2 -> tagLet t rep <$> e1 <*> e2
--    ELam t rep ex    -> tagLam t rep <$> ex
--    EMatch t exs eqs -> do
--        resPair <- runWriterT (traverse desugarEquation eqs)
--        exs1 <- sequence exs
--        exs2 <- traverse desugar (snd resPair)
--        pure (tagMatch t (exs1 <> exs2) (fst resPair))
--
--desugarEquation :: (MonadSupply Name m) => Equation (Pattern t) (m (RepExpr t)) -> WriterT [PatternExpr t] m (RepEq t)
--desugarEquation (Equation ps exs e) =
--    Equation <$> traverse patternRep ps
--             <*> lift (sequence exs) 
--             <*> lift e 

repVars :: Rep t -> [(Name, t)]
repVars = cata $ \case
    RVar t var    -> [(var, t)]
    RCon _ con rs -> concat rs

patternReps :: [Pattern t] -> ([Rep t], [PatternExpr t])
patternReps = fmap concat . unzip . fmap patternRep

patternRep :: Pattern t -> (Rep t, [PatternExpr t])
patternRep pat = fromJust (evalSupply (runWriterT (toRep pat)) (nameSupply "$"))

toRep :: Pattern t -> WriterT [PatternExpr t] (Supply Name) (Rep t)
toRep =  cata alg where
    alg pat = do
        case pat of
            PVar t var    -> pure (rVar t var)
            PCon t con ps -> rCon t con <$> sequence ps 
            PAny t        -> pure (rVar t "$_")
            PLit t lit -> do
                var <- supply
                tell [tagEq (tagVar t var) (tagLit t lit)]
                pure (rVar t var)

data Head = ConHead | VarHead
    deriving (Show, Eq, Ord)

headType :: Equation (Rep t) a -> Head
headType (Equation ps _ _) = 
    case unfix <$> ps of
        RVar{}:_ -> VarHead
        _        -> ConHead

equationGroups :: [SimpleEq t] -> [(Head, [SimpleEq t])]
equationGroups = cata alg . fmap taggedEq 
  where
    alg :: Algebra (ListF (Head, SimpleEq t)) [(Head, [SimpleEq t])]
    alg Nil =
        []
    alg (Cons (pt, eq) []) =
        [(pt, [eq])]
    alg (Cons (pt, eq) (group@(qt, eqs):gs))
        | pt == qt  = (pt, eq:eqs):gs
        | otherwise = (pure <$> taggedEq eq):group:gs

    taggedEq eq = (headType eq, eq)

conGroups :: [SimpleEq t] -> [(Name, [Rep t], t, [SimpleEq t])]
conGroups =
    concatMap conGroup
      . groupSortOn (fst3 . fst)
      . concatMap expanded
  where
    expanded (Equation (Fix (RCon t con rs):qs) c e) =
        [((con, rs, t), Equation (rs <> qs) c e)]
    expanded _ =
        []
    conGroup gs@(((con, rs, t), _):_) =
        [(con, rs, t, snd <$> gs)]
    conGroup [] =
        []
