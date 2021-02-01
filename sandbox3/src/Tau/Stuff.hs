{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
module Tau.Stuff where

import Data.List
import Data.Tuple.Extra
import Tau.Expr
import Tau.Type
import Tau.Expr.Main
import Tau.Type.Main
import Tau.Util

--class TaggedA a t where
--    getTag :: a -> t
--    setTag :: t -> a -> a
--
--updateTag :: (TaggedA a t) => (t -> t) -> a -> a
--updateTag f a = let tag = getTag a in setTag (f tag) a
--
--instance TaggedA (Expr t p q) t where
--    getTag = cata $ 
--        \case
--          EVar t _       -> t
--          ECon t _ _     -> t
--          ELit t _       -> t
--          EApp t _       -> t
--          ELet t _ _ _   -> t
--          ELam t _ _     -> t
--          EIf  t _ _ _   -> t
--          EMat t _ _     -> t
--          EOp  t _       -> t
--          ERec t _       -> t
--    setTag t = cata $ 
--        \case
--          EVar _ var     -> varExpr t var
--          ECon _ con exs -> conExpr t con exs
--          ELit _ lit     -> litExpr t lit
--          EApp _ exs     -> appExpr t exs
--          ELet _ p e1 e2 -> letExpr t p e1 e2
--          ELam _ p e1    -> lamExpr t p e1
--          EIf  _ c e1 e2 -> ifExpr  t c e1 e2
--          EMat _ exs eqs -> matExpr t exs eqs
--          EOp  _ op      -> opExpr  t op
--          ERec _ fields  -> recExpr t fields
--
--instance TaggedA (Pattern t) t where
--    getTag = cata $ 
--        \case
--          PVar t _       -> t
--          PCon t _ _     -> t
--          PLit t _       -> t
--          PRec t _       -> t
--          PAny t         -> t
--    setTag t = cata $ 
--        \case
--          PVar _ var     -> varPat t var
--          PCon _ con ps  -> conPat t con ps
--          PLit _ lit     -> litPat t lit
--          PRec _ fields  -> recPat t fields
--          PAny _         -> anyPat t
--
--instance TaggedA (Prep t) t where
--    getTag = 
--        \case
--          RVar t _       -> t
--          RCon t _ _     -> t
--    setTag t = 
--        \case
--          RVar _ var     -> RVar t var
--          RCon _ con rs  -> RCon t con rs
--
--instance TaggedA (Field t a) t where
--    getTag   (Field t _ _) = t
--    setTag t (Field _ n v) = Field t n v
--
--mapTags :: (s -> t) -> Expr s (Pattern s) (Pattern s) -> Expr t (Pattern t) (Pattern t)
--mapTags f = cata $ 
--    \case
--      EVar t var      -> varExpr (f t) var
--      ECon t con exs  -> conExpr (f t) con exs
--      ELit t lit      -> litExpr (f t) lit
--      EApp t exs      -> appExpr (f t) exs
--      ELet t p e1 e2  -> letExpr (f t) (mapPatternTags f p) e1 e2
--      ELam t p e1     -> lamExpr (f t) (mapPatternTags f p) e1
--      EIf  t c e1 e2  -> ifExpr  (f t) c e1 e2
--      EMat t exs eqs  -> matExpr (f t) exs (clause <$> eqs)
--      EOp  t op       -> opExpr  (f t) op
--      ERec t fields   -> recExpr (f t) (mapField f <$> fields)
--  where
--    clause (Clause ps exs e) =
--        Clause (mapPatternTags f <$> ps) exs e
--
--mapPatternTags :: (s -> t) -> Pattern s -> Pattern t
--mapPatternTags f = cata $ 
--    \case
--      PVar t var    -> varPat (f t) var
--      PCon t con ps -> conPat (f t) con ps
--      PLit t lit    -> litPat (f t) lit
--      PRec t fields -> recPat (f t) (mapField f <$> fields)
--      PAny t        -> anyPat (f t)
--
--mapField :: (s -> t) -> Field s a -> Field t a
--mapField f (Field t n v) = Field (f t) n v

--sortFields :: [Field a c] -> [Field a c]
--sortFields = sortOn (\(Field _ n _) -> n)

--fieldInfos = (to <$>) . sortFields

--

--getTag :: Expr t p q -> t
--getTag = cata $ \case
--    EVar t _     -> t
--    ECon t _ _   -> t
--    ELit t _     -> t
--    EApp t _     -> t
--    ELet t _ _ _ -> t
--    ELam t _ _   -> t
--    EIf  t _ _ _ -> t
--    EMat t _ _   -> t
--    EOp  t _     -> t
--
--setTag :: t -> Expr t p q -> Expr t p q
--setTag t = cata $ \case
--    EVar _ var     -> varExpr t var
--    ECon _ con exs -> conExpr t con exs
--    ELit _ lit     -> litExpr t lit
--    EApp _ exs     -> appExpr t exs
--    ELet _ p e1 e2 -> letExpr t p e1 e2
--    ELam _ p e1    -> lamExpr t p e1
--    EIf  _ c e1 e2 -> ifExpr  t c e1 e2
--    EMat _ exs eqs -> matExpr t exs eqs
--    EOp  _ op      -> opExpr  t op
--
--modifyTag :: (t -> t) -> Expr t p q -> Expr t p q
--modifyTag f p = setTag (f (getTag p)) p

--getPatternTag :: Pattern t -> t
--getPatternTag = cata $ \case
--    PVar t _   -> t
--    PCon t _ _ -> t
--    PLit t _   -> t
--    PAny t     -> t
--
--setPatternTag :: t -> Pattern t -> Pattern t
--setPatternTag t = cata $ \case
--    PVar _ var    -> varPat t var
--    PCon _ con ps -> conPat t con ps
--    PLit _ lit    -> litPat t lit
--    PAny _        -> anyPat t
--
--modifyPatternTag :: (t -> t) -> Pattern t -> Pattern t
--modifyPatternTag f p = setPatternTag (f (getPatternTag p)) p
--
--getPrepTag :: Prep t -> t
--getPrepTag = \case
--    RVar t _   -> t
--    RCon t _ _ -> t
--
--setPrepTag :: t -> Prep s -> Prep t
--setPrepTag t = \case
--    RVar _ var    -> RVar t var
--    RCon _ con rs -> RCon t con rs
--
--modifyPrepTag :: (t -> t) -> Prep t -> Prep t
--modifyPrepTag f p = setPrepTag (f (getPrepTag p)) p

--

--

--
--



expr1 :: PatternExpr ()
expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")


--type NodeInfo = (Type, [Predicate])
--
--infer
--  :: (MonadSupply Name m, MonadReader (ClassEnv a, Env Scheme) m, MonadError String m) 
--  => PatternExpr t 
--  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
--infer =
--    undefined
