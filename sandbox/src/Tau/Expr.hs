{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE FlexibleInstances #-}
module Tau.Expr where

import Control.Monad.Supply
import Tau.Type
import Tau.Util

data Literal
    = LUnit
    | LBool Bool
    | LInt Int
    deriving (Show, Eq)

data PatternF t a
    = PVar t Name
    | PCon t Name [a]
    | PLit t Literal
    | PAny t
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''PatternF
deriveEq1   ''PatternF

type Pattern t = Fix (PatternF t)

data Prep t
    = RVar t Name
    | RCon t Name [Name]
    deriving (Show, Eq)

data Clause p a = Clause [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Clause
deriveEq1   ''Clause

data Op a
    = OEq  a a
    | OAnd a ~a
    | OOr  a ~a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Op
deriveEq1   ''Op

data ExprF t p q a
    = EVar t Name
    | ECon t Name [a]
    | ELit t Literal
    | EApp t [a]
    | ELet t q a a
    | ELam t q a
    | EIf  t a ~a ~a
    | EMat t [a] [Clause p a]
    | EOp  t (Op a)
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

type Expr t p q = Fix (ExprF t p q)

getTag :: Expr t p q -> t
getTag = cata $ \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    ELet t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EMat t _ _   -> t
    EOp  t _     -> t

getPatternTag :: Pattern t -> t
getPatternTag = cata $ \case
    PVar t _     -> t
    PCon t _ _   -> t
    PLit t _     -> t
    PAny t       -> t

getRepTag :: Prep t -> t
getRepTag = \case
    RVar t _     -> t
    RCon t _ _   -> t

setRepTag :: t -> Prep s -> Prep t
setRepTag t = \case
    RVar _ var    -> RVar t var
    RCon _ con rs -> RCon t con rs


--
--
--getRepTag :: SimpleRep t -> t
--getRepTag = \case
--    PVar t _   -> t
--    PCon t _ _ -> t

--setRepTag :: t -> SimpleRep s -> SimpleRep t
--setRepTag t = \case
--    PVar _ var    -> PVar t var
--    PCon _ con rs -> PCon t con rs

varPat :: t -> Name -> Pattern t
varPat t var = embed (PVar t var)

conPat :: t -> Name -> [Pattern t] -> Pattern t
conPat t con ps = embed (PCon t con ps)

litPat :: t -> Literal -> Pattern t
litPat t lit = embed (PLit t lit)

anyPat :: t -> Pattern t
anyPat t = embed (PAny t)

varExpr :: t -> Name -> Expr t p q 
varExpr t var = embed (EVar t var)

conExpr :: t -> Name -> [Expr t p q] -> Expr t p q 
conExpr t con exs = embed (ECon t con exs)

litExpr :: t -> Literal -> Expr t p q 
litExpr t lit = embed (ELit t lit)

appExpr :: t -> [Expr t p q] -> Expr t p q 
appExpr t exs = embed (EApp t exs)

letExpr :: t -> q -> Expr t p q -> Expr t p q -> Expr t p q
letExpr t rep e1 e2 = embed (ELet t rep e1 e2)

lamExpr :: t -> q -> Expr t p q -> Expr t p q
lamExpr t rep expr = embed (ELam t rep expr)

matExpr :: t -> [Expr t p q] -> [Clause p (Expr t p q)] -> Expr t p q
matExpr t exs eqs = embed (EMat t exs eqs)

ifExpr :: t -> Expr t p q -> Expr t p q -> Expr t p q -> Expr t p q
ifExpr t cond tr fl = embed (EIf t cond tr fl)

opExpr :: t -> Op (Expr t p q) -> Expr t p q 
opExpr t op = embed (EOp t op)

eqOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
eqOp t e1 e2 = embed (EOp t (OEq e1 e2))

andOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
andOp t e1 e2 = embed (EOp t (OAnd e1 e2))

orOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
orOp t e1 e2 = embed (EOp t (OOr e1 e2))
