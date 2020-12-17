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

type SimpleRep t = PatternF t Name

data Equation p a = Equation [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Equation
deriveEq1   ''Equation

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
    | EMat t [a] [Equation p a]
    | EOp  t (Op a)
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

type Expr t p q = Fix (ExprF t p q)

type PatternExpr t = Expr t (Pattern t) (Pattern t)

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
    PVar t _   -> t
    PCon t _ _ -> t
    PLit t _   -> t
    PAny t     -> t

getRepTag :: SimpleRep t -> t
getRepTag = \case
    PVar t _   -> t
    PCon t _ _ -> t

setRepTag :: t -> SimpleRep s -> SimpleRep t
setRepTag t = \case
    PVar _ var    -> PVar t var
    PCon _ con rs -> PCon t con rs

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

matExpr :: t -> [Expr t p q] -> [Equation p (Expr t p q)] -> Expr t p q
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

--

--

type Gex t = Expr t (SimpleRep t) Name

data InF a
    = AMatch [Gex ()] [Equation (Pattern ()) (Gex ())] a
    | AFail
    deriving (Show, Eq, Functor, Foldable, Traversable)

type In = Fix InF

data OutF m a
    -- = Case a (m [(SimpleRep (), a)])
--    = Defer a
    = Grok (m a)
    | Suitcase a [(SimpleRep (), a)]
    | If a a a -- (Gex ()) (Gex ()) a
    | D (Gex ())
    | Fail -- ?
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Out m = Fix (OutF  m)

deriveShow1 ''InF
deriveEq1   ''InF

deriveShow1 ''OutF
deriveEq1   ''OutF


--


data GSeedF t m a
    = GMatch [Gex t] [Equation (Pattern t) (Gex t)] a
    | GCase (Gex t) (m [(SimpleRep t, a)])
    | GIf (Gex t) a (Gex t)
    | GFail
    deriving (Functor, Foldable, Traversable)

type GSeed t m = Fix (GSeedF t m)

deriveShow1 ''GSeedF
deriveEq1   ''GSeedF

--type Gex m t = m (Expr t (SimpleRep t) Name)
--data GSeedF t m a
--    = GMatch [Gex m t] [Equation (Pattern t) (Gex m t)] a
--    | GCase (Gex m t) (m [(SimpleRep t, a)])
--    | GBase (Gex m t)
--    | GIf (Gex m t) a a
--    | GFail
--    | H a
--    deriving (Functor, Foldable, Traversable)
 

--

type Ex t = Expr t (SimpleRep t) Name

data FSeedF t a
    = FMatch [Ex t] [Equation (Pattern t) (Ex t)] a
    | FCase (Ex t) [(SimpleRep t, a)]
    | FBase (Ex t)
    | FIf (Ex t) a a
    | FFail
    | G a
    deriving (Functor, Foldable, Traversable)
    --deriving (Show, Functor, Foldable, Traversable)

--deriveShow1 ''FSeedF
--deriveEq1   ''FSeedF

type FSeed t = Fix (FSeedF t)

--instance Show (Supply Name a) where
--    show _ = ""

--deriveShow1 ''Supply Name a
