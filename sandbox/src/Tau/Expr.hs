-- {-# LANGUAGE DeriveFoldable    #-}
-- {-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Expr where

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

data RepF t a
    = RVar t Name
    | RCon t Name [a]
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''RepF
deriveEq1   ''RepF

type Pattern   t = Fix (PatternF t)
type Rep       t = Fix (RepF t)
type SimpleRep t = RepF t Name

data Equation p a = Equation [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Equation
deriveEq1   ''Equation

data Op t a
    = OEq a a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Op
deriveEq1   ''Op

data ExprF t p q a
    = EVar t Name
    | ELit t Literal
    | EApp t [a]
    | ELet t q a a
    | ELam t q a
    | EIf t a ~a ~a
    | EAnd a ~a
    | EOr a ~a
    | EMatch t [a] [Equation p a]
    | EOp (Op t a)
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

type Expr t p q = Fix (ExprF t p q)

type PatternExpr t = Expr t (Pattern t) (Rep t)
type RepExpr     t = Expr t (Rep t) (Rep t)
type SimpleExpr  t = Expr t (SimpleRep t) (SimpleRep t)

type PatternEq   t = Equation (Pattern t) (PatternExpr t)
type RepEq       t = Equation (Rep t) (RepExpr t)
type SimpleEq    t = Equation (Rep t) (SimpleExpr t)

getTag :: Expr t p q -> t
getTag = cata $ \case
    EVar t _     -> t
    ELit t _     -> t
    EApp t _     -> t
    ELet t _ _ _ -> t
    ELam t _ _   -> t
    EMatch t _ _ -> t

getRepTag :: Rep t -> t
getRepTag = cata $ \case
    RVar t _   -> t
    RCon t _ _ -> t

setRepTag :: t -> Rep s -> Rep t
setRepTag t = cata $ \case
    RVar _ var    -> rVar t var
    RCon _ con rs -> rCon t con rs


pVar :: t -> Name -> Pattern t
pVar t var = Fix (PVar t var)

pCon :: t -> Name -> [Pattern t] -> Pattern t
pCon t con ps = Fix (PCon t con ps)

pLit :: t -> Literal -> Pattern t
pLit t lit = Fix (PLit t lit)

pAny :: t -> Pattern t
pAny t = Fix (PAny t)

rVar :: t -> Name -> Rep t
rVar t var = Fix (RVar t var)

rCon :: t -> Name -> [Rep t] -> Rep t
rCon t con rs = Fix (RCon t con rs)

sVar :: t -> Name -> SimpleRep t
sVar = RVar 

sCon :: t -> Name -> [Name] -> SimpleRep t
sCon = RCon 

eVar :: Name -> Expr () p q
eVar var = Fix (EVar () var)

eLit :: Literal -> Expr () p q
eLit lit = Fix (ELit () lit)

eApp :: [Expr () p q] -> Expr () p q
eApp exs = Fix (EApp () exs)

eLet :: q -> Expr () p q -> Expr () p q -> Expr () p q
eLet rep e1 e2 = Fix (ELet () rep e1 e2)

eLam :: q -> Expr () p q -> Expr () p q
eLam rep expr = Fix (ELam () rep expr)

eMatch :: [Expr () p q] -> [Equation p (Expr () p q)] -> Expr () p q
eMatch exs eqs = Fix (EMatch () exs eqs)

eIf :: Expr () p q -> Expr () p q -> Expr () p q -> Expr () p q
eIf cond tr fl = Fix (EIf () cond tr fl)

eErr = undefined

eAnd :: Expr t p q -> Expr t p q -> Expr t p q 
eAnd a b = Fix (EAnd a b)

eOr :: Expr t p q -> Expr t p q -> Expr t p q 
eOr a b = Fix (EOr a b)

eEq :: Expr () p q -> Expr () p q -> Expr () p q 
eEq a b = Fix (EOp (OEq a b))

tagVar :: t -> Name -> Expr t p q
tagVar t var = Fix (EVar t var)

tagLit :: t -> Literal -> Expr t p q
tagLit t lit = Fix (ELit t lit)

tagApp :: t -> [Expr t p q] -> Expr t p q
tagApp t exs = Fix (EApp t exs)

tagLet :: t -> q -> Expr t p q -> Expr t p q -> Expr t p q
tagLet t rep e1 e2 = Fix (ELet t rep e1 e2)

tagLam :: t -> q -> Expr t p q -> Expr t p q
tagLam t rep expr = Fix (ELam t rep expr)

tagMatch :: t -> [Expr t p q] -> [Equation p (Expr t p q)] -> Expr t p q
tagMatch t exs eqs = Fix (EMatch t exs eqs)

tagIf :: t -> Expr t p q -> Expr t p q -> Expr t p q -> Expr t p q
tagIf t cond tr fl = Fix (EIf t cond tr fl)

tagEq :: Expr t p q -> Expr t p q -> Expr t p q 
tagEq a b = Fix (EOp (OEq a b))

tagErr = undefined

--tagEq = undefined

-- -- data Literal
-- --     = LUnit
-- --     | LBool Bool
-- --     | LInt Int
-- --     deriving (Show, Eq)
-- -- 
-- -- data PatternF t a
-- --     = PVar t Name
-- --     | PCon t Name [a]
-- --     | PLit t Literal
-- --     | PAny t
-- --     deriving (Show, Eq, Functor, Foldable, Traversable)
-- -- 
-- -- deriveShow1 ''PatternF
-- -- deriveEq1   ''PatternF
-- -- 
-- -- type Pattern t = Fix (PatternF t)
-- -- 
-- -- data RepF t a
-- --     = RVar t Name
-- --     | RCon t Name [a]
-- --     deriving (Show, Eq, Functor, Foldable, Traversable)
-- -- 
-- -- deriveShow1 ''RepF
-- -- deriveEq1   ''RepF
-- -- 
-- -- type Rep t = Fix (RepF t)
-- -- 
-- -- type SimpleRep t = RepF t Name
-- -- 
-- -- data EquationF p a = EquationF [p] [a] a
-- --     deriving (Show, Eq, Functor, Foldable, Traversable)
-- -- 
-- -- deriveShow1 ''EquationF
-- -- deriveEq1   ''EquationF
-- -- 
-- -- --type Equation t p = EquationF p (Expr t p)
-- -- 
-- -- type Equation t p = Fix (EquationF (Expr t p))
-- -- 
-- -- ----data ExprF t p a
-- -- data ExprF t p a
-- --     = EVar t Name
-- --     | ELit t Literal
-- --     | EApp t [a]
-- --     | ELet t (Rep t) a a
-- --     | ELam t (Rep t) a
-- --     -- | EMatch t [a] [EquationF t p]
-- --     | EMatch t [a] [p]
-- --     deriving (Functor, Foldable, Traversable)
-- -- 
-- -- --type Expr t p = Fix (ExprF t p)
-- -- type Expr t p = Fix (ExprF t p)
-- -- 
-- -- deriveShow  ''ExprF
-- -- deriveShow1 ''ExprF
-- -- deriveEq    ''ExprF
-- -- deriveEq1   ''ExprF
-- -- 
-- -- getTag :: Expr t p -> t
-- -- getTag = cata $ \case
-- --     EVar t _     -> t
-- --     ELit t _     -> t
-- --     EApp t _     -> t
-- --     ELet t _ _ _ -> t
-- --     ELam t _ _   -> t
-- --     EMatch t _ _ -> t
-- -- 
-- -- bbb :: Expr t p
-- -- bbb = undefined
-- -- ----
-- -- --myEqs :: [EquationF t p]
-- -- --myEqs = [ EquationF [] [] bbb ]
-- -- --myEqs = [ EquationF [] [] bbb ]
-- -- ----
-- -- 
-- -- --pvar :: Name -> Pattern t
-- -- --pvar a1 = Fix (PVar a1)
-- -- --
-- -- --pcon :: Name -> [Pattern] -> Pattern
-- -- --pcon a1 a2 = Fix (PCon a1 a2)
-- -- --
-- -- --plit :: Literal -> Pattern
-- -- --plit a1 = Fix (PLit a1)
-- -- --
-- -- --pany :: Pattern
-- -- --pany = Fix PAny
-- -- --
-- -- ----rvar :: Name -> Rep t
-- -- ----rvar a1 = Fix (RVar a1)
-- -- ----
-- -- ----rcon :: Name -> [Rep t] -> Rep t
-- -- ----rcon a1 a2 = Fix (RCon a1 a2)
-- -- --
-- -- ----svar :: Name -> SimpleRep t
-- -- ----svar a1 = RVar a1
-- -- ----
-- -- ----scon :: Name -> [Name] -> SimpleRep t
-- -- ----scon a1 a2 = RCon a1 a2
-- -- --
-- -- ----evar :: Name -> Expr () p
-- -- --evar a1 = Fix (EVar () a1)
-- -- --
-- -- ----tagVar :: t -> Name -> Expr t p
-- -- tagVar t a1 = Fix (EVar t a1)
-- -- ----
-- -- ----elit :: Literal -> Expr () p
-- -- --elit a1 = Fix (ELit () a1)
-- -- ----
-- -- ----tagLit :: t -> Literal -> Expr t p
-- -- tagLit t a1 = Fix (ELit t a1)
-- -- ----
-- -- ---- eapp :: [Expr () p] -> Expr () p
-- -- --eapp a1 = Fix (EApp () a1)
-- -- ----
-- -- ---- tagApp :: t -> [Expr t p] -> Expr t p
-- -- tagApp t a1 = Fix (EApp t a1)
-- -- ----
-- -- ---- elet :: p -> Expr () p -> Expr () p -> Expr () p
-- -- --elet a1 a2 a3 = Fix (ELet () a1 a2 a3)
-- -- ----
-- -- ---- tagLet :: t -> p -> Expr t p -> Expr t p -> Expr t p
-- -- tagLet t a1 a2 a3 = Fix (ELet t a1 a2 a3)
-- -- ----
-- -- ---- elam :: p -> Expr () p -> Expr () p
-- -- --elam a1 a2 = Fix (ELam () a1 a2)
-- -- ----
-- -- ---- tagLam :: t -> p -> Expr t p -> Expr t p
-- -- tagLam t a1 a2 = Fix (ELam t a1 a2)
-- -- ----
-- -- ---- eif = undefined
-- -- ----
-- -- ---- tagIf = undefined
-- -- ----
-- -- ---- eand = undefined
-- -- ----
-- -- ---- tagAnd = undefined
-- -- ----
-- -- ---- eerr = undefined
-- -- ----
-- -- ---- eunit :: Expr () p
-- -- ---- eunit = elit LUnit
-- -- ----
-- -- ---- ebool :: Bool -> Expr () p
-- -- ---- ebool a1 = elit (LBool a1)
-- -- ----
-- -- ---- eint :: Int -> Expr () p
-- -- ---- eint a1 = elit (LInt a1)
