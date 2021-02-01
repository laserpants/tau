module Tau.Expr.Main where

import Data.List (sortOn)
import Data.Tuple.Extra
import Tau.Expr
import Tau.Util

varPat :: t -> Name -> Pattern t
varPat = embed2 PVar

conPat :: t -> Name -> [Pattern t] -> Pattern t
conPat = embed3 PCon

litPat :: t -> Literal -> Pattern t
litPat = embed2 PLit

recPat :: t -> [Field t (Pattern t)] -> Pattern t
recPat = embed2 PRec

anyPat :: t -> Pattern t
anyPat = embed1 PAny 

varExpr :: t -> Name -> Expr t p q
varExpr = embed2 EVar

conExpr :: t -> Name -> [Expr t p q] -> Expr t p q
conExpr = embed3 ECon 

litExpr :: t -> Literal -> Expr t p q
litExpr = embed2 ELit 

appExpr :: t -> [Expr t p q] -> Expr t p q
appExpr = embed2 EApp 

letExpr :: t -> q -> Expr t p q -> Expr t p q -> Expr t p q
letExpr = embed4 ELet 

lamExpr :: t -> q -> Expr t p q -> Expr t p q
lamExpr = embed3 ELam 

matExpr :: t -> [Expr t p q] -> [Clause p (Expr t p q)] -> Expr t p q
matExpr = embed3 EMat 

ifExpr :: t -> Expr t p q -> Expr t p q -> Expr t p q -> Expr t p q
ifExpr = embed4 EIf

recExpr :: t -> [Field t (Expr t p q)] -> Expr t p q
recExpr = embed2 ERec 

opExpr :: t -> Op (Expr t p q) -> Expr t p q
opExpr = embed2 EOp 

binOpExpr :: (a -> b -> Op (Expr t p q)) -> t -> a -> b -> Expr t p q
binOpExpr op t a b = opExpr t (op a b)

eqOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
eqOp = binOpExpr OEq 

andOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
andOp = binOpExpr OAnd 

orOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
orOp = binOpExpr OOr

fieldsInfo :: [Field a c] -> [(a, Name, c)]
fieldsInfo = sortOn snd3 . (to <$>)
