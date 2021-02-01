{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
module Tau.Stuff where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Map.Strict (Map)
import Data.Void
import Data.List
import Data.Tuple.Extra
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Expr.Main
import Tau.Type
import Tau.Type.Main
import Tau.Util
import qualified Tau.Env as Env
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

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

--
-- Substitution
--

apply = undefined

newtype Sub = Sub { getSub :: Map Name (Type Void) }
    deriving (Show, Eq)

mapsTo :: Name -> Type Void -> Sub
mapsTo name val = Sub (Map.singleton name val)

compose :: Sub -> Sub -> Sub
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)


--
-- Type checker
--

type ClassEnv a = [a] -- TODO!!

--type NodeInfo = (Type, [Predicate])    -- TODO!!
type NodeInfo = (Type Void, [Int])

type TypeEnv = Env Scheme

newTVar :: (MonadSupply Name m) => Kind -> m (Type a)
newTVar kind = tVar kind <$> supply 

infer
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => PatternExpr t 
  -> StateT Sub m (PatternExpr NodeInfo)
infer = cata alg
  where
    alg expr = do
        newTy <- newTVar kTyp
        case expr of
            EVar _ var -> do
                undefined

            ECon _ con exprs -> do
                undefined

            ELit _ lit -> do
                undefined

            EApp _ exprs -> do
                undefined

            ELet _ pat expr1 expr2 -> do
                undefined

            ELam _ pat expr1 -> do
                undefined

            EIf _ cond tr fl -> do
                undefined

            EOp  _ (OAnd a b) -> inferLogicOp OAnd a b
            EOp  _ (OOr  a b) -> inferLogicOp OOr a b
            EOp  _ _ -> undefined

            EMat _ exs eqs -> do
                undefined

            ERec _ fields -> do
                undefined

inferClause =
    undefined

inferLiteral :: (MonadSupply Name m) => Literal -> StateT Sub m (Type a)
inferLiteral = pure . \case
    LUnit{}    -> tUnit
    LBool{}    -> tBool
    LInt{}     -> tInt
    LInteger{} -> tInteger
    LFloat{}   -> tFloat
    LChar{}    -> tChar
    LString{}  -> tString

inferPattern =
    undefined

inferLogicOp
  :: (MonadSupply Name m, MonadError String m) 
  => (PatternExpr NodeInfo -> PatternExpr NodeInfo -> Op (PatternExpr NodeInfo))
  -> StateT Sub m (PatternExpr NodeInfo)
  -> StateT Sub m (PatternExpr NodeInfo)
  -> StateT Sub m (PatternExpr NodeInfo)
inferLogicOp op a b = do
    newTy <- newTVar kTyp
    e1 <- a
    e2 <- b
    --unify22 newTy tBool
    --unify22 (typeOf5 e1) tBool
    --unify22 (typeOf5 e2) tBool 
    pure (opExpr (newTy, []) (op e1 e2))
