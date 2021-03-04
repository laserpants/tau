{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Tau.Comp.Classes where

import Control.Arrow
import Control.Monad.Error.Class (liftEither)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Data.Foldable (foldrM)
import Data.List (nub)
import Data.Maybe (fromJust)
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import qualified Data.Text as Text

compileClasses 
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (Ast NodeInfo), TypeEnv) m)
  => Ast (NodeInfoT Type)
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type)) 
compileClasses expr = 
    insertDictArgs <$> run expr <*> collect
  where
    run = cata $ \case

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            xs <- collect
            letExpr t pat (insertDictArgs e1 xs) <$> expr2

--        EOp2 t op expr1 expr2 -> do
--            op2Expr t op <$> expr1 <*> expr2

--        EOp1 _ op a -> 
--            undefined
--
--        EOp2 _ op expr1 expr2 -> do
--            a <- expr1
--            b <- expr2
--            appExpr <$> sequence [pure (prefix2 op), a, b]
--
--        prefix2 op = 
--            varExpr ("(" <> opSymbol op <> ")")

        EVar t var -> 
            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)

        e -> 
            embed <$> sequence e


insertDictArgs :: Ast NodeInfo -> [(Name, Type)] -> Ast NodeInfo
insertDictArgs expr = foldr fun expr
  where
    fun (a, b) = lamExpr (NodeInfo (tArr b (typeOf expr)) []) [varPat (NodeInfo b []) a] 

collect :: (MonadState [(Name, Type)] m) => m [(Name, Type)]
collect = nub <$> acquireState

applyDicts
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (Ast NodeInfo), TypeEnv) m)
  => Predicate
  -> Ast (NodeInfoT Type)
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type))
applyDicts (InClass name ty) expr 

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
            dict = varExpr (NodeInfo t []) tv
        modify ((tv, t) :)
        let expr' = setExprTag (NodeInfo (t `tArr` typeOf expr) []) expr
        pure (appExpr (exprTag expr) [expr', dict])

    | otherwise = do
        env <- asks fst
        case lookupClassInstance name ty env of
            Left e -> throwError e
            Right (_ , Instance{..}) -> do
                -- TODO: super-classes???
                dict <- compileClasses instanceDict
                let expr' = setExprTag (NodeInfo (typeOf dict `tArr` typeOf expr) []) expr
                pure (appExpr (exprTag expr) [expr', dict])

setNodeType :: Type -> NodeInfo -> NodeInfo
setNodeType ty info = info{ nodeType = ty }

setNodePredicates :: [Predicate] -> NodeInfoT a -> NodeInfoT a
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: NodeInfoT a -> NodeInfoT a
stripNodePredicates = setNodePredicates []
