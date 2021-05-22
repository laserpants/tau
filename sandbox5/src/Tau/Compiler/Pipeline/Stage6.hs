{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage6 where

import Tau.Tool
import Tau.Core
import Tau.Lang
import Tau.Compiler.Pipeline

type SourceExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (SimplifiedPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate
  :: (Monad m)
  => SourceExpr t
  -> m Core
translate = cata $ \case
    EVar _ var       -> pure (cVar var)
    ELit _ lit       -> pure (cLit lit)
    EApp _ exs       -> sequenceExs exs
    EFix _ var e1 e2 -> cLet var <$> e1 <*> e2
    ELam _ var e1    -> cLam var <$> e1
    EIf  _ e1 e2 e3  -> cIf <$> e1 <*> e2 <*> e3
    ECon _ con exs   -> sequenceExs (pure (cVar con):exs)
    EPat _ eqs cs -> do 
        sequence eqs >>= \case
            [expr] -> cPat expr <$> traverse desugarClause cs
            _      -> error "Implementation error"

desugarClause 
  :: (Monad m) 
  => SimplifiedClause t (SimplifiedPattern t) (m Core)
  -> m ([Name], Core)
desugarClause (SimplifiedClause t [SCon _ con ps] (Guard [] e)) = 
    (,) (con:ps) <$> e
desugarClause _ = 
    error "Implementation error"

sequenceExs :: (Monad m) => [m Core] -> m Core
sequenceExs = (fun <$>) . sequence
  where
    fun = \case
        [e] -> e
        es  -> cApp es
