module Tau.Compiler.Pipeline.Stage2 where

import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate 
  :: SourceExpr (TypeInfoT [Error] (Maybe Type))
  -> SourceExpr (Maybe Type)
translate = undefined
