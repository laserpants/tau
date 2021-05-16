module Tau.Compiler.Pipeline.Stage2 where

import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Tool

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

