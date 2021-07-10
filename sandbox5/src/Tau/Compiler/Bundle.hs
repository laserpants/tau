{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Bundle where

import Control.Monad.Reader
import Data.Aeson
import Tau.Compiler.Error
import Tau.Compiler.Pipeline.Stage0 
import Tau.Compiler.Pipeline.Stage1 
import Tau.Compiler.Pipeline.Stage2 
import Tau.Compiler.Pipeline.Stage3 
import Tau.Compiler.Pipeline.Stage4 
import Tau.Compiler.Pipeline.Stage5 
import Tau.Compiler.Pipeline.Stage6 
import Tau.Compiler.Substitute
import Tau.Compiler.Typecheck
import Tau.Core
import Tau.Eval
import Tau.Lang
import Tau.Prog
import Tau.Serialize
import Tau.Tooling
import Tau.Type
import qualified Tau.Compiler.Pipeline.Stage0 as Stage0
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6

data Bundle = Bundle
    { sourceExpr :: ProgExpr ()
    , normalExpr :: ProgExpr Type
    , stage1Expr :: Stage1.TargetExpr (TypeInfoT [Error] (Maybe Type))
    , stage2Expr :: Stage2.WorkingExpr (Maybe Type)
    , stage3Expr :: Stage3.TargetExpr (Maybe Type)
    , stage4Expr :: Stage4.TargetExpr (Maybe Type)
    , stage5Expr :: Stage5.TargetExpr (Maybe Type)
    , coreExpr   :: Core
    } deriving (Show, Eq)

instance ToRep Bundle where
    toRep Bundle{..} =
        object 
            [ "source" .= toRep sourceExpr
            , "normal" .= toRep normalExpr
            , "stage1" .= toRep stage1Expr
            , "stage2" .= toRep stage2Expr
            , "stage3" .= toRep stage3Expr
            , "stage4" .= toRep stage4Expr
            , "stage5" .= toRep stage5Expr
            , "core"   .= toRep coreExpr  
            ]

runInferTree
  :: (MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m)
  => InferStack m (Ast (TypeInfo [Error]))
  -> m (Ast (TypeInfo [Error]), Substitution Type, Substitution Kind, Context)
runInferTree a = do
    (e1, e2, e3, e4) <- ask
    runInferT mempty e1 e2 e3 e4 a

runStage2
  :: (MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m)
  => Stage2.WorkingExpr (TypeInfoT [Error] (Maybe Type))
  -> m (Stage2.WorkingExpr (Maybe Type))
runStage2 expr = do
    (e1, e2, e3, e4) <- ask
    pure (Stage2.runTranslate e1 e2 e3 e4 (Stage2.translate expr))

compileBundle 
  :: (Monad m)
  => ProgExpr t
  -> ReaderT (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m Bundle
compileBundle expr = do

    (ast, _, _, context) <- runInferTree (inferAstType (Ast expr))

    -- TODO
    let normal = getAst (nodeType <$> ast)
    -- TODO

    let expr1 = Stage1.translate (getAst (Just <$$> ast))

    expr2 <- runStage2 expr1

    let expr3 = Stage3.runTranslate (Stage3.translate expr2)
    let expr4 = Stage4.translate expr3
    let expr5 = Stage5.runTranslate (Stage5.translate expr4)

    expr6 <- Stage6.translate expr5

    let bundle = Bundle
          { sourceExpr = mapExprTag (const ()) expr
          , normalExpr = normal
          , stage1Expr = expr1
          , stage2Expr = expr2
          , stage3Expr = expr3
          , stage4Expr = expr4
          , stage5Expr = expr5
          , coreExpr   = expr6 }

    --traceShowM (toRep bundle)
    --traceShowM (toRep bundle)

    --traceShowM (stage1Expr bundle)
    --traceShowM (coreExpr bundle)

    pure bundle
