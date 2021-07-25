{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Bundle where

import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.State
import Data.Aeson
import Data.Maybe
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
import Tau.Type
import Tau.Util
import qualified Tau.Compiler.Pipeline.Stage0 as Stage0
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6

data Bundle = Bundle
    { sourceExpr  :: ProgExpr ()
    , typedExpr   :: ProgExpr (TypeInfoT [Error] Type)
    , normalExpr  :: ProgExpr (TypeInfoT [Error] Type)
    , stage1Expr  :: Maybe (Stage1.TargetExpr (TypeInfoT [Error] (Maybe Type)))
    , stageX1Expr :: Maybe StageX1ExprYY
    , stageX2Expr :: Maybe StageX1ExprYY
    , stageX3Expr :: Maybe (StageX1ExprYYY (Maybe Type))
    , stageX5Expr :: Maybe (Stage5.TargetExpr (Maybe Type))
    , stage2Expr  :: Maybe (Stage2.WorkingExpr (Maybe Type))
    , stage3Expr  :: Maybe (Stage3.TargetExpr (Maybe Type))
    , stage4Expr  :: Maybe (Stage4.TargetExpr (Maybe Type))
    , stage5Expr  :: Maybe (Stage5.TargetExpr (Maybe Type))
    , stageX6Expr :: Maybe Core
    , coreExpr    :: Maybe Core
    , value       :: Maybe (Tau.Eval.Value Eval)
    , value2      :: Maybe (Tau.Eval.Value Eval)
    } deriving (Show, Eq)

instance ToRep Bundle where
    toRep Bundle{..} =
        object 
            ( [ "source"  .= toRep sourceExpr
              , "typed"   .= toRep typedExpr
              , "normal"  .= toRep normalExpr
              , "stage1"  .= toRep stage1Expr
              , "stageX"  .= toRep stageX1Expr
              , "stage2"  .= toRep stage2Expr
              , "stageX2" .= toRep stageX2Expr
              , "stage3"  .= toRep stage3Expr
              , "stageX3" .= toRep stageX3Expr
              , "stage4"  .= toRep stage4Expr
              , "stage5"  .= toRep stage5Expr
              , "stageX5" .= toRep stageX5Expr
              , "stageX6" .= toRep stageX6Expr
              , "core"    .= toRep coreExpr
              ] <> valueField <> value2Field )
      where
        valueField = case value of
            Nothing  -> []
            Just val -> ["value" .= toRep val]
        value2Field = case value2 of
            Nothing  -> []
            Just val -> ["value2" .= toRep val]

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
    constructorEnv <- askConstructorEnv
    classEnv <- askClassEnv
    let normal_ = Stage0.foo2 context constructorEnv classEnv (getAst ast)
        normal  = Stage0.runExhaustivePatternsCheck constructorEnv normal_
    -- TODO
    --
    
    let bundle = Bundle
          { sourceExpr  = mapExprTag (const ()) expr
          , typedExpr   = getAst ast
          , normalExpr  = normal
          , stage1Expr  = Nothing
          , stageX1Expr = Nothing
          , stage2Expr  = Nothing
          , stageX2Expr = Nothing
          , stage3Expr  = Nothing
          , stageX3Expr = Nothing
          , stage4Expr  = Nothing
          , stage5Expr  = Nothing
          , stageX5Expr = Nothing
          , stageX6Expr = Nothing
          , coreExpr    = Nothing
          , value       = Nothing
          , value2      = Nothing
          }

    --

    if not (hasErrors normal) 
        then do
            let expr1 = Stage1.translate (getAst (Just <$$> ast))

            exprX1 <- runTranslate44 (expandExpr expr1)
            let exprX2 = translateLiteral3 exprX1
            exprX3 <- runTranslate44 (evalStateT (compileTypeclasses exprX2) mempty)
            let exprX5 = Stage5.runTranslate (Stage5.translate222 exprX3)
            exprX6 <- Stage6.translate exprX5

            --

            expr2 <- runStage2 expr1

            let expr3 = Stage3.runTranslate (Stage3.translate expr2)
            let expr4 = Stage4.translate expr3
            let expr5 = Stage5.runTranslate (Stage5.translate expr4)
--
--            expr6 <- Stage6.translate expr5

--            traceShowM "vv"
--            traceShowM (pretty exprX3)
--            traceShowM "vvvv"
--            traceShowM (pretty expr5)

            pure (bundle
                    { stage1Expr  = Just expr1
                    , stageX1Expr = Just exprX1
                    , stageX2Expr = Just exprX2
                    , stageX3Expr = Just exprX3
                    , stageX5Expr = Just exprX5
                    , stageX6Expr = Just exprX6
                    , stage2Expr  = Just expr2
                    , stage3Expr  = Just expr3
                    , stage4Expr  = Just expr4
--                    , stage5Expr  = Just expr5
--                    , coreExpr    = Just expr6
                    })
        else 
            pure bundle

    --traceShowM (toRep bundle)
    --traceShowM (toRep bundle)

    --traceShowM (stage1Expr bundle)
    --traceShowM (coreExpr bundle)
