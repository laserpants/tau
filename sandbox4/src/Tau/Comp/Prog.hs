{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Comp.Prog where

import Control.Arrow ((>>>), (<<<))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (Sum, Product)
import Data.Foldable hiding (null)
import Data.Maybe (fromJust, fromMaybe)
import Data.List ((\\), nub)
import Data.Set.Monad (Set)
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution hiding (null)
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

data ProgEnv f = ProgEnv
    { progTypeEnv  :: TypeEnv
    , progExprEnv  :: Env Core
    , progConstrs  :: ConstructorEnv
    , progClassEnv :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f)
--    { progValueEnv :: ValueEnv Eval
    } deriving (Show, Eq)

emptyProgEnv :: ProgEnv f
emptyProgEnv = ProgEnv mempty mempty mempty mempty

modifyProgConstrs :: (MonadState (ProgEnv f) m) => (ConstructorEnv -> ConstructorEnv) -> m ()
modifyProgConstrs f = modify (\ProgEnv{..} -> ProgEnv{ progConstrs = f progConstrs, .. })

modifyExprEnv :: (MonadState (ProgEnv f) m) => (Env Core -> Env Core) -> m ()
modifyExprEnv f = modify (\ProgEnv{..} -> ProgEnv{ progExprEnv = f progExprEnv, .. })

modifyTypeEnv :: (MonadState (ProgEnv f) m) => (TypeEnv -> TypeEnv) -> m ()
modifyTypeEnv f = modify (\ProgEnv{..} -> ProgEnv{ progTypeEnv = f progTypeEnv, .. })

--compileType :: (MonadError String m, MonadState ProgEnv m) => Datatype -> m ()
compileType :: (MonadState (ProgEnv f) m) => Datatype -> m ()
compileType (Sum name vars prods) = do
    -- Update constructor environment
    modifyProgConstrs (flip (foldr (`Env.insert` constrs)) constrs)
    -- Update type environment
    mapM_ insertConType prods
--    -- Update expr environment
--    modifyExprEnv (flip (foldr insertConstructor) prods)
  where
    constrs = Set.fromList ((\(Prod con _) -> con) <$> prods)

--    insertConstructor :: Product -> Env Core -> Env Core
--    insertConstructor (Prod con _) = 
--        Env.insert con (cVar con)
--    --insertConstructor (Prod con ts) = 
--        --Env.insert con (cConstructor (length ts) con) 

    insertConType :: (MonadState (ProgEnv f) m) => Product -> m ()
    insertConType (Prod con ts) = do 

        let ty = ttt name (tVar kTyp <$> vars)
            missing = nub (free ts) \\ free ty

        unless (null missing) (error ("One or more type variables are missing in the type: " <> show missing))

        ProgEnv{..} <- get
        case runInfer3 mempty progTypeEnv (generalize (foldr tArr ty ts)) of
            Left err -> 
                error "TODO"
            Right (scheme, (sub, _)) 
                | Env.isMember con progTypeEnv -> 
                    error ("A data constructor named " <> Text.unpack con <> " already exists")
                | otherwise -> 
                    put ProgEnv{ progTypeEnv = Env.insert con (apply sub scheme) progTypeEnv, .. }

-- TODO: DRY
ttt :: Name -> [Type] -> Type
ttt con ts = setKind (foldr1 kArr (kTyp:ks)) (foldl1 tApp (tCon kTyp con:ts))
  where
    ks = fromJust . kindOf <$> ts

--ttt con ts = setKind (kArr kTyp kind) (foldl1 tApp (tCon kTyp con:ts))
--  where kind = foldr1 kArr (fromJust . kindOf <$> ts)

---

-- TODO: DRY

type InferState  = StateT (Substitution, Context)
type InferReader = ReaderT (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) ()), TypeEnv)
type InferSupply = SupplyT Name
type InferError  = ExceptT String

runInferState :: StateT (Substitution, Context) m a -> m (a, (Substitution, Context))
runInferState = flip runStateT mempty

runInferReader :: a -> b -> ReaderT (a, b) m r -> m r
runInferReader a b = flip runReaderT (a, b)

runInferSupply :: (Monad m) => SupplyT Name m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInferError :: ExceptT e m a -> m (Either e a)
runInferError = runExceptT

runInferMaybe :: Maybe (Either String a) -> Either String a
runInferMaybe = fromMaybe (Left "error")

type InferStack = InferState (InferReader (InferSupply (InferError Maybe)))

--runInfer :: InferStack a -> Either String (a, (Substitution, Context))
runInfer3 classEnv typeEnv = runInferState
    >>> runInferReader classEnv typeEnv
    >>> runInferSupply
    >>> runInferError
    >>> runInferMaybe

---

compileDefinition :: (MonadState (ProgEnv f) m) => Definition -> m ()
compileDefinition Def{..} = do
    -- Check if patterns are exhaustive

    -- Compile local definitions

    ProgEnv{..} <- get
--    let xx = runInfer3 progClassEnv progTypeEnv (infer (patExpr () [] defClauses))
    undefined

compileClass :: (MonadState (ProgEnv f) m) => Class ProgExpr -> m ()
compileClass class_ = undefined

compileInstance :: (MonadState (ProgEnv f) m) => Instance ProgExpr -> m ()
compileInstance = undefined

compileModule :: (MonadState (ProgEnv f) m) => Module -> m ()
compileModule = undefined
