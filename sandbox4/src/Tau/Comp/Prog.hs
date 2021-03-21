{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE StrictData        #-}
module Tau.Comp.Prog where

import Control.Arrow ((>>>), (<<<))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (Sum, Product)
import Data.Foldable hiding (null)
import Data.List ((\\), nub, delete)
import Data.Maybe (fromJust, fromMaybe)
import Data.Set.Monad (Set)
import Data.Void
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution hiding (null)
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

type TypedAst = Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo)

type Internals = 
    ( TypedAst 
    , Ast Type Void Void
    , Context )

data ProgEnv = ProgEnv
    { progTypeEnv   :: TypeEnv
    , progExprEnv   :: Env Core
    , progCtorEnv   :: ConstructorEnv
    , progClassEnv  :: ClassEnv 
    , progInternals :: Env Internals
    } deriving (Show, Eq)

emptyProgEnv :: ProgEnv
emptyProgEnv = ProgEnv mempty mempty mempty mempty mempty

modifyCtorEnv :: (MonadState ProgEnv m) => (ConstructorEnv -> ConstructorEnv) -> m ()
modifyCtorEnv f = modify (\ProgEnv{..} -> ProgEnv{ progCtorEnv = f progCtorEnv, .. })

modifyExprEnv :: (MonadState ProgEnv m) => (Env Core -> Env Core) -> m ()
modifyExprEnv f = modify (\ProgEnv{..} -> ProgEnv{ progExprEnv = f progExprEnv, .. })

modifyTypeEnv :: (MonadState ProgEnv m) => (TypeEnv -> TypeEnv) -> m ()
modifyTypeEnv f = modify (\ProgEnv{..} -> ProgEnv{ progTypeEnv = f progTypeEnv, .. })

modifyClassEnv :: (MonadState ProgEnv m) => (ClassEnv -> ClassEnv) -> m ()
modifyClassEnv f = modify (\ProgEnv{..} -> ProgEnv{ progClassEnv = f progClassEnv, .. })

modifyInternals :: (MonadState ProgEnv m) => (Env Internals -> Env Internals) -> m ()
modifyInternals f = modify (\ProgEnv{..} -> ProgEnv{ progInternals = f progInternals, .. })

compileType :: (MonadState ProgEnv m) => Datatype -> m ()
compileType (Sum name vars prods) = do

    -- Update constructor environment
    modifyCtorEnv (flip (foldr (`Env.insert` ctors)) ctors)

    -- Update type environment
    mapM_ insertCtorType prods

  where
    ctors = Set.fromList ((\(Prod con _) -> con) <$> prods)

    insertCtorType :: (MonadState ProgEnv m) => Product -> m ()
    insertCtorType (Prod con ts) = do 

        let ty = ttt name (tVar kTyp <$> vars)
            missing = nub (free ts) \\ free ty

        unless (null missing) (error ("One or more type variables are missing in the type: " <> show missing))

        ProgEnv{..} <- get
        case runInfer3 mempty mempty progTypeEnv (generalize (foldr tArr ty ts)) of
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

---

-- TODO: DRY

type InferState  = StateT (Substitution, Context)
type InferReader = ReaderT (ClassEnv, TypeEnv)
type InferSupply = SupplyT Name
type InferError  = ExceptT String

runInferState :: Context -> StateT (Substitution, Context) m a -> m (a, (Substitution, Context))
runInferState ctx = flip runStateT (mempty, ctx)

runInferReader :: a -> b -> ReaderT (a, b) m r -> m r
runInferReader a b = flip runReaderT (a, b)

runInferSupply :: (Monad m) => SupplyT Name m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInferError :: ExceptT e m a -> m (Either e a)
runInferError = runExceptT

runInferMaybe :: Maybe (Either String a) -> Either String a
runInferMaybe = fromMaybe (Left "error")

type InferStack c d = InferState (InferReader (InferSupply (InferError Maybe)))

runInfer3 :: Context -> ClassEnv -> TypeEnv -> InferStack c d a -> Either String (a, (Substitution, Context))
runInfer3 ctx classEnv typeEnv = 
    runInferState ctx
    >>> runInferReader classEnv typeEnv
    >>> runInferSupply
    >>> runInferError
    >>> runInferMaybe

---

--compileDefinition :: (MonadError String m, MonadState ProgEnv m) => Definition -> m ()
--compileDefinition :: (MonadState ProgEnv m) => Definition -> m ()
compileDefinition :: (MonadState ProgEnv m) => Definition -> m ()
compileDefinition Def{..} = do
    -- TODO: Check if patterns are exhaustive

    -- TODO: Compile local definitions

    ProgEnv{..} <- get
    case runInfer3 mempty progClassEnv progTypeEnv steps of
        Left err ->
            error "TODO"
        Right ((ast, scheme, code), (_, ctx)) -> do
            --traceShowM ast
            --traceShowM "---"
            --traceShowM (pretty scheme)
            --traceShowM "---"
            --traceShowM code

            modifyTypeEnv (Env.insert defName scheme)
            let core = fromJust (evalSupply (compileExpr (extractType code)) (numSupply "$"))
            modifyExprEnv (Env.insert defName core)
            modifyInternals (Env.insert defName (ast, extractType code, ctx))
  where
    steps = do
      ast <- infer (patExpr () [] defClauses)
      sub <- gets fst
      let expr = astApply sub ast
      scheme <- generalize (typeOf expr)
      code <- evalStateT (compileClasses (desugarOperators expr)) [] 
      pure (expr, scheme, code)

compileClass :: (MonadState ProgEnv m) => ClassInfo Name Type -> m ()
compileClass info@(super, InClass name var, methods) = do

    -- TODO: check if class already exists

    ProgEnv{..} <- get

    -- Update type environment
    let classEnv = Env.fromList [(var, Set.singleton name)]
    case runInfer3 classEnv mempty progTypeEnv (traverse foo methods) of
        Left err ->
            error "TODO"
        Right (types, _) ->
            modifyTypeEnv (flip (foldr (uncurry Env.insert)) types)

    -- Update expression environment
    let fields = fst <$> methods
        baz f = 
            let 
            -- Field () field (varPat () "e")])
                fields_ = Field () f (varPat () "$e"):[Field () g (anyPat ()) | g <- delete f fields]
                expr = patExpr () [] [ Clause [recPat () (fieldSet fields_)] [] (varExpr () "$e") ]
                core = fromJust (evalSupply (compileExpr expr) (numSupply "$")) -- TODO: DRY
             in Env.insert f core -- (patExpr () [] [ Clause [recPat () (fieldSet [] [] (varExpr () "$e"))] [] (varExpr () "$e") ])

    modifyExprEnv (flip (foldr baz) fields)

    -- Update class environment
    modifyClassEnv (Env.insert name (info, []))

--foo :: (Name, Type) -> m (Name, Scheme)
foo (name, ty) = (name ,) <$> generalize ty

compileInstance :: (MonadState ProgEnv m) => ClassInfo Type ProgExpr -> m ()
compileInstance (ps, InClass name ty, methods) = do
    undefined

compileModule :: (MonadState ProgEnv m) => Module -> m ()
compileModule = undefined

--    insertConstructor :: Product -> Env Core -> Env Core
--    insertConstructor (Prod con _) = 
--        Env.insert con (cVar con)
--    --insertConstructor (Prod con ts) = 
--        --Env.insert con (cConstructor (length ts) con) 
