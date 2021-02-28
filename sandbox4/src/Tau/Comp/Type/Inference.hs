{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
module Tau.Comp.Type.Inference where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Maybe (maybeToList)
import Data.Text (Text)
import Data.Tuple.Extra (second)
import Tau.Comp.Type.Substitution
import Tau.Comp.Type.Unification
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

type ClassEnv a = Env (Class a)

type TypeEnv = Env Scheme

instance Substitutable TypeEnv Type where
    apply sub = Env.map (apply sub)

instance Free TypeEnv where
    free = free . Env.elems

type Ast t = Expr t (Pattern t) (Binding (Pattern t)) [Pattern t]

data NodeInfo = NodeInfo 
    { nodeType       :: Type
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

instance Typed NodeInfo where
    typeOf = nodeType

instance (Typed t) => Typed (Ast t) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (Pattern t) where
    typeOf = typeOf . patternTag

infer 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m )
  => Ast t
  -> m (Ast NodeInfo)
infer = cata $ \expr -> do
    newTy <- newTVar kTyp
    case expr of
        EVar _ var -> do
            (ty, ps) <- lookupScheme var >>= instantiate
            unifyTyped ty newTy
            pure (varExpr (NodeInfo newTy ps) var)

        ECon _ con exprs -> do
            (ty, ps) <- lookupScheme con >>= instantiate
            es <- sequence exprs
            unifyTyped ty (foldr tArr newTy (typeOf <$> es))
            pure (conExpr (NodeInfo newTy ps) con es)

        ELit _ lit -> do
            ty <- inferLiteral lit
            unifyTyped newTy ty
            pure (litExpr (NodeInfo newTy []) lit)

        EApp _ exprs -> do
            es <- sequence exprs
            case es of
                []     -> pure ()
                f:args -> unifyTyped f (foldr tArr newTy (typeOf <$> args))
            pure (appExpr (NodeInfo newTy []) es)

        ELet _ (BLet pat) expr1 expr2 -> do
            (tp, vs) <- runWriterT (inferPattern pat)
            e1 <- expr1
            unifyTyped tp e1
            vs1 <- traverse (secondM generalize) vs
            e2 <- local (second (Env.inserts vs1)) expr2
            unifyTyped newTy e2
            pure (letExpr (NodeInfo newTy []) (BLet tp) e1 e2)

        ELet _ (BFun f pats) expr1 expr2 -> do
            (tps, vs) <- runWriterT (traverse inferPattern pats)
            e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
            t1 <- newTVar kTyp
            unifyTyped t1 (foldr tArr (typeOf e1) (typeOf <$> tps))
            e2 <- local (second (Env.insert f (toScheme t1))) expr2
            unifyTyped newTy e2
            pure (letExpr (NodeInfo newTy []) (BFun f tps) e1 e2)

        EFix _ name expr1 expr2 -> do
            t1 <- newTVar kTyp
            e1 <- local (second (Env.insert name (toScheme t1))) expr1
            unifyTyped t1 e1
            scheme <- generalize (typeOf e1)
            e2 <- local (second (Env.insert name scheme)) expr2
            unifyTyped newTy e2
            pure (fixExpr (NodeInfo newTy []) name e1 e2)

        ELam _ pats expr1 -> do            
            (tps, vs) <- runWriterT (traverse inferPattern pats)
            e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
            unifyTyped newTy (foldr tArr (typeOf e1) (typeOf <$> tps))
            pure (lamExpr (NodeInfo newTy []) tps e1)

        EIf  _ cond tr fl -> do
            e1 <- cond
            e2 <- tr
            e3 <- fl
            unifyTyped e1 (tBool :: Type)
            unifyTyped e2 e3
            unifyTyped newTy e2
            pure (ifExpr (NodeInfo newTy []) e1 e2 e3)

        --
        -- fun-expression, e.g.,
        --
        --    fun 
        --      | Some a => a
        --      | None   => 0
        --
        EPat _ [] eqs@(Clause ps _ _:_) -> do
            ts <- tVar kTyp <$$> supplies (length ps)
            es2 <- sequence (inferClause newTy ts <$> eqs)
            pure (patExpr (NodeInfo (foldr tArr newTy ts) []) [] es2)

        --
        -- Ordinary match expression
        --
        EPat _ exs eqs -> do
            es1 <- sequence exs
            es2 <- sequence (inferClause newTy (typeOf <$> es1) <$> eqs)
            pure (patExpr (NodeInfo newTy []) es1 es2)

        EOp1 _ ONot expr1 -> do
            a <- expr1
            unifyTyped newTy (tBool :: Type)
            pure (op1Expr (NodeInfo newTy []) ONot a)

        EOp1 _ ONeg expr1 -> do
            a <- expr1
            unifyTyped newTy (typeOf a)
            pure (op1Expr (NodeInfo newTy []) ONeg a)

        EOp2 _ op expr1 expr2 -> do
            a <- expr1
            b <- expr1
            let name = "(" <> opSymbol op <> ")"
            (ty, ps) <- lookupScheme name >>= instantiate
            unifyTyped (typeOf a `tArr` typeOf b `tArr` newTy) ty 
            pure (op2Expr (NodeInfo newTy ps) op a b)

        EDot _ name expr1 -> do          
            e1 <- expr1
            (ty, ps) <- lookupScheme name >>= instantiate
            unifyTyped (typeOf e1 `tArr` newTy) ty
            pure (dotExpr (NodeInfo newTy ps) name e1)

        ERec _ fields -> do
            let (_, ns, fs) = unzip3 (fieldList fields)
                info Field{..} = Field{ fieldTag = NodeInfo (typeOf fieldValue) [], .. }
            es <- sequence fs
            unifyTyped newTy (tRecord ns (typeOf <$> es))
            pure (recExpr (NodeInfo newTy []) (FieldSet (zipWith (info <$$> Field ()) ns es))) 

        ETup _ elems -> do
            tes <- sequence elems
            unifyTyped newTy (tTuple (typeOf <$> tes))
            pure (tupExpr (NodeInfo newTy []) tes)

        -- EAnn Scheme a           

inferLiteral :: (Monad m) => Literal -> m Type
inferLiteral = pure . \case
    LUnit{}    -> tUnit
    LBool{}    -> tBool
    LInt{}     -> tInt
    LInteger{} -> tInteger
    LFloat{}   -> tFloat
    LChar{}    -> tChar
    LString{}  -> tString

inferClause
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m ) 
  => Type
  -> [Type]
  -> Clause (Pattern t) (m (Ast NodeInfo))
  -> m (Clause (Pattern NodeInfo) (Ast NodeInfo))
inferClause ty types clause@(Clause ps _ _) = do
    (tps, vs) <- runWriterT (traverse inferPattern ps)
    let Clause _ exs e = local (second (Env.inserts (toScheme <$$> vs))) <$> clause
    forM_ exs (>>= unifyTyped (tBool :: Type) . typeOf)
    forM_ (zip tps types) (uncurry unifyTyped) 
    e >>= unifyTyped ty . typeOf
    Clause tps <$> sequence exs <*> e

inferPattern
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m ) 
  => Pattern t 
  -> WriterT [(Name, Type)] m (Pattern NodeInfo)
inferPattern = cata $ \pat -> do
    newTy <- newTVar kTyp
    case pat of
        PVar _ var -> do
            tell [(var, newTy)]
            pure (varPat (NodeInfo newTy []) var)

        PCon _ con ps -> do
            (ty, qs) <- lift (lookupScheme con >>= instantiate)
            trs <- sequence ps
            lift (unifyTyped ty (foldr tArr newTy (typeOf <$> trs)))
            pure (conPat (NodeInfo newTy qs) con trs)

        PLit _ lit -> do
            ty <- lift (inferLiteral lit)
            pure (litPat (NodeInfo ty []) lit)

        PRec _ fieldSet -> do
            let (_, ns, fs) = unzip3 (fieldList fieldSet)
            ps <- sequence fs
            let tfs = zipWith (\n p -> Field (patternTag p) n p) ns ps
            lift (unifyTyped newTy (tRecord ns (typeOf <$> ps)))
            pure (recPat (NodeInfo newTy []) (FieldSet tfs))

        PTup _ elems -> do
            ps <- sequence elems
            pure (tupPat (NodeInfo newTy []) ps)

        PAs  _ name pat -> do
            tell [(name, newTy)]
            asPat (NodeInfo newTy []) name <$> pat

        POr  _ pat1 pat2 -> do
            p1 <- pat1
            p2 <- pat2
            lift (unifyTyped newTy p1)
            lift (unifyTyped newTy p2)
            pure (orPat (NodeInfo newTy []) p1 p2)

        PAny _ ->
            pure (anyPat (NodeInfo newTy []))

instantiate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadError String m ) 
  => Scheme 
  -> m (Type, [Predicate])
instantiate (Forall kinds ps ty) = do
    names <- supplies (length kinds)
    let ts = zipWith tVar kinds names 
        preds = fun <$> ps
        fun p@(InClass name n) = ( names !! n
                                 , replaceBound ts <$> (tGen <$> p) )
--    modify (second (flip (foldr (uncurry (\k -> Env.insertWith (<>) k . pure))) preds))
    pure (replaceBound ts ty, snd <$> preds)

generalize
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m ) 
  => Type
  -> m Scheme
generalize ty = do
    env <- asks snd
    sub1 <- get
    let ty1   = apply sub1 ty
        pairs = filter ((`notElem` free (apply sub1 env)) . fst) (typeVars ty1)
        sub2  = fromList [(fst v, tGen n) | (v, n) <- zip pairs [0..]]
--    ps <- lookupPredicates (fst <$> pairs)
    pure (Forall (snd <$> pairs) 
                 (traverse (maybeToList . getTypeIndex) =<< apply sub2 
--                 (upgrade <$$> ps)) (apply sub2 (upgrade ty1)))
                 []) (apply sub2 (upgrade ty1)))

lookupScheme 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m ) 
  => Name 
  -> m Scheme
lookupScheme name = do
    env <- asks snd 
    case Env.lookup name env of
        Nothing     -> throwError ("Unbound type identifier: " <> Text.unpack name)
        Just scheme -> gets apply <*> pure scheme
--        Just scheme -> gets (apply . fst) <*> pure scheme

unified 
  :: ( MonadState Substitution m 
     , MonadError String m ) 
  => Type 
  -> Type 
  -> m Substitution
unified t1 t2 = do
    sub1 <- get
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    pure (sub2 <> sub1)

unifyTyped 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadState Substitution m
     , MonadError String m
     , Typed t
     , Typed u ) 
  => t
  -> u
  -> m ()
unifyTyped v1 v2 = do 
    sub <- unified (typeOf v1) (typeOf v2)
    modify (sub <>)
--    modify (second (Env.map (apply sub) >>> propagateClasses sub))
