{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Class where
--module Tau.Type.Classes where

import Data.Types.Injective
import Control.Monad.Except
import Control.Monad.Extra (allM, (||^))
import Data.List (partition, (\\))
import Control.Arrow (first, second)
import Data.Either (isRight)
import Data.Either.Combinators (rightToMaybe)
import Tau.Type
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Tau.Env as Env



--

type Class a = ([Name], [Instance a])

data Predicate = InClass Name Type
    deriving (Show, Eq, Ord)

instance Injective Predicate (Name, Type) where
    to (InClass name ty) = (name, ty)

predicateName :: Predicate -> Name
predicateName (InClass name _) = name

predicateType :: Predicate -> Type
predicateType (InClass _ ty) = ty

type QualifiedType = (Type, [Predicate])

data Instance a = Instance [Predicate] Type a
    deriving (Show, Eq)

type ClassEnv a = Env (Class a)

super :: ClassEnv a -> Name -> [Name]
super env name = maybe [] fst (Env.lookup name env)

instances :: ClassEnv a -> Name -> [Instance a]
instances env name = maybe [] snd (Env.lookup name env)

addClassInstance :: Name -> Type -> a -> ClassEnv a -> ClassEnv a
addClassInstance name ty ex =
    Env.update (Just . second (Instance [] ty ex :)) name

lookupClassInstance :: Name -> Type -> ClassEnv a -> Maybe a
lookupClassInstance name ty env = 
    case filter fff (instances env name) of
        [Instance _ _ t] -> Just t
        _                -> Nothing
  where
    fff (Instance _ t _) = t == ty



unifyClass, matchClass :: (MonadError String m) => Predicate -> Predicate -> m Substitution
unifyClass = liftX unify
matchClass = liftX match

liftX :: (MonadError String m) => (Type -> Type -> m a) -> Predicate -> Predicate -> m a
liftX m (InClass c1 t1) (InClass c2 t2)
    | c1 == c2  = m t1 t2
    | otherwise = throwError "ClassMismatch" -- throwError ClassMismatch


--


bySuper :: ClassEnv a -> Predicate -> [Predicate]
bySuper env self@(InClass name ty) = 
    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

byInstance :: ClassEnv a -> Predicate -> Maybe [Predicate]
byInstance env self@(InClass name ty) = 
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Instance a -> Either String [Predicate]
    tryInstance (Instance ps h _) = 
        apply <$> matchClass (InClass name h) self <*> pure ps

instance Substitutable Predicate where
    apply sub (InClass name ty) = InClass name (apply sub ty)

entail :: ClassEnv a -> [Predicate] -> Predicate -> Either a Bool
entail env cls0 cl = pure super ||^ instances
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instances = case byInstance env cl of
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: Predicate -> Bool
isHeadNormalForm (InClass _ t) = 
    flip cata t $ \case
        TApp t1 _ -> t1
        TVar{}    -> True
        TGen{}    -> True
        _         -> False

toHeadNormalForm :: ClassEnv a -> [Predicate] -> Either a [Predicate]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = case byInstance env tycl of
            Nothing  -> error "ContextReductionFailed" -- throwError ContextReductionFailed Just cls -> toHeadNormalForm env cls


-- remove a class constraint if it is entailed by the other constraints in the list
simplify :: ClassEnv a -> [Predicate] -> Either a [Predicate]
simplify env = loop [] where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        entailed <- entail env (qs <> ps) p
        if entailed then loop qs ps 
             else loop (p:qs) ps

reduce :: ClassEnv a -> [Predicate] -> Either a [Predicate]
reduce env cls = toHeadNormalForm env cls >>= simplify env 







--

testClassEnv :: ClassEnv (Expr () (Pattern ()) (Pattern ()))
testClassEnv =
    Env.fromList
        [ ( "Ord"  , ordClass )
        , ( "Show" , showClass )
        ]


ordClass =
    ( -- "Ord"
      ["Eq"]                                       -- Eq is a superclass
    , [ Instance [] tUnit (varExpr () "xx1")              -- () is in Ord
      , Instance [] tInt  (varExpr () "xx1")              -- Int is in Ord 
      , Instance [InClass "Ord" (tVar kStar "a")]  
                 (tList (tVar kStar "a"))          -- Ord a => Ord [a]
                 (varExpr () "xxx")
      ]
    )


showClass =
    ( -- "Show"
      []                               
    , [ Instance [] tInt (recExpr () [Field () "show" (varExpr () "@showInt")])
      ]
    )







--overlap :: TypeClass -> TypeClass -> Bool
--overlap a b = isRight (runExcept (unifyClass a b))
--
--bySuper :: ClassEnv -> TypeClass -> [TypeClass]
--bySuper env self@(TypeClass name ty) = 
--    self:concat [bySuper env (TypeClass tc ty) | tc <- super env name]
--
--byInstance :: ClassEnv -> TypeClass -> Maybe [TypeClass]
--byInstance env self@(TypeClass name ty) = 
--    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
--  where
--    tryInstance :: Qualified TypeClass -> Either TypeError [TypeClass]
--    tryInstance (ps :=> h) = 
--        apply <$> matchClass h self <*> pure ps
--
--entail :: ClassEnv -> [TypeClass] -> TypeClass -> Either TypeError Bool
--entail env cls0 cl = pure super ||^ instc
--  where
--    super = any (cl `elem`) (bySuper env <$> cls0)
--    instc = case byInstance env cl of
--        Nothing   -> pure False
--        Just cls1 -> allM (entail env cls0) cls1
--
--isHeadNormalForm :: TypeClass -> Bool
--isHeadNormalForm (TypeClass _ t) = 
--    flip cata t $ \case
--        TApp t _ -> t
--        TVar{}   -> True
--        TGen{}   -> True
--        _        -> False
--
--toHeadNormalForm :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
--toHeadNormalForm env = fmap concat . mapM (hnf env) 
--  where
--    hnf env tycl 
--        | isHeadNormalForm tycl = pure [tycl]
--        | otherwise = case byInstance env tycl of
--            Nothing  -> throwError ContextReductionFailed
--            Just cls -> toHeadNormalForm env cls
--
---- remove a class constraint if it is entailed by the other constraints in the list
--simplify :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
--simplify env = loop [] where
--    loop qs [] = pure qs
--    loop qs (p:ps) = do
--        entailed <- entail env (qs <> ps) p
--        if entailed then loop qs ps 
--             else loop (p:qs) ps
--
--reduce :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
--reduce env cls = toHeadNormalForm env cls >>= simplify env 
--
---- The first, fs, specifies the set of ‘fixed’ variables, which are just the 
---- variables appearing free in the assumptions. The second, gs, specifies the 
---- set of variables over which we would like to quantify; 
--
--split :: ClassEnv -> [Name] -> [Name] -> [TypeClass] -> Either TypeError ([TypeClass], [TypeClass])
--split env fs gs ps = do 
--    qs <- reduce env ps
--    let (ds, rs) = partition (all (`elem` fs) . free) qs
--    pure (ds, rs)
--    -- TODO
----    rs1 <- defaultedPreds env (fs <> gs) rs
----    pure (ds, rs \\ rs1)
--
--defaultedPreds = undefined
