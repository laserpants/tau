{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Class where
--module Tau.Type.Classes where

import Control.Monad.Except
import Control.Monad.Extra (allM, (||^))
import Data.List (partition, (\\))
import Data.Either (isRight)
import Data.Either.Combinators (rightToMaybe)
import Tau.Type
import Tau.Expr
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Tau.Env as Env



bySuper :: ClassEnv a -> InClass -> [InClass]
bySuper env self@(InClass name ty) = 
    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

byInstance :: ClassEnv a -> InClass -> Maybe [InClass]
byInstance env self@(InClass name ty) = 
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Instance a -> Either a [InClass]
    tryInstance (Instance ps h _) = 
        apply <$> matchClass (InClass name h) self <*> pure ps

instance Substitutable InClass where
    apply sub (InClass name ty) = InClass name (apply sub ty)

entail :: ClassEnv a -> [InClass] -> InClass -> Either a Bool
entail env cls0 cl = pure super ||^ instances
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instances = case byInstance env cl of
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: InClass -> Bool
isHeadNormalForm (InClass _ t) = 
    flip cata t $ \case
        TApp t _ -> t
        TVar{}   -> True
        TGen{}   -> True
        _        -> False

toHeadNormalForm :: ClassEnv a -> [InClass] -> Either a [InClass]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = case byInstance env tycl of
            Nothing  -> error "ContextReductionFailed" -- throwError ContextReductionFailed Just cls -> toHeadNormalForm env cls


-- remove a class constraint if it is entailed by the other constraints in the list
simplify :: ClassEnv a -> [InClass] -> Either a [InClass]
simplify env = loop [] where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        entailed <- entail env (qs <> ps) p
        if entailed then loop qs ps 
             else loop (p:qs) ps

reduce :: ClassEnv a -> [InClass] -> Either a [InClass]
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
