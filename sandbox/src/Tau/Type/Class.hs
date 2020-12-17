{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
module Tau.Type.Class where

import Control.Monad.Except
import Control.Monad.Extra (allM, (||^))
import Data.Either (isRight)
import Data.Either.Combinators (rightToMaybe)
import Tau.Type
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Tau.Env as Env

overlap :: TypeClass -> TypeClass -> Bool
overlap a b = isRight (runExcept (unifyClass a b))

bySuper :: ClassEnv -> TypeClass -> [TypeClass]
bySuper env self@(TypeClass name ty) = 
    self:concat [bySuper env (TypeClass tc ty) | tc <- super env name]

byInstance :: ClassEnv -> TypeClass -> Maybe [TypeClass]
byInstance env self@(TypeClass name ty) = 
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Qualified TypeClass -> Either TypeError [TypeClass]
    tryInstance (ps :=> h) = 
        apply <$> matchClass h self <*> pure ps

entail :: ClassEnv -> [TypeClass] -> TypeClass -> Either TypeError Bool
entail env cls0 cl = pure super ||^ instc
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instc = case byInstance env cl of
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: TypeClass -> Bool
isHeadNormalForm (TypeClass _ t) = 
    flip cata t $ \case
        TApp t _ -> t
        TVar{}   -> True
        TBound{} -> True
        _        -> False

toHeadNormalForm :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = case byInstance env tycl of
            Nothing  -> throwError ContextReductionFailed
            Just cls -> toHeadNormalForm env cls

-- remove a class constraint if it is entailed by the other constraints in the list
simplify :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
simplify env = loop [] where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        entailed <- entail env (qs <> ps) p
        if entailed then loop qs ps 
             else loop (p:qs) ps

reduce :: ClassEnv -> [TypeClass] -> Either TypeError [TypeClass]
reduce env cls = toHeadNormalForm env cls >>= simplify env 
