{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
module Tau.Type.Class where

import Control.Monad.Except
import Control.Monad.Extra (allM)
import Data.Either (isRight)
import Data.Either.Combinators (rightToMaybe)
import Tau.Type
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Tau.Env as Env

overlap :: TyClass -> TyClass -> Bool
overlap a b = isRight (runExcept (unifyClass a b))

bySuper :: ClassEnv -> TyClass -> [TyClass]
bySuper env self@(TyClass name ty) = 
    self:concat [bySuper env (TyClass tc ty) | tc <- super env name]

byInstance :: ClassEnv -> TyClass -> Maybe [TyClass]
byInstance env self@(TyClass name ty) = 
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Qualified TyClass -> Either UnificationError [TyClass]
    tryInstance (ps :=> h) = 
        apply <$> matchClass h self <*> pure ps

entail :: ClassEnv -> [TyClass] -> TyClass -> Either UnificationError Bool
entail env cls0 cl = do
    i <- instc
    pure (super || i)
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instc = case byInstance env cl of
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: TyClass -> Bool
isHeadNormalForm (TyClass _ t) = 
    flip cata t $ \case
        TApp t _ -> t
        TVar{}   -> True
        TBound{} -> True
        _        -> False

toHeadNormalForm :: ClassEnv -> [TyClass] -> Either UnificationError [TyClass]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = case byInstance env tycl of
            Nothing  -> throwError ContextReductionFailed
            Just cls -> toHeadNormalForm env cls

-- remove a class constraint if it is entailed by the other constraints in the list
simplify :: ClassEnv -> [TyClass] -> Either UnificationError [TyClass]
simplify env = loop [] where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        b <- entail env (qs <> ps) p
        if b then loop qs ps 
             else loop (p:qs) ps

reduce :: ClassEnv -> [TyClass] -> Either UnificationError [TyClass]
reduce env cls = toHeadNormalForm env cls >>= simplify env 

-- scEntail :: ClassEnv -> [TyClass] -> TyClass -> Bool
-- scEntail env tycls = undefined
