{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.UnificationTests where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Supply
import Data.Either (isLeft, isRight)
import Data.List (intersect, (\\))
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Tau.Compiler.Substitute
import Tau.Compiler.Unify
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tooling
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "The types " <> prettyText t1 <> " and " <> prettyText t2 

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = runUnify (unifyTypes t1 t2)
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right (typeSub, kindSub) = result
                r1 = apply kindSub (apply typeSub t1)
                r2 = apply kindSub (apply typeSub t2)
            canon r1 == canon r2

canon :: Type -> Type
canon = cata $ \case
    TVar k var       -> tVar k var
    TCon k con       -> tCon k con
    TApp k t1 t2     -> tApp k t1 t2
    TArr t1 t2       -> tArr t1 t2
    TRow label t1 t2 -> toCanonicalRow (tRow label t1 t2)

toCanonicalRow :: Type -> Type
toCanonicalRow t = fromMap (baseRow t) (foldr (uncurry f) mempty (rowFields t))
  where
    fromMap :: Type -> Map Name [Type] -> Type
    fromMap = Map.foldrWithKey (flip . foldr . tRow)

    rowFields :: Type -> [(Name, Type)]
    rowFields = para $ \case
        TRow label ty rest             -> (label, fst ty):snd rest
        _                              -> []

    baseRow :: Type -> Type
    baseRow = cata $ \case
        TRow _ _ r                     -> r
        t                              -> embed t

    f name ty = Map.insertWith (<>) name [ty]

--toCanonicalRow = uncurry fromMap . toMap
--  where
--    fromMap :: Type -> Map Name [Type] -> Type
--    fromMap = Map.foldrWithKey (flip . foldr . tRow)
--
--    toMap :: Type -> (Type, Map Name [Type])
--    toMap t = (getBaseRow t, foldr (uncurry f) mempty (getRowExts t))
--      where
--        f name ty = Map.insertWith (<>) (getLabel name) [ty]
--        getLabel  = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
--
--    getRowExts :: Type -> [(Name, Type)]
--    getRowExts = para $ \case
--        TApp _ (Fix (TCon _ con), _) t -> [(con, fst t)]
--        TApp _ a b                     -> snd a <> snd b
--        TArr a b                       -> snd a <> snd b
--        TVar{}                         -> []
--        _                              -> []
--
--    getBaseRow :: Type -> Type
--    getBaseRow = cata $ \case
--        TApp _ _ t                     -> t
--        t                              -> embed t

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = runUnify (unifyTypes t1 t2)
    describe (testDescription t1 t2) $
        it "✗ fails to unify" $
            isLeft result

runUnify :: SupplyT Name (ExceptT err Maybe) a -> Either err a
runUnify x = fromJust (runExceptT (evalSupplyT x (numSupply "")))

--import Data.Either (isLeft, isRight)
--import Data.Text (Text)
--import Tau.Compiler.Substitution
--import Tau.Compiler.Unification
--import Tau.Lang
--import Tau.Pretty
--import Tau.Row
--import Tau.Type
--import Test.Hspec hiding (describe, it)
--import Utils
--
--testBind :: SpecWith ()
--testBind = do
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testIsRow :: SpecWith ()
--testIsRow = do
--
--    describe "TODO" $ do pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testDescription :: Type -> Type -> Text
--testDescription t1 t2 = "The types " <> prettyText t1 <> " and " <> prettyText t2 
--
--failUnifyTypes :: Type -> Type -> SpecWith ()
--failUnifyTypes t1 t2 = do
--    let result = unify t1 t2
--    describe (testDescription t1 t2) $
--        it "✗ fails to unify" $
--            isLeft result
--
--succeedUnifyTypes :: Type -> Type -> SpecWith ()
--succeedUnifyTypes t1 t2 = do
--    let result = unify t1 t2
--    describe (testDescription t1 t2) $ do
--        it "✔ yields a substitution" $
--            isRight result
--
--        it "✔ and it unifies the two types" $ do
--            let Right sub = result
--                r1 = apply sub t1 
--                r2 = apply sub t2
--            if kRow == kindOf r1
--                then typeToRow r1 == typeToRow r2
--                else r1 == r2

testUnify :: SpecWith ()
testUnify = do

    succeedUnifyTypes
        (_a `tArr` _b)
        (tInt `tArr` tInt)

    failUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tBool)

    succeedUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tInt)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _a)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _b)

    failUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (tInt `tArr` tInt `tArr` tBool)

    succeedUnifyTypes
        (tList _a)
        (tList tInt)
        
    succeedUnifyTypes
        (tList _a)
        (tList _b)

    failUnifyTypes
        (tList _a)
        (tPair _a _b)

    succeedUnifyTypes
        (tPair _a _a)
        (tPair _a _b)

    failUnifyTypes
        (tPair _a _a)
        (tPair tInt tBool)

    failUnifyTypes
        (tList _a)
        tInt

    succeedUnifyTypes
        tInt
        tInt

    failUnifyTypes
        tUnit
        tInt

    succeedUnifyTypes
        (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))     -- { name : a26 | a27 }
        (tRow "id" tInt (tRow "name" tString tRowNil))  -- { id : Int, name : String }

    succeedUnifyTypes
        (tArr (tRow "name" (tVar kTyp "a26") (tVar kRow "a27")) (tVar kTyp "a"))   
        (tArr (tRow "id" tInt (tRow "name" tString tRowNil)) tInt)

    succeedUnifyTypes
        (tArr (tRecord (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))) (tVar kTyp "a"))   
        (tArr (tRecord (tRow "id" tInt (tRow "name" tString tRowNil))) tInt)

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testMatch :: SpecWith ()
--testMatch = do
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testUnifyPairs :: SpecWith ()
--testUnifyPairs = do
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testMatchPairs :: SpecWith ()
--testMatchPairs = do
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testUnifyRowTypes :: SpecWith ()
testUnifyRowTypes = do

    failUnifyTypes
        (tRow "name" tString (tRow "id" tInt tRowNil))
        (tRow "id" tString (tRow "name" tInt tRowNil))

    succeedUnifyTypes
        (tRow "name" tString (tRow "id" tInt tRowNil))
        (tRow "id" tInt (tRow "name" tString tRowNil))

    succeedUnifyTypes
        (tRow "x" tInt (tVar kRow "r"))
        (tRow "x" tInt (tVar kRow "r"))

    failUnifyTypes
        (tRow "x" tInt (tVar kRow "r"))
        (tRow "y" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRow "x" tInt (tVar kRow "r"))
        (tRow "x" tInt (tVar kRow "s"))

    succeedUnifyTypes
        (tRow "id" tInt (tVar kRow "r"))
        (tRow "id" tInt (tRow "name" tString tRowNil))

    succeedUnifyTypes
        (tRow "id" tInt (tRow "name" tString tRowNil))
        (tRow "id" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
        (tRow "id" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
        (tVar kRow "r")

    failUnifyTypes
        (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
        (tVar kTyp "r")  --- Note: Not a row kind!

    succeedUnifyTypes
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        (tRow "shoeSize" tFloat (tRow "id" tInt (tRow "name" tString tRowNil)))

    succeedUnifyTypes
        -- { name : String, shoeSize : Float }
        (tRow "name" tString (tRow "shoeSize" tFloat tRowNil))
        -- { shoeSize : Float | r }
        (tRow "shoeSize" tFloat (tVar kRow "r"))

    succeedUnifyTypes
        -- { name : String, id : Int, shoeSize : Float }
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        -- { shoeSize : Float, id : Int | r }
        (tRow "shoeSize" tFloat (tRow "id" tInt (tVar kRow "r")))

    succeedUnifyTypes
        -- { name : String, id : Int, shoeSize : Float }
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        -- { shoeSize : Float | r }
        (tRow "shoeSize" tFloat (tVar kRow "r"))

    succeedUnifyTypes
        (tRow "shoeSize" tFloat (tVar kRow "r"))
        (tRow "name" tString (tRow "shoeSize" tFloat tRowNil))

    succeedUnifyTypes
        (tRow "shoeSize" tFloat (tRow "id" tInt (tVar kRow "r")))
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))

    succeedUnifyTypes
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        (tRow "name" tString (tRow "id" tInt (tVar kRow "r")))

    succeedUnifyTypes
        (tRow "name" tString (tRow "id" tInt tRowNil))
        (tRow "name" tString (tRow "id" (tVar kTyp "a") tRowNil))

    succeedUnifyTypes
        (tRow "name" tString (tRow "id" (tVar kTyp "a") tRowNil))
        (tRow "name" tString (tRow "id" tInt tRowNil))

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testMatchRowTypes :: SpecWith ()
--testMatchRowTypes = do
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--succeedTypeToRow :: Type -> Row Type -> SpecWith ()
--succeedTypeToRow ty row =
--    describe ("The type " <> prettyText ty) $ 
--        it ("✔ unfolds to " <> prettyText row)
--            (typeToRow ty == row)
--
--testTypeToRow :: SpecWith ()
--testTypeToRow = do
--
--    succeedTypeToRow 
--        (tVar kRow "r") 
--        (rVar (tVar kRow "r"))
--
--    succeedTypeToRow 
--        tRowNil
--        rNil
--
--    succeedTypeToRow 
--        (tRow "id" tInt tRowNil)
--        (rExt "id" tInt rNil)
--
--    succeedTypeToRow 
--        (tRow "id" tInt (tVar kRow "r"))
--        (rExt "id" tInt (rVar (tVar kRow "r")))
--
--    succeedTypeToRow 
--        (tRow "name" tString (tRow "id" tInt (tVar kRow "r")))
--        (rExt "name" tString (rExt "id" tInt (rVar (tVar kRow "r"))))
--
--    succeedTypeToRow 
--        (tRow "name" tString (tRow "id" tInt tRowNil))
--        (rExt "name" tString (rExt "id" tInt rNil))
