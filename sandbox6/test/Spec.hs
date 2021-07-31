{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad.Except (runExceptT)
import Data.Either (isLeft, isRight)
import Data.Functor.Foldable (cata, para, embed)
import Data.Map.Strict (Map)
import Data.Text (Text, unpack)
import Tau.Misc
import Tau.Util (Name, runSupplyNats)
import Test.Hspec hiding (describe, it)
import qualified Data.Map.Strict as Map
import qualified Test.Hspec as Hspec

describe :: Text -> SpecWith () -> SpecWith ()
describe = Hspec.describe . unpack

it :: (Example a) => Text -> a -> SpecWith (Arg a)
it = Hspec.it . unpack

main :: IO ()
main =
    hspec $ do
        describe "Unification"  testUnification
        describe "Substitution" testSubstitution
        describe "Type vars"    testTypeVars
        describe "Kind of"      testKindOf
        describe "toPolytype"   testToPolytype
        describe "tupleCon"     testTupleCon

_a :: Type
_a = tVar kTyp "a"

_b :: Type
_b = tVar kTyp "b"

_c :: Type
_c = tVar kTyp "c"

-------------------------------------------------------------------------------

-- Unification tests

runUnify :: Type -> Type -> Either UnificationError (Substitution Type, Substitution Kind)
runUnify t1 t2 = runSupplyNats (runExceptT (unifyTypes t1 t2))

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "TODO" -- "The types " <> prettyPrint t1 <> " and " <> prettyPrint t2

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = runUnify t1 t2
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right (typeSub, kindSub) = result
                r1 = apply kindSub (apply typeSub t1)
                r2 = apply kindSub (apply typeSub t2)
            canonicalRep r1 == canonicalRep r2

canonicalRep :: Type -> Type
canonicalRep = cata $ \case
    TVar k var       -> tVar k var
    TCon k con       -> tCon k con
    TApp k t1 t2     -> tApp k t1 t2
    TArr t1 t2       -> tArr t1 t2
    TRow label t1 t2 -> toCanonical (tRow label t1 t2)
  where
    toCanonical t =
        fromMap (baseRow t) (foldr (uncurry f) mempty (rowFields t))

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

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = runUnify t1 t2
    describe (testDescription t1 t2) $
        it "✗ fails to unify" $
            isLeft result

testUnification :: SpecWith ()
testUnification = do

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

    describe "Row types" $ do

        succeedUnifyTypes
            -- { name : a26 | a27 }
            (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))
            -- { id : Int, name : String }
            (tRow "id" tInt (tRow "name" tString tRowNil))

        succeedUnifyTypes
            (tArr (tRow "name" (tVar kTyp "a26") (tVar kRow "a27")) (tVar kTyp "a"))
            (tArr (tRow "id" tInt (tRow "name" tString tRowNil)) tInt)

        succeedUnifyTypes
            (tArr (tRecord (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))) (tVar kTyp "a"))
            (tArr (tRecord (tRow "id" tInt (tRow "name" tString tRowNil))) tInt)

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

-------------------------------------------------------------------------------

-- Substitution tests

succeedApplyTo :: Substitution Type -> Type -> Type -> SpecWith ()
succeedApplyTo sub ty res =
    describe "TODO" $ do -- ("apply " <> prettyPrint (show sub) <> " to " <> prettyPrint ty) $ do
        it ("✔ returns: " <> "TODO") -- prettyPrint res)
            (apply sub ty == res)

succeedComposeAndApplyTo :: Substitution Type -> Substitution Type -> Type -> Type -> SpecWith ()
succeedComposeAndApplyTo sub1 sub2 ty res =
    describe ("apply TODO to ") $ do -- TODO <> prettyPrint ty) $ do
        it ("✔ returns: ") --  <> prettyPrint res)
            (apply (compose sub1 sub2) ty == res)

testSubstitution :: SpecWith ()
testSubstitution = do

    describe "Apply to" $ do

        succeedApplyTo
            (mapsTo "a" tInt)
            _a
            tInt

        succeedApplyTo
            (mapsTo "a" tInt)
            (_a `tArr` _b)
            (tInt `tArr` _b)

        succeedApplyTo
            (mapsTo "a" tInt)
            (_a `tArr` _a)
            (tInt `tArr` tInt)

        succeedApplyTo
            (mapsTo "a" tInt)
            tInt
            tInt

    describe "Compose and apply to" $ do

        succeedComposeAndApplyTo
            (fromList [ ("a", tInt) ])
            (fromList [ ("b", tBool) ])
            _a
            tInt

        succeedComposeAndApplyTo
            (fromList [ ("a", tInt) ])
            (fromList [ ("b", tBool) ])
            _b
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            _a
            tInt

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            _b
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            (_a `tArr` _b)
            (tInt `tArr` tBool)

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tVar kTyp "b") ])
            _a
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tVar kTyp "b") ])
            _b
            tBool

        succeedComposeAndApplyTo
            (compose (fromList [ ("a3", tVar kTyp "a4") ]) (fromList [ ("a2", tVar kTyp "a3") ]))
            (fromList [ ("a1", tVar kTyp "a2") ])
            (tVar kTyp "a1")
            (tVar kTyp "a4")

-------------------------------------------------------------------------------

-- Type tests

succeedMatchTypeVars :: Type -> [(Name, Kind)] -> SpecWith ()
succeedMatchTypeVars ty vars =
    describe ("The free type variables in " <> "TODO") $ -- prettyPrint ty) $
        it ("✔ are [" <> "TODO") -- Text.intercalate ", " (renderDoc . prettyTypePair <$> vars) <> "]")
            (typeVars ty == vars)
--  where
--    prettyTypePair (n, k) = pretty n <+> ":" <+> pretty k

testTypeVars :: SpecWith ()
testTypeVars = do

    succeedMatchTypeVars
        _a
        [("a", kTyp)]

    succeedMatchTypeVars
        (_a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedMatchTypeVars
        (tList _a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedMatchTypeVars
        tInt
        []

    succeedMatchTypeVars
        (tApp kTyp (tVar kFun "m") _a)
        [("m", kFun), ("a", kTyp)]

testKindOf :: SpecWith ()
testKindOf = do

    describe "The kind of Bool" $ do
        it "✔ is *"
            (kindOf tBool == kTyp)

    describe "The kind of (Int -> Int)" $ do
        it "✔ is *"
            (kindOf (tInt `tArr` tInt) == kTyp)

    describe "The kind of (List a)" $ do
        it "✔ is *"
            (kindOf (tList _a) == kTyp)

    describe "The kind of (List Int)" $ do
        it "✔ is *"
            (kindOf (tList tInt) == kTyp)

    describe "The kind of List" $ do
        it "✔ is * -> *"
            (kindOf tListCon == kFun)

testToPolytype :: SpecWith ()
testToPolytype = do

    describe "Upgrading a type variable" $ do
        it "✔ returns the same type"
            (toPolytype _a == (tVar kTyp "a" :: Polytype))

    describe "Upgrading a type constructor" $ do
        it "✔ returns the same type"
            (toPolytype tInt == (tInt :: Polytype))

testTupleCon :: SpecWith ()
testTupleCon = do

    describe "The pair constructor" $ do
        it "✔ is (,)"
            (tupleCon 2 == "(,)")

    describe "The 3-tuple constructor" $ do
        it "✔ is (,,)"
            (tupleCon 3 == "(,,)")

    describe "The 4-tuple constructor" $ do
        it "✔ is (,,,)"
            (tupleCon 4 == "(,,,)")

-------------------------------------------------------------------------------

-- Type inference tests

