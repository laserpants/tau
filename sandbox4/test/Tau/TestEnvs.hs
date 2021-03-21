{-# LANGUAGE OverloadedStrings #-}
module Tau.TestEnvs where

import Data.Maybe (fromJust)
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util.Env (Env(..))
import qualified Data.Map.Strict as Map
import qualified Tau.Util.Env as Env

-- TODO
testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ["Some", "None"])
    , ("None"     , ["Some", "None"])
    , ("[]"       , ["[]", "(::)"])
    , ("(::)"     , ["[]", "(::)"])
    , ("(,)"      , ["(,)"])
    ]

testExprEnv = Env.fromList
    [ ("first"   , cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "a")]))
    , ("second"  , cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "b")]))
    ]

testValueEnv = Env.map (fromJust . (`evalExpr` mempty)) testExprEnv
--    Env (Map.foldrWithKey (\k v e -> Map.insert k (fromJust (evalExpr v e)) e) mempty m)
--  where
--    Env m = testExprEnv


--testValueEnv = Env.fromList
----    [ ("(,)"     , constructor "(,)" 2)  
----    , ("[]"      , constructor "[]" 0)  
----    , ("(::)"    , constructor "(::)" 2)  
--    [ ("first"   , fromJust (evalExpr first_ mempty))
--    , ("second"  , fromJust (evalExpr second_ mempty))
--    ]
--  where
--    first_  = cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "a")])
--    second_ = cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "b")])

--testClassEnv :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f)
testClassEnv :: ClassEnv 
testClassEnv = Env.fromList
    [ ( "Num"
      , ( ( []
          , InClass "Num" "a"
          , [ ("(+)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a")
            , ("(*)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a")
            , ("(-)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a") 
            ]
          )
          -- Instances
        , [ ( []
            , InClass "Num" tInt
            , [ ("(+)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)")
              , ("(*)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)")
              , ("(-)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)")
              ]
            )
          ]
        )
      )
    , ( "Ord"
      , ( ( [ InClass "Eq" "a" ]
          , InClass "Ord" "a"
          , [ ("(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool)
            , ("(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool) 
            ]
          )
          -- Instances
        , [ ( []
            , InClass "Ord" tInt
            , [ ("(>)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)")
              , ("(<)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)")
              ]
            )
          ]
        )
      )
    ]

--    [ ( "Num"
--      , ( []
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) (fieldSet 
--            [ Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)")
--            , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)")
--            , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)")
--            ]))
--          ] 
--        )
--      )
--    , ( "Ord"
--      , ( ["Eq"]
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Ord") tInt) []) (fieldSet 
--            [ Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(>)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)")
--            , Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(<)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)")
--            ]))
--          ]
--        )
--      )
--    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "(==)"     , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )
    , ( "(+)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(-)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "add"      , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(,)"      , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1)))
    , ( "first"    , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 0))
    , ( "second"   , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` tGen 1))
    , ( "(::)"     , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"       , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "length"   , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
    , ( "None"     , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"     , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
    , ( "@Int.(+)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(-)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(*)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "const"    , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` tGen 0) )
    , ( "id"       , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    ]
