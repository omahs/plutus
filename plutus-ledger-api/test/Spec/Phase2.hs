-- For testing the checks that happen during phase-2
module Spec.Phase2 (tests) where


-- See Note [Checking the Plutus Core language version] for why these have to use mkTermToEvaluate
testLanguageVersions :: TestTree
testLanguageVersions = testGroup "Plutus Core language versions"
  [ testCase "v1.1.0 is available in l3,future and not before" $ do
      assertBool "in l3,Vasil" $ isLeft $ mkTermToEvaluate PlutusV3 vasilPV v110script []
      assertBool "in l2,future" $ isLeft $ mkTermToEvaluate PlutusV2 conwayPV v110script []
      assertBool "not in l3,future" $ isRight $ mkTermToEvaluate PlutusV3 conwayPV v110script []
  , testCase "constr is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ mkTermToEvaluate PlutusV3 conwayPV badConstrScript []
  , testCase "case is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ mkTermToEvaluate PlutusV3 conwayPV badCaseScript []
  ]


