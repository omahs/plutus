-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | For testing the checks that happen during phase-1
module Spec.Phase1 (tests) where

import PlutusPrelude
import PlutusCore as PLC
import PlutusCore.MkPlc as PLC
import PlutusCore.Version as PLC
import UntypedPlutusCore as UPLC
import PlutusLedgerApi.Common as Common
import PlutusLedgerApi.Common.Versions

import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as BSS
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Data.Map qualified as Map
import Data.Set qualified as Set
import Text.Printf

tests :: TestTree
tests = testGroup "versions"
    [ testRmdr12
    , testRmdr3
    , testBuiltinVersions
    ]

testRmdr12 :: TestTree
testRmdr12 = testGroup "rmdr12" $ concat $
  [[ testCase (printf "unit-%s-%s" (pretty lv) (pretty pv)) $
      assertBool "remdr unit did not pass" $ isRight $ Common.assertScriptWellFormed lv pv $ errorScript <> "remdr1"
   , testProperty (printf "prop-%s-%s" (pretty lv) $ pretty pv) $
       \remdr -> isRight $ Common.assertScriptWellFormed lv pv $ errorScript <> BSS.pack remdr
   ]
  | lv <- [PlutusV1,PlutusV2]
  , pv <- knownPVsForLang lv
  ]

testRmdr3 :: TestTree
testRmdr3 = testGroup "rmdr3" $
    [ testCase (printf "unit-%s-%s" (pretty lv) ( pretty pv)) $
                          (Left $ RemainderError "remdr3") @=? Common.assertScriptWellFormed lv pv (errorScript <> "remdr3")
                    -- we cannot make a property test because it may generate valid bytestring append extensions to the original script
                    -- a more sophisticated one could work though
    | lv <- [PlutusV3 ..] -- and for future versions
    , pv <- knownPVsForLang lv
    ]

testBuiltinVersions :: TestTree
testBuiltinVersions = testGroup "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems builtinsIntroducedIn
                allBuiltins = enumerate @DefaultFun
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before Plutus introduction, aka PlutusV1" $
        let pVsBeforePlutus = Set.takeWhileAntitone (< ledgerLanguageIntroducedIn PlutusV1) knownPVs
        in for_ pVsBeforePlutus $ \pv->
            assertBool "builtins are available" $ Set.null $ builtinsAvailableIn PlutusV1 pv

    , testCase "serializeData is available in PlutusV2 and after" $
        let (lsBefore, lsAfter) = span (<PlutusV2) $ enumerate @PlutusLedgerLanguage
            check l p  = Common.assertScriptWellFormed l p serialiseDataExScript
        in do
            for_ lsBefore $ \lv ->
                for_ knownPVs $ assertBool "serialiseData is not excluded" . isLeft . check lv
            for_ lsAfter $ \lv ->
                let (woPvs, wPvs) = Set.spanAntitone (< ledgerLanguageIntroducedIn lv) knownPVs
                in do
                    for_ woPvs $ assertBool "serialiseData is not excluded" . isLeft . check lv
                    for_ wPvs $ assertBool "serialiseData is not included" . isRight . check lv

    , testCase "bls,keccak256,blake2b224 only available in PlutusV3 and after" $
        let (lsBefore, lsAfter) = span (<PlutusV3) $ enumerate @PlutusLedgerLanguage
        in for_ [blsExScript, keccak256ExScript, blake2b224ExScript] $ \script -> do
            for_ lsBefore $ \lv ->
                for_ knownPVs $ \pv -> assertBool "serialiseData is not excluded" $ isLeft $ Common.assertScriptWellFormed lv pv script
            for_ lsAfter $ \lv ->
                let (woPvs, wPvs) = Set.spanAntitone (< ledgerLanguageIntroducedIn lv) knownPVs
                in do
                    for_ woPvs $ \pv -> assertBool "serialiseData is not excluded" $ isLeft $ Common.assertScriptWellFormed lv pv script
                    for_ wPvs $ \pv -> assertBool "serialiseData is not included" $ isRight $ Common.assertScriptWellFormed lv pv script

    ]

-- * Helpers

instance Arbitrary ProtocolVersion where
    arbitrary = ProtocolVersion <$> arbitrary <*> arbitrary



knownPVsForLang :: PlutusLedgerLanguage -> [ProtocolVersion]
knownPVsForLang lv = toList $ Set.dropWhileAntitone (< ledgerLanguageIntroducedIn lv) knownPVs


serialiseDataExScript :: SerialisedScript
serialiseDataExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()


-- Note that bls can work also with plcversion==1.0.0
blsExScript :: SerialisedScript
blsExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
     builtin () Bls12_381_G1_uncompress @@ [mkConstant () $ BS.pack (0xc0 : replicate 47 0x00)]

-- Note that keccak can work also with plcversion==1.0.0
keccak256ExScript :: SerialisedScript
keccak256ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () Keccak_256 @@ [mkConstant @BS.ByteString () "hashme"]

-- Note that blake2b224 can work also with plcversion==1.0.0
blake2b224ExScript :: SerialisedScript
blake2b224ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () Blake2b_224 @@ [mkConstant @BS.ByteString () "hashme"]
