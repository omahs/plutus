module Main (main) where

import PlutusConformance.Common
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Bytecode qualified as B

failingTests :: [FilePath]
failingTests = []

evalBC :: UplcEvaluator
evalBC = BinaryEvaluator $ \(UPLC.Program _ _ t) -> do
    case UPLC.deBruijnTerm t of
        Left (_ :: UPLC.FreeVariableError) -> False
        Right t' ->
          let dbt = UPLC.termMapNames unNameDeBruijn t'
          in case B.evaluateBCTerm B.defaultBCParameters B.restrictingEnormous B.noEmitter dbt of
              (Left _, _, _)  -> False
              (Right _, _, _) -> True

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalBC (\dir -> elem dir failingTests)
