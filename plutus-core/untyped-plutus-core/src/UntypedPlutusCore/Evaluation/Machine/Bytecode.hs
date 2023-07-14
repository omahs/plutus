module UntypedPlutusCore.Evaluation.Machine.Bytecode
  ( evaluateBCTerm
  , runBC
  , termToInstrs
  , defaultBCCostModel
  , defaultBCParameters
  , restricting
  , restrictingEnormous
  , noEmitter
  , logEmitter)
where

import Data.Default.Class (def)
import Data.Text (Text)
import PlutusCore as PLC
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel,
                                                          defaultCekMachineCosts)
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Bytecode.Internal
import UntypedPlutusCore.Evaluation.Machine.Cek (CekMachineCosts, ThrowableBuiltins)

evaluateBCTerm
  :: (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun)
  => MachineParameters CekMachineCosts fun (Value uni fun)
  -> ExBudgetMode cost uni fun
  -> EmitterMode uni fun
  -> UPLC.Term PLC.DeBruijn uni fun ann
  -> (Either (BCEvaluationException uni fun) (Value uni fun), cost, [Text])
evaluateBCTerm (MachineParameters costs runtime) budget emitter t =
  runBC runtime budget emitter (termToInstrs True True costs t)

defaultBCCostModel :: CostModel CekMachineCosts BuiltinCostModel
defaultBCCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel

defaultBCParameters :: MachineParameters CekMachineCosts DefaultFun (Value DefaultUni DefaultFun)
defaultBCParameters = mkMachineParameters def defaultBCCostModel
