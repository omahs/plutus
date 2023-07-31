-- editorconfig-checker-disable-fil
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DuplicateRecordFields    #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE ImplicitParams           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE NamedFieldPuns           #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData               #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnboxedTuples            #-}
{-# LANGUAGE UndecidableInstances     #-}

{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-uniques -dsuppress-coercions -dsuppress-type-applications -dsuppress-unfoldings -dsuppress-idinfo -dppr-cols=200 -dumpdir /tmp/dumps #-}

module UntypedPlutusCore.Evaluation.Machine.Bytecode.Internal where

import PlutusCore.Builtin hiding (Emitter)
import PlutusCore.DeBruijn qualified as PLC
import Universe
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Bytecode.Stack

import Data.RandomAccessList.Class qualified as Env
import Data.RandomAccessList.SkewBinary qualified as Env

import Data.Vector qualified as V
import Data.Word (Word64)

import Control.DeepSeq (NFData)
import Control.Exception (catch)
import Control.Monad.Catch (throwM)
import Control.Monad.Except (MonadError (..), unless, when)
import Control.Monad.Primitive (PrimMonad)
import Control.Monad.ST
import Control.Monad.ST.Unsafe (unsafeIOToST, unsafeSTToIO)
import Data.Coerce
import Data.DList qualified as DList
import Data.Foldable (for_)
import Data.Kind qualified as GHC
import Data.Primitive
import Data.SatInt
import Data.STRef
import Data.Text (Text)
import Debug.Trace
import GHC.Generics (Generic)
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty
import Prettyprinter
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts (..))

---
--- Instructions
---

{- Note [Instruction sequences as Vectors]
We represent sequences of instructions as Vectors. This has a few desirable properties:
1. Vectors unpack well, and functions on Vectors usually optimize well
2. Slices of Vectors just appear as another independent Vector, so this is compatible with
all the Vectors being slices of one original byte array
3. We don't have to worry about indices
-}

-- TODO: this seems to be leading to some boxing in pushReturnFrame
-- which doesn't happen if it's a bare int. Unclear why, but fixing
-- it didn't seem to affect performance much, so leaving for now.
newtype CodePointer = CodePointer { unCodePointer :: Int }
  deriving newtype (Show, NFData)
newtype CodePointerOffset = CodePointerOffset Int
  deriving newtype (Show, NFData)

bumpCodePointer :: CodePointer -> CodePointer
bumpCodePointer (CodePointer ptr) = CodePointer $ ptr + 1

offsetCodePointer :: CodePointer -> CodePointerOffset -> CodePointer
offsetCodePointer (CodePointer ptr) (CodePointerOffset offset) = CodePointer $ ptr + offset

data Instruction uni fun =
  Lookup { index :: {-# UNPACK #-} Word64 }
  | Closure { next :: {-# UNPACK #-} CodePointerOffset }
  | Constant { con :: Some (ValueOf uni) }
  | Builtin { fun :: fun }
  | ApplyLTR
  | TailApplyLTR
  | ApplyRTL
  | TailApplyRTL
  | Return
  | Error
  | Spend ExBudget
  | Delay { next :: {-# UNPACK #-} CodePointerOffset }
  | Force
  | TailForce
  | Constr { next :: {-# UNPACK #-} CodePointerOffset, arity :: {-# UNPACK #-} Word64, tag :: {-# UNPACK #-} Word64 }
  | Case { next :: CodePointerOffset, branchOffsets :: {-# UNPACK #-} V.Vector CodePointerOffset }
  deriving stock (Generic)
  deriving anyclass (NFData)

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Closed uni)
    => Show (Instruction uni fun)

instance (GShow uni, Everywhere uni Show, Show fun, Closed uni) => PrettyBy PrettyConfigPlc (Instruction uni fun) where
  prettyBy _ i = pretty (show i)

type Instructions uni fun = V.Vector (Instruction uni fun)

instance (PrettyBy PrettyConfigPlc a) => PrettyBy PrettyConfigPlc (V.Vector a) where
  prettyBy config vs = prettyBy config (V.toList vs)

nextInstrOffset :: Instruction uni fun -> CodePointerOffset
nextInstrOffset = \case
  Closure next    -> next
  Delay next      -> next
  Constr next _ _ -> next
  Case next _     -> next
  _               -> CodePointerOffset 1

-- costs obviously weird here
termToInstrs :: Bool -> Bool -> CekMachineCosts -> UPLC.Term PLC.DeBruijn uni fun ann -> Instructions uni fun
termToInstrs insertCostingInstrs insertTailCalls (CekMachineCosts{..}) term = V.singleton (Spend cekStartupCost) <> go term
  where
    go = \case
      UPLC.Var _ (PLC.DeBruijn (PLC.Index n)) -> spend cekVarCost <> V.singleton (Lookup n)
      UPLC.LamAbs _ _ t ->
        let rest = goTail t
        in spend cekLamCost <> V.singleton (Closure $ CodePointerOffset $ 1 + V.length rest) <> rest
      UPLC.Apply _ l r -> spend cekApplyCost <> go l <> go r <> V.singleton ApplyLTR
      UPLC.Force _ t -> spend cekForceCost <> go t <> V.singleton Force
      UPLC.Delay _ t ->
        let rest = goTail t
        in spend cekDelayCost <> V.singleton (Delay $ CodePointerOffset $ 1 + V.length rest) <> rest
      UPLC.Builtin _ f -> spend cekBuiltinCost <> V.singleton (Builtin f)
      UPLC.Constant _ t -> spend cekConstCost <> V.singleton (Constant t)
      UPLC.Error _ -> V.singleton Error
      UPLC.Constr _ t args ->
        let arity = length args
            code = (V.replicate arity ApplyRTL <> V.singleton Return)
        in spend cekConstrCost <> foldMap go args <> V.singleton (Constr (CodePointerOffset $ 1 + V.length code) (fromIntegral arity) t) <> code
      UPLC.Case _ scrut branches ->
        let branchCodes = fmap goTail branches
            branchLengths = fmap V.length branchCodes
            -- This is fine because scanl produces a non-empty list
            Just (offsets, next) = V.unsnoc $ V.fromList $ fmap CodePointerOffset $ scanl (\offset len -> offset + len) 1 branchLengths
        in spend cekCaseCost <> go scrut <> V.singleton (Case next offsets) <> V.concat branchCodes
    -- 'go', when we know the next thing should be a 'Return'
    goTail = \case
      UPLC.Apply _ l r | insertTailCalls -> spend cekApplyCost <> go l <> go r <> V.singleton TailApplyLTR
      UPLC.Force _ t | insertTailCalls   -> spend cekForceCost <> go t <> V.singleton TailForce
      i                         -> go i <> V.singleton Return
    spend cost | insertCostingInstrs = V.singleton (Spend cost)
               | otherwise = mempty

---
--- Values
---

data Value uni fun =
    -- This bang gave us a 1-2% speed-up at the time of writing.
    VCon (Some (ValueOf uni))
  | VDelay { codePointer :: {-# UNPACK #-} CodePointer, env :: Env uni fun }
  | VClosure { codePointer :: {-# UNPACK #-} CodePointer, env :: Env uni fun }
    -- | A partial builtin application, accumulating arguments for eventual full application.
    -- We don't need a 'CekValEnv' here unlike in the other constructors, because 'VBuiltin'
    -- values always store their corresponding 'Term's fully discharged, see the comments at
    -- the call sites (search for 'VBuiltin').
  | VBuiltin { function :: fun, runtime :: BuiltinRuntime (Value uni fun) }
      -- ^ The partial application and its costing function.
      -- Check the docs of 'BuiltinRuntime' for details.
    -- | A constructor value, including fully computed arguments and the tag.
  | VConstr { codePointer :: {-# UNPACK #-} CodePointer, tag :: {-# UNPACK #-} Word64, args :: {-# UNPACK #-} V.Vector (Value uni fun) }

instance Show (BuiltinRuntime (Value uni fun)) where
    show _ = "<builtin_runtime>"

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Closed uni)
    => Show (Value uni fun)

instance (GShow uni, Everywhere uni Show, Show fun, Closed uni) => PrettyBy PrettyConfigPlc (Value uni fun) where
    prettyBy _ v = pretty $ show v

type instance UPLC.UniOf (Value uni fun) = uni

instance HasConstant (Value uni fun ) where
    asConstant (VCon val) = pure val
    asConstant _          = throwNotAConstant

    fromConstant = VCon

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Value uni fun) where
    memoryUsage = \case
        VCon c      -> memoryUsage c
        VDelay {}   -> singletonRose 1
        VClosure {} -> singletonRose 1
        VBuiltin {} -> singletonRose 1
        VConstr {}  -> singletonRose 1
    {-# INLINE memoryUsage #-}

---
--- Machine monad types
---

data BCUserError =
    BCEvaluationFailure -- ^ Error has been called or a builtin application has failed
    | BCOutOfExError ExRestrictingBudget
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Pretty BCUserError where
  pretty BCEvaluationFailure = "EvaluationFailure"

instance AsEvaluationFailure BCUserError where
    _EvaluationFailure = _EvaluationFailureVia BCEvaluationFailure

type BCM :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type -> GHC.Type -> GHC.Type
-- | The monad the CEK machine runs in.
newtype BCM uni fun s a = BCM
    { unBCM :: ST s a
    } deriving newtype (Functor, Applicative, Monad, PrimMonad)

-- | The CEK machine-specific 'EvaluationException'.
type BCEvaluationException uni fun =
    EvaluationException BCUserError (MachineError fun) (Instructions uni fun)

instance (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun) => MonadError (BCEvaluationException uni fun) (BCM uni fun s) where
    -- See Note [Throwing exceptions in ST].
    throwError = BCM . throwM
    a `catchError` h = BCM . unsafeIOToST $ aIO `catch` hIO where
        aIO = unsafeRunCekM a
        hIO = unsafeRunCekM . h

        -- | Unsafely run a 'BCM' computation in the 'IO' monad by converting the
        -- underlying 'ST' to it.
        unsafeRunCekM :: BCM uni fun s a -> IO a
        unsafeRunCekM = unsafeSTToIO . unBCM

---
--- Budget
---

newtype BudgetSpender uni fun s = BudgetSpender
    { unBudgetSpender :: ExBudget -> BCM uni fun s ()
    }

-- General enough to be able to handle a spender having one, two or any number of 'STRef's
-- under the hood.
-- | Runtime budgeting info.
data ExBudgetInfo cost uni fun s = ExBudgetInfo
    { _exBudgetModeSpender       :: !(BudgetSpender uni fun s)  -- ^ A spending function.
    , _exBudgetModeGetFinal      :: !(ST s cost) -- ^ For accessing the final state.
    , _exBudgetModeGetCumulative :: !(ST s ExBudget) -- ^ For accessing the cumulative budget.
    }

-- We make a separate data type here just to save the caller from those pesky
-- 'ST'-related details.
-- | A budgeting mode to execute the CEK machine in.
newtype ExBudgetMode cost uni fun = ExBudgetMode
    { unExBudgetMode :: forall s. ST s (ExBudgetInfo cost uni fun s)
    }

---
--- Emitter
---

-- | The CEK machine is parameterized over an emitter function, similar to 'CekBudgetSpender'.
type Emitter uni fun s = DList.DList Text -> BCM uni fun s ()

-- | Runtime emitter info, similar to 'ExBudgetInfo'.
data EmitterInfo uni fun s = EmitterInfo {
    _emitterInfoEmit       :: !(Emitter uni fun s)
    , _emitterInfoGetFinal :: !(ST s [Text])
    }

-- | An emitting mode to execute the CEK machine in, similar to 'ExBudgetMode'.
newtype EmitterMode uni fun = EmitterMode
    { unEmitterMode :: forall s. ST s ExBudget -> ST s (EmitterInfo uni fun s)
    }

---
--- Implicits
---

-- | Implicit parameter for the log emitter reference.
type GivenEmitter uni fun s = (?emitter :: Emitter uni fun s)
-- | Implicit parameter for the builtin runtime.
type GivenRuntime uni fun = (?runtime :: (BuiltinsRuntime fun (Value uni fun)))
-- | Implicit parameter for budget spender.
type GivenSpender uni fun s = (?budgetSpender :: (BudgetSpender uni fun s))

---
--- Environments, frames and stacks
---

type Env uni fun = Env.RAList (Value uni fun)
data Frame uni fun = Frame {-# UNPACK #-} !CodePointer !(Env uni fun)
  deriving stock (Show)

-- Some very crap stacks
type ValueStack s uni fun = MStack s (Value uni fun)
type ControlStack s uni fun = MStack s (Frame uni fun)

-- | A 'MonadError' version of 'try'.
--
-- TODO: remove when we switch to mtl>=2.3
tryError :: MonadError e m => m a -> m (Either e a)
tryError a = (Right <$> a) `catchError` (pure . Left)

---
--- The machine
---

runBC
  :: (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun)
  => BuiltinsRuntime fun (Value uni fun)
  -> ExBudgetMode cost uni fun
  -> EmitterMode uni fun
  -> Instructions uni fun
  -> (Either (BCEvaluationException uni fun) (Value uni fun), cost, [Text])
runBC runtime (ExBudgetMode getExBudgetInfo) (EmitterMode getEmitterMode) code = runST $ unBCM $ do
  ExBudgetInfo{_exBudgetModeSpender, _exBudgetModeGetFinal, _exBudgetModeGetCumulative} <- BCM getExBudgetInfo
  EmitterInfo{_emitterInfoEmit, _emitterInfoGetFinal} <- BCM $ getEmitterMode _exBudgetModeGetCumulative
  let
    ?emitter = _emitterInfoEmit
    ?runtime = runtime
    ?budgetSpender = _exBudgetModeSpender

  vs <- BCM $ newStack 100
  cs <- BCM $ newStack 100
  let env = Env.empty

  errorOrRes <- tryError (runMachine vs cs code env)
  st <- BCM _exBudgetModeGetFinal
  logs <- BCM _emitterInfoGetFinal
  pure (errorOrRes, st, logs)

runMachine
  :: forall uni fun s
  . (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun
  , GivenEmitter uni fun s, GivenRuntime uni fun, GivenSpender uni fun s)
  => ValueStack s uni fun
  -> ControlStack s uni fun
  -> Instructions uni fun
  -> Env uni fun
  -> BCM uni fun s (Value uni fun)
runMachine !vs !cs !instrs !env = enter env (CodePointer 0)
  where
    enter :: Env uni fun -> CodePointer -> BCM uni fun s (Value uni fun)
    enter !env !codePtr = do
      --traceEnter
      go codePtr
      where
        {-# NOINLINE traceEnter #-}
        traceEnter :: BCM uni fun s ()
        traceEnter = do
          traceM "Entering:"
          traceM $ "  Code: " ++ show instrs
          vss <- showMStack vs
          traceM $ "  Value stack: " ++ vss
          css <- showMStack cs
          traceM $ "  Control stack: " ++ css
          traceM $ "  Env: " ++ show env
        {-# NOINLINE traceInstr #-}
        traceInstr :: Instruction uni fun -> Instructions uni fun -> BCM uni fun s ()
        traceInstr instr rest = do
          traceM $ show instr ++ " in state:"
          traceM $ "  Subsequent code: " ++ show rest
          vss <- showMStack vs
          traceM $ "  Value stack: " ++ vss
          css <- showMStack cs
          traceM $ "  Control stack: " ++ css
          traceM $ "  Env: " ++ show env
        pushReturnFrame !rest = BCM $ pushStack (Frame rest env) cs
        pushValue !v = BCM $ pushStack v vs
        popValue = BCM $ popStack vs
        go :: CodePointer -> BCM uni fun s (Value uni fun)
        go !codePtr =
          case instrs V.!? unCodePointer codePtr of
            -- Terminate
            Nothing -> popValue
            Just instr -> do
              --traceInstr instr rest
              let nextOffset = nextInstrOffset instr
                  nextPtr = offsetCodePointer codePtr nextOffset
                  continue = go nextPtr
              case instr of
                Lookup{index} -> do
                  case Env.indexOne env index of
                    Just v  -> do
                      pushValue v
                      continue
                    Nothing -> throwingWithCause _MachineError OpenTermEvaluatedMachineError Nothing
                Closure{} -> do
                  pushValue (VClosure (bumpCodePointer codePtr) env)
                  continue
                Constant{con} -> do
                  pushValue (VCon con)
                  continue
                Builtin{fun} -> do
                  let meaning = lookupBuiltin fun ?runtime
                  pushValue (VBuiltin fun meaning)
                  continue
                ApplyLTR -> do
                  v <- popValue
                  f <- popValue
                  pushReturnFrame nextPtr
                  applyEvaluate f v
                TailApplyLTR -> do
                  v <- popValue
                  f <- popValue
                  applyEvaluate f v
                ApplyRTL -> do
                  f <- popValue
                  v <- popValue
                  pushReturnFrame nextPtr
                  applyEvaluate f v
                TailApplyRTL -> do
                  f <- popValue
                  v <- popValue
                  applyEvaluate f v
                Return -> doReturn
                Error -> throwing_ _EvaluationFailure
                Spend budget -> do
                  spendBudgetBCM budget
                  continue
                Delay{} -> do
                  pushValue (VDelay (bumpCodePointer codePtr) env)
                  continue
                Force -> do
                  v <- popValue
                  pushReturnFrame nextPtr
                  forceEvaluate v
                TailForce -> do
                  v <- popValue
                  forceEvaluate v
                Constr{arity, tag} -> do
                  -- in reverse order
                  args <- V.replicateM (fromIntegral arity) popValue
                  pushValue (VConstr (bumpCodePointer codePtr) tag args)
                  continue
                Case{branchOffsets} -> do
                  v <- popValue
                  case v of
                    VConstr ctorCode tag args -> case branchOffsets V.!? fromIntegral tag of
                      Just branchOffset -> do
                        -- reverses again, getting them in the right order
                        for_ args pushValue
                        -- When we are completely done, we want to return into
                        -- the next instruction
                        pushReturnFrame nextPtr
                        -- We push a return frame for the constructor entry code to jump to
                        -- after we've computed the branch.
                        pushReturnFrame ctorCode
                        -- Enter the branch.
                        enter env (offsetCodePointer codePtr branchOffset)
                      Nothing -> throwingWithCause _MachineError (MissingCaseBranch tag) Nothing
                    _ -> throwingWithCause _MachineError NonConstrScrutinized Nothing

        doReturn = do
          Frame codePtr' env' <- BCM $ popStack cs
          enter env' codePtr'

        applyEvaluate (VClosure code' env') v = enter (Env.cons v env') code'
        applyEvaluate (VBuiltin fun runtime) v =
          case runtime of
              -- It's only possible to apply a builtin application if the builtin expects a term
              -- argument next.
              BuiltinExpectArgument f -> do
                  res <- evalBuiltinApp fun $ f v
                  pushValue res
                  -- Bulitins must transfer control back by returning, cannot just
                  -- continue. Otherwise tail calls can't work (won't jump up to
                  -- parent return)
                  -- TODO: note + tests to show this
                  doReturn
              _ -> throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError Nothing
        applyEvaluate _ _ = throwingWithCause _MachineError NonFunctionalApplicationMachineError Nothing
        {-# INLINE applyEvaluate #-}

        forceEvaluate (VDelay code' env') = enter env' code'
        forceEvaluate (VBuiltin fun runtime) =
          case runtime of
              -- It's only possible to apply a builtin application if the builtin expects a term
              -- argument next.
              BuiltinExpectForce runtime' -> do
                  -- We allow a type argument to appear last in the type of a built-in function,
                  -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
                  -- application.
                  res <- evalBuiltinApp fun runtime'
                  pushValue res
                  doReturn
              _ -> throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError Nothing
        forceEvaluate _ = throwingWithCause _MachineError NonPolymorphicInstantiationMachineError Nothing
        {-# INLINE forceEvaluate #-}

spendBudgetBCM :: (GivenSpender uni fun s) => ExBudget -> BCM uni fun s ()
spendBudgetBCM = unBudgetSpender ?budgetSpender
{-# INLINE spendBudgetBCM #-}

-- | Spend each budget from the given stream of budgets.
spendBudgetStreamBCM
    :: GivenSpender uni fun s
    => ExBudgetStream
    -> BCM uni fun s ()
spendBudgetStreamBCM = go where
    go (ExBudgetLast budget)         = spendBudgetBCM budget
    go (ExBudgetCons budget budgets) = spendBudgetBCM budget *> go budgets
{-# INLINE spendBudgetStreamBCM #-}

-- hacked up copy of the one in the CEK machine
evalBuiltinApp
    :: (Everywhere uni Show, GShow uni, Show fun, ThrowableBuiltins uni fun
       , GivenEmitter uni fun s, GivenSpender uni fun s)
    => fun
    -> BuiltinRuntime (Value uni fun)
    -> BCM uni fun s (Value uni fun)
evalBuiltinApp fun runtime = case runtime of
    BuiltinResult budgets getX -> do
        spendBudgetStreamBCM budgets
        case getX of
            MakeKnownFailure logs err       -> do
                ?emitter logs
                throwKnownTypeError err
            MakeKnownSuccess x              -> pure x
            MakeKnownSuccessWithLogs logs x -> ?emitter logs >> pure x
    _ -> pure $ VBuiltin fun runtime
{-# INLINE evalBuiltinApp #-}

-- Copied from CEK machine, surely can share?

newtype RestrictingSt = RestrictingSt ExRestrictingBudget
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid, NFData)
    deriving anyclass (PrettyBy config)

instance Pretty RestrictingSt where
    pretty (RestrictingSt budget) = parens $ "final budget:" <+> pretty budget <> line

-- | For execution, to avoid overruns.
restricting
    :: (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun)
    => ExRestrictingBudget -> ExBudgetMode RestrictingSt uni fun
restricting (ExRestrictingBudget initB@(ExBudget cpuInit memInit)) = ExBudgetMode $ do
    -- We keep the counters in a PrimArray. This is better than an STRef since it stores its contents unboxed.
    --
    -- If we don't specify the element type then GHC has difficulty inferring it, but it's
    -- annoying to specify the monad, since it refers to the 's' which is not in scope.
    ref <- newPrimArray @_ @SatInt 2
    let
        cpuIx = 0
        memIx = 1
        readCpu = coerce @_ @ExCPU <$> readPrimArray ref cpuIx
        writeCpu cpu = writePrimArray ref cpuIx $ coerce cpu
        readMem = coerce @_ @ExMemory <$> readPrimArray ref memIx
        writeMem mem = writePrimArray ref memIx $ coerce mem

    writeCpu cpuInit
    writeMem memInit
    let
        spend (ExBudget cpuToSpend memToSpend) = do
            cpuLeft <- BCM readCpu
            memLeft <- BCM readMem
            let cpuLeft' = cpuLeft - cpuToSpend
            let memLeft' = memLeft - memToSpend
            -- Note that even if we throw an out-of-budget error, we still need to record
            -- what the final state was.
            BCM $ writeCpu cpuLeft'
            BCM $ writeMem memLeft'
            when (cpuLeft' < 0 || memLeft' < 0) $ do
                let budgetLeft = ExBudget cpuLeft' memLeft'
                throwingWithCause _EvaluationError
                    (UserEvaluationError . BCOutOfExError $ ExRestrictingBudget budgetLeft)
                    Nothing
        spender = BudgetSpender spend
        remaining = ExBudget <$> readCpu <*> readMem
        cumulative = do
            r <- remaining
            pure $ initB `minusExBudget` r
        final = RestrictingSt . ExRestrictingBudget <$> remaining
    pure $ ExBudgetInfo spender final cumulative

-- | 'restricting' instantiated at 'enormousBudget'.
restrictingEnormous :: (GShow uni, Everywhere uni Show, Show fun, ThrowableBuiltins uni fun) => ExBudgetMode RestrictingSt uni fun
restrictingEnormous = restricting enormousBudget

-- | No emitter.
noEmitter :: EmitterMode uni fun
noEmitter = EmitterMode $ \_ -> pure $ EmitterInfo (\_ -> pure ()) (pure mempty)

-- | Emits log only.
logEmitter :: EmitterMode uni fun
logEmitter = EmitterMode $ \_ -> do
    logsRef <- newSTRef DList.empty
    let emitter logs = BCM $ modifySTRef logsRef (`DList.append` logs)
    pure $ EmitterInfo emitter (DList.toList <$> readSTRef logsRef)
