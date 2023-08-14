-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{- |
Call site inlining machinery. We inline if the size of the inlined result is not larger.
See note [Inlining of fully applied functions].
-}
module PlutusIR.Transform.Inline.CallSiteInline where

import PlutusCore qualified as PLC
import PlutusCore.Rename (liftDupable)
import PlutusIR.Analysis.Size (termSize)
import PlutusIR.Contexts
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils
import PlutusIR.Transform.Substitute

import Control.Monad.State (gets)
import Debug.Trace
import PlutusCore.Pretty (display)
import Unsafe.Coerce (unsafeCoerce)

{- Note [Inlining and beta reduction of fully applied functions]

We inline if its cost and size are acceptable.

For size, we compare the sizes (in terms of AST nodes before and after the inlining and beta
reduction), and inline only if it does not increase the size. In the above example, we count
the number of AST nodes in `f a b` and in `a`. The latter is smaller, which means inlining
reduces the size.

We care about program size increases primarily because it
affects the size of the serialized script, which appears on chain and must be paid for.
This is different to many compilers which care about this also because e.g. larger ASTs
slow down compilation. We care about this too, but the serialized size is the main driver for us.

The number of AST nodes is an approximate rather than a precise measure. It correlates,
but doesn't directly map to the size of the serialised script. Different kinds of AST nodes
may take different number of bits to encode; in particular, a `Constant` node always
counts as one AST node, but the constant in it can be of arbitrary size. Then, would it be
better to use the size of the serialised term, instead of the number of AST nodes? Not
necessarily, because other transformations, such as CSE, may change the size further;
specifically, if a large constant occurs multiple times in a program, it may get CSE'd.

In general there's no reliable way to precisely predict the size impact of an inlining
decision, and we believe the number of AST nodes is in fact a good approximation.

For cost, we check whether the RHS (in this example, `\x. \y -> x`) has a small cost.
If the RHS has a non-zero arity, then the cost is always small (since a lambda or a type
abstraction is already a value). This may not be the case if the arity is zero.

For effect-safety, we require: (1) the RHS be pure, i.e., evaluating it is guaranteed to
not have side effects; (2) all arguments be pure, since otherwise it is unsafe to
perform beta reduction.
-}

{- | Apply the RHS of the given variable to the given arguments, and beta-reduce
the application, if possible.
-}
applyAndBetaReduce ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  -- | The rhs of the variable, should have been renamed already
  Term tyname name uni fun ann ->
  -- | The arguments, already processed
  AppContext tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
applyAndBetaReduce rhs args0 = do
  let go ::
        Term tyname name uni fun ann ->
        AppContext tyname name uni fun ann ->
        InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
      go acc args = case (acc, args) of
        (LamAbs _ann n _ty tm, appCtx@(TermAppContext arg _ args')) -> do
          usedOnce <- nameUsedAtMostOnce n
          isTermPure <- checkPurity arg
          isEffectSafe <- effectSafe acc Strict n isTermPure
          safe <- safeToBetaReduce n arg acc

          if safe -- we only do substitution if it is safe to beta reduce
            then do
              acc' <- do
                termSubstNamesM -- substitute the term param with the arg in the function body
                  -- rename before substitution to ensure global uniqueness
                  (\tmName -> if tmName == n then Just <$> PLC.rename arg else pure Nothing)
                  tm -- drop the beta reduced term lambda
              trace
                ( "LamAbs & TermAppContext, safe and substituted arg \n"
                  <> "name \n " <> display (unsafeCoerce n::Name) <> "\n"
                  <>" arg0 \n"
                  <> show (unsafeCoerce args0::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " arg \n"
                  <> display (unsafeCoerce arg::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " args' \n"
                  <> show (unsafeCoerce args'::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " args \n"
                  <> show (unsafeCoerce args::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " acc \n"
                  <> display (unsafeCoerce acc::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " tm \n" <> display (unsafeCoerce tm::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " rhs \n "
                  <> display (unsafeCoerce rhs::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n")
                (go acc' args')
            else pure . Just $ trace
                ( "LamAbs & TermAppContext, unsafe \n" <>
                  "name \n " <> display (unsafeCoerce n::Name)
                  <> " arg or rhs that is the input of safeToBetaReduce \n "
                  <> display (unsafeCoerce arg::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <>  "acc or body that is the input of safeToBetaReduce\n "
                  <> display (unsafeCoerce acc::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> "used at most once? \n " <> display usedOnce
                  <> "is arg pure \n" <> display isTermPure
                  <> "is effect safe \n " <> display isEffectSafe
                  <> " arg0 \n"
                  <> show (unsafeCoerce args0::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " args' \n"
                  <> show (unsafeCoerce args'::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " args \n"
                  <> show (unsafeCoerce args::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " acc \n"
                  <> display (unsafeCoerce acc::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " tm \n" <> display (unsafeCoerce tm::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " rhs \n "
                  <> display (unsafeCoerce rhs::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                )
                  (fillAppContext acc appCtx)
        (TyAbs _ann n _kd tm, TypeAppContext arg _ args') -> do
          acc' <-
            termSubstTyNamesM -- substitute the type param with the arg
              (\tyName -> if tyName == n then Just <$> PLC.rename arg else pure Nothing)
              tm -- drop the beta reduced type lambda
          trace
            (  "TyAbs & TypeAppContext, substituted \n" <> " arg0 \n"
              <> show (unsafeCoerce args0::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " args' \n"
              <> show (unsafeCoerce args'::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " args \n"
              <> show (unsafeCoerce args::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " acc \n"
              <> display (unsafeCoerce acc::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " tm \n" <> display (unsafeCoerce tm::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " rhs \n "
              <> display (unsafeCoerce rhs::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n")
            (go acc' args')
        -- term/type argument mismatch, don't inline
        (LamAbs{}, TypeAppContext{}) -> error "lamAbs, type"--pure Nothing
        (TyAbs{}, TermAppContext{}) -> error "tyabs term" --pure Nothing
        -- no more lambda abstraction, just return the processed application
        (_, appCtx) -> pure . Just $ trace
                ( "no more lambda abstraction \n"
                  <> " arg0 \n"
                  <> show (unsafeCoerce args0::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " appCtx \n"
                  <> show (unsafeCoerce appCtx::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " acc \n"
                  <> display (unsafeCoerce acc::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                  <> " rhs \n "
                  <> display (unsafeCoerce rhs::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
                )
                  (fillAppContext acc appCtx)

      -- Is it safe to turn `(\a -> body) arg` into `body [a := arg]`?
      -- The criteria is the same as the criteria for inlining `a` in
      -- `let !a = arg in body`.
      safeToBetaReduce ::
        -- `a`
        name ->
        -- `arg`
        Term tyname name uni fun ann ->
        -- the body `a` will be beta reduced in
        Term tyname name uni fun ann ->
        InlineM tyname name uni fun ann Bool
      safeToBetaReduce = shouldUnconditionallyInline Strict
  go rhs args0

-- | Consider whether to inline a term. For applications, consider whether to apply and beta reduce.
callSiteInline ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  -- | The term.
  Term tyname name uni fun ann ->
  -- | The head of term, obtained from `Contexts.splitApplication`.
  Term tyname name uni fun ann ->
  -- | The application context of the term, already processed.
  AppContext tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Term tyname name uni fun ann)
callSiteInline t = go
  where
    go var@(Var _ann name) args =
      gets (lookupVarInfo name) >>= \case
        Just varInfo -> do
          -- rename the rhs of the variable before any substitution
          rhs <-
            trace
            ( "Just varInfo case \n" <> -- display varInfo
              " tm " <> display (unsafeCoerce t::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " var " <> display (unsafeCoerce var::Term TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
              <> " args "
              <> show (unsafeCoerce args::AppContext TyName Name PLC.DefaultUni PLC.DefaultFun ()) <> "\n"
            )
            (liftDupable (let Done rhs = varRhs varInfo in rhs))
          applyAndBetaReduce rhs args >>= \case
            Just applied -> do
              let -- Inline only if the size is no bigger than not inlining.
                  sizeIsOk = termSize applied <= termSize t
                  -- The definition itself will be inlined, so we need to check that the cost
                  -- of that is acceptable. Note that we do _not_ check the cost of the _body_.
                  -- We would have paid that regardless.
                  -- Consider e.g. `let y = \x. f x`. We pay the cost of the `f x` at
                  -- every call site regardless. The work that is being duplicated is
                  -- the work for the lambda.
                  costIsOk = costIsAcceptable rhs
              -- check if binding is pure to avoid duplicated effects.
              -- For strict bindings we can't accidentally make any effects happen less often
              -- than it would have before, but we can make it happen more often.
              -- We could potentially do this safely in non-conservative mode.
              rhsPure <- isTermBindingPure (varStrictness varInfo) rhs
              pure $ if sizeIsOk && costIsOk && rhsPure then applied else t
            Nothing -> pure t
        -- The variable maybe a *recursive* let binding, in which case it won't be in the map,
        -- and we don't process it. ATM recursive bindings aren't inlined.
        Nothing -> pure t
    go _ _ = pure t
