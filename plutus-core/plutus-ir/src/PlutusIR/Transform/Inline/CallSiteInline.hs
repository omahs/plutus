{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
We inline fully applied functions if the cost and size are acceptable.
See note [Inlining of fully applied functions].
-}

module PlutusIR.Transform.Inline.CallSiteInline where

import PlutusIR.Analysis.Size
import PlutusIR.Contexts
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils
import PlutusIR.Transform.Substitute

import Control.Monad.Extra
import Control.Monad.State

{- Note [Inlining of fully applied functions]

We inline if (1) a function is fully applied (2) its cost and size are acceptable. We discuss
each in detail below.

(1) What do we mean by "fully applied"?

A function is fully applied when it has been applied to all arguments as indicated by its
"syntactic arity":

Consider `let v = rhs in body`, in which `body` calls `v`.

We focus on cases when `v` is a function. (Non-functions have arity () or 0).
I.e., it has type/term lambda abstraction(s). E.g.:

let v = \x1.\x2...\xn.VBody in body

(x1,x2...xn) or n is the syntactic arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.

In the `body`, where `v` is *called*,
if it was given the `n` term or type arguments in the correct order, then it is *fully applied*.
If `VBody` is acceptable in size and cost, we inline the call site of the fully applied `v` in this
case, i.e., we replace `v` in the `body` with `rhs`. E.g.

let f = \x.\y -> x
in
  let z = f q
  in f a b

becomes

let f = \x.\y -> x
in
  let z = f q
  in ((\x.\y -> x) a b)

With beta reduction, it becomes:

let f = \x.\y -> x
in
  let z = f q
  in a (more accurately it becomes (let { x = a, y = b } in x))

This is already a reduction in code size. However, because of this,
our dead code elimination pass is able to further reduce the code to just `a`.

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a substitution map like in `Inline`,
which substitute *all* occurrences of a variable. Instead, we store all in scope variables in a
map, `Utils.NonRecInScopeSet`, with all information needed for inlining saturated functions.

To find out whether a function is fully applied, when we encounter a variable in the `body`,
we find its arity from the `Utils.NonRecInScopeSet` map and compare it with the list
of arguments it has been applied to at that site. If it is fully applied, we inline it there.

Note that over-application of a function would also be inlined. E.g.:

```haskell
let id = \y -> y
     f = \x -> id
 in f x y
```

`f`'s arity is (\x) or 1, but is applied to 2 arguments. We inline `f` in this case if its cost and
size are acceptable.

(2) How do we decide whether cost and size are acceptable?

We currently reuse the heuristics 'Utils.sizeIsAcceptable' and 'Utils.costIsAcceptable'
that are used in unconditional inlining. For

let v = \x1.\x2...\xn.VBody in body

we check `VBody` with the above "acceptable" functions.
The "acceptable" functions are currently quite conservative, e.g.,
we currently reject `Constant` (has acceptable cost but not acceptable size).
We will work on more refined checks (e.g., checking their sizes instead of just rejecting them) to
improve the optimization.
-}

-- | Computes the 'Utils.Arity' of a term. Also returns the function body, for checking whether
-- it's `Utils.acceptable`.
computeArity ::
    Term tyname name uni fun ann
    -> (Arity tyname name uni ann, Term tyname name uni fun ann)
computeArity = \case
    LamAbs ann n ty body ->
      let (nextArgs, nextBody) = computeArity body in (TermParam ann n ty : nextArgs, nextBody)
    TyAbs ann n k body  ->
      let (nextArgs, nextBody) = computeArity body in (TypeParam ann n k : nextArgs, nextBody)
    -- Whenever we encounter a body that is not a lambda or type abstraction, we are done counting
    tm                -> ([],tm)

-- | Apply the RHS of the given variable to the given arguments, and beta-reduce
-- the application, if possible.
applyAndBetaReduce ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  -- | The variable
  VarInfo tyname name uni fun ann ->
  -- | The arguments
  AppContext tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
applyAndBetaReduce info = go (varBody info) (varArity info)
  where
    go ::
      Term tyname name uni fun ann ->
      Arity tyname name uni ann ->
      AppContext tyname name uni fun ann ->
      InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
    go acc arity args = case (arity, args) of
      -- fully applied
      ([], _) -> pure . Just $ mkApps acc args
      -- partially applied
      (_, AppContextEnd) -> pure . Just $ mkLams acc arity
      (TermParam _ param _ : arity', TermAppContext arg _ args') ->
        ifM
          (safeToSubst param arg)
          ( go
              (termSubstNames (\n -> if n == param then Just arg else Nothing) acc)
              arity'
              args'
          )
          (pure Nothing)
      (TypeParam _ param _ : arity', TypeAppContext arg _ args') ->
        go
          (termSubstTyNames (\n -> if n == param then Just arg else Nothing) acc)
          arity'
          args'
      _ -> pure Nothing

    -- Checks whether it is safe (i.e., preserves semantics) to perform beta reduction,
    -- namely, turning `(\a -> body) arg` into `body [a := arg]`.
    safeToSubst :: name -> Term tyname name uni fun ann -> InlineM tyname name uni fun ann Bool
    safeToSubst n = effectSafe (varBody info) Strict n <=< checkPurity

-- | Consider whether to inline an application.
inlineApp ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  -- | The `body` of the `Let` term.
  Term tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Term tyname name uni fun ann)
inlineApp t
  | (Var _ann name, args) <- splitApplication t =
      gets (lookupVarInfo name) >>= \case
        Just varInfo -> applyAndBetaReduce varInfo args >>= \case
          Just reduced -> do
            let def = varDef varInfo
                sizeIsOk = termSize reduced <= termSize t
                -- The definition itself will be inlined, so we need to check that the cost
                -- of that is acceptable. Note that we do _not_ check the cost of the _body_.
                -- We would have paid that regardless.
                -- Consider e.g. `let y = \x. f x`. We pay the cost of the `f x` at
                -- every call site regardless. The work that is being duplicated is
                -- the work for the lambda.
                defCostOk = costIsAcceptable def
            -- check if binding is pure to avoid duplicated effects.
            -- For strict bindings we can't accidentally make any effects happen less often
            -- than it would have before, but we can make it happen more often.
            -- We could potentially do this safely in non-conservative mode.
            defPure <- isTermBindingPure (varStrictness varInfo) def
            pure $ if sizeIsOk && defCostOk && defPure then reduced else t
          Nothing -> pure t
        -- The variable maybe a *recursive* let binding, in which case it won't be in the map,
        -- and we don't process it. ATM recursive bindings aren't inlined.
        Nothing -> pure t
  -- if the term being applied is not a `Var`, don't inline
  | otherwise = pure t
