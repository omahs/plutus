<pre>
 <code>
                             <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/MachineParameters/Default.hs">Evaluation.Machine.MachineParameters.Default</a>
                                       /       |       \
                                      /        |        \
<a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs">Evaluation.Machine.ExBudgetingDefaults</a>  <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs">Default.Builtins</a> <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/MachineParameters.hs">Evaluation.Machine.MachineParameters</a>
                  |                            |        /
                  |                            |       /
        [other_costing_stuff]           <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Meaning.hs">Builtin.Meaning</a> ## <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Elaborate.hs">Builtin.Elaborate</a>
                                       *       |       #         #
                                      *        |        #       #
                    <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/TypeScheme.hs">Builtin.TypeScheme</a>  <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Runtime.hs">Builtin.Runtime</a>  <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Debug.hs">Builtin.Debug</a>
                   *       *          *        |
                  *        *           *       |
 <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/KnownKind.hs">Builtin.KnownKind</a> <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/KnownTypeAst.hs">Builtin.KnownTypeAst</a> <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/KnownType.hs">Builtin.KnownType</a> -- <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Emitter.hs">Builtin.Emitter</a>
                                      *        |
                                       *       |
                                        <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/Polymorphism.hs">Builtin.Polymorphism</a>
                                               |
                                               |
                                        <a href="https://github.com/input-output-hk/plutus/blob/a52315036763a03b2b1d281ca7876ceaf47a5fbd/plutus-core/plutus-core/src/PlutusCore/Builtin/HasConstant.hs">Builtin.HasConstant</a>
 </code>
</pre>











## Built-in functions: overview

### Module alignment

The module alignment of the built-in functions machinery (sans most of costing, which we'll include in a separate section):

```
                             Evaluation.Machine.MachineParameters.Default
                                       /       |       \
                                      /        |        \
Evaluation.Machine.ExBudgetingDefaults  Default.Builtins Evaluation.Machine.MachineParameters
                   |                           |        /
                   |                           |       /
         [other_costing_stuff]          Builtin.Meaning ## Builtin.Elaborate
                                       *       |       #         #
                                      *        |        #       #
                    Builtin.TypeScheme  Builtin.Runtime  Builtin.Debug
                   *       *          *        |
                  *        *           *       |
 Builtin.KnownKind Builtin.KnownTypeAst Builtin.KnownType -- Builtin.Emitter
                                      *        |
                                       *       |
                                        Builtin.Polymorphism
                                               |
                                               |
                                        Builtin.HasConstant
```

Legend:

- each node in the graph (apart from the `[other_costing_stuff]` placeholder) is an actual module with its `PlutusCore` prefix omitted for brevity
- control flows down and sideways from the center. I.e. `Evaluation.Machine.MachineParameters.Default` is the most high-level and user-facing module importing e.g. `Default.Builtins`. "Sideways from the center" means that `Builtin.Meaning` imports `Builtin.Elaborate` and not the other way around
- "imports" does not necessarily mean a direct import, it can be a transitive one
- if module X imports module Y and module Y imports module Z, then X may or may not import Z too
- the graph is not meant to be 100% complete, but it is meant to represent the vast majority and all more or less important modules of the built-in functions machinery (with most of the costing stuff omitted)
- any kind of line from module X to module Y means that module X imports something from module Y and uses that for some specific purpose, which depends on the kind of the line
- the central lines from `Evaluation.Machine.MachineParameters.Default` to `Builtin.HasConstant` contain almost 100% bits of costing-unaware evaluation of builtins
- in general, straight lines (`\`, `|`, `/`, `-`) indicate evaluation path, costing included
- star lines (`*`) indicate testing and Plutus type checking path. We don't distinguish between these two rather different things in the graph, because we don't distinguish between them in the structure of the code either as Plutus types tend to be very useful for tests
- hash lines (`#`) indicate optional quality-of-life improvements for developers and users of the builtins machinery

### User-facing API

The top-level module is `Evaluation.Machine.MachineParameters.Default`, which only exports these definitions:

```haskell
-- | 'MachineParameters' instantiated at CEK-machine-specific types and default builtins.
-- Encompasses everything we need for evaluating a UPLC program with default builtins using the CEK
-- machine.
type DefaultMachineParameters = <...>

-- | Whenever you need to evaluate UPLC in a performance-sensitive manner (e.g. in the production,
-- for benchmarking, for cost calibration etc), you MUST use this definition for creating a
-- 'DefaultMachineParameters' and not any other. Changing this definition in absolutely any way,
-- however trivial, requires running the benchmarks and making sure that the resulting GHC Core is
-- still sensible. E.g. you switch the order of arguments -- you run the benchmarks and check the
-- Core; you move this definition as-is to a different file -- you run the benchmarks and check the
-- Core; you change how it's exported (implicitly as a part of a whole-module export or explicitly
-- as a single definition) -- you get the idea.
mkMachineParametersFor :: <...>
```

`mkMachineParametersFor` is where all evaluation bits get assembled into a `DefaultMachineParameters` in a highly optimized manner. The resulting `DefaultMachineParameters` consists of

1. A `CekMachineCosts` assigning each step of the CEK machine a cost.
2. A `BuiltinsRuntime` assigning each built-in function its "runtime denotation" determining how the builtin gets evaluated and costed.

This is all we need for evaluating a UPLC program with default builtins using the CEK machine.

Both these constituents of a `DefaultMachineParameters` require a `CostModelParams`, which contains constants coming from the ledger (so that the ledger can tweak costing calculations). `CekMachineCosts` is entirely determined by the CEK-specific constants from the `CostModelParams`, but `BuiltinsRuntime` is much bigger and is assembled from

1. The builtins-specific constants from the `CostModelParams`.
2. A `BuiltinCostModel` assigning each built-in function one of `ModelOneArgument`, `ModelTwoArguments`, `ModelThreeArguments` etc depending on the number of arguments the built-in function receives. Each such model specifies the shape of the costing function for the builtin. For example, a `ModelOneArgument` may specify the costing function to be linear or constant.
3. The "meaning" of each built-in function, more on that later.

A `BuiltinCostModel` lives in the `Evaluation.Machine.ExBudgetingDefaults` module and all other costing ingridients can be discovered from there, but we're going to focus on non-costing parts of the built-in functions machinery in this section.

### Adding a built-in function

The only module one needs to amend in order to define a new built-in function for UPLC/TPLC/PIR is `Default.Builtins` (for Plutus Tx one has also edit modules in `plutus-tx` and `plutus-tx-plugin`, but that is out of scope of this document). For that do the following:

1. Add a new constructor to `DefaultFun`.
2. Handle it in the `toBuiltinMeaning` method in the `ToBuiltinMeaning uni DefaultFun` instance. You'll get a warning there once you've added the builtin to `DefaultFun`.
3. Handle the constructor in the `encode` and `decode` methods in the `Flat DefaultFun` instance. You'll only get a warning in the former once you've added the builtin to `DefaultFun` and not the latter unfortunately, so make sure not to forget about it.

And that's it, you'll get everything else automatically, including general tests that are not specific to the particular builtin (please write specific tests for new builtins!). If you run the tests and then check `git status`, you'll find a new golden file that contains the Plutus type of the new builtin.

`Default.Builtins` contains extensive documentation on how to add a built-in function, what is allowed and what should be avoided, make sure to read everything if you want to add a built-in function.

### Builtin meanings

`toBuiltinMeaning` is the sole method of the `ToBuiltinMeaning` type class (not counting two associated type/data families) defined in `Builtin.Meaning` and is used for assigning each built-in function its `BuiltinMeaning`, which comprises everything needed for testing, type checking and executing the builtin. The type signature of the method looks like this:

```haskell
toBuiltinMeaning
    :: HasMeaningIn uni val
    => BuiltinVersion fun -> fun -> BuiltinMeaning val (CostingPart uni fun)
```

i.e. in order to construct a `BuiltinMeaning` one needs not only a built-in function, but also a version of the set of built-in functions. You can read more about versioning of builtins and everything else in [this](https://cips.cardano.org/cips/cip35) CIP.

We do not construct `BuiltinMeaning`s manually, because that would be extremely laborious. Instead, we use an auxiliary function that does the heavy lifting for us. Here's its type signature with a few lines of constraints omitted for clarity:

```haskell
makeBuiltinMeaning
    :: a
    -> (cost -> FoldArgs (GetArgs a) ExBudgetStream)
    -> BuiltinMeaning val cost
```

It takes two arguments: a Haskell implementation of the builtin, which we call a denotation, and a costing function of the builtin -- and creates an entire `BuiltinMeaning` out of these two. `a` is the type of the denotation and it's so general, because we support a wide range of Haskell functions, however `a` is still constrained, it's just that we omitted the constraints for clarity.

Here's some real example of constructing a `BuiltinMeaning` out of its denotation and its costing function:

```haskell
makeBuiltinMeaning
    (\b x y -> if b then x else y)
    (runCostingFunThreeArguments . paramIfThenElse)
```

The denotation can (but not should!) be arbitrary Haskell code as long as the type of that function is supported by the builtins machinery. There's plenty of restrictions, but as you can see polymorphism is not one of them, so do read the docs in `Default.Builtins` if you want to learn more. The elaboration machinery is responsible for handling polymorphism in the type of a built-in function, it's some extremely convoluted type-level code residing in `Builtin.Elaborate`.

Since elaborating and "parsing" the type of a denotation is a complex thing, we have some helpful doctests in `Builtin.Debug` showing how one would go about debugging a `makeBuiltinMeaning` call behaving in an unexpected way.

So what's that `BuiltinMeaning` returned by `toBuiltinMeaning`? It's this:

```haskell
-- | The meaning of a built-in function consists of its type represented as a 'TypeScheme',
-- its Haskell denotation and its uninstantiated runtime denotation.
--
-- The 'TypeScheme' of a built-in function is used for example for
--
-- 1. computing the PLC type of the function to be used during type checking
-- 2. getting arity information
-- 3. generating arbitrary values to apply the function to in tests
--
-- The denotation is lazy, so that we don't need to worry about a builtin being bottom
-- (happens in tests). The production path is not affected by that, since only runtime denotations
-- are used for evaluation.
data BuiltinMeaning val cost =
    forall args res. BuiltinMeaning
        (TypeScheme val args res)
        ~(FoldArgs args res)
        (cost -> BuiltinRuntime val)
```

As the docs say, `TypeScheme` is used primarily for type checking and testing. It's defined in `Builtin.TypeScheme` together with a function converting a `TypeScheme` to a `Type`.

`FoldArgs args res`, the type of the second field, is what we turn the general type of the denotation into (originally, just `a`) by separating the list of types of arguments (`args`) from the type of the result (`res`). We do it for convenience, in a lot of places argument types are handled very differently than the result type, so it's natural to separate them explicitly. `FoldArgs` then recreates the original type of the built-in function by folding the list of arguments with `(->)`, e.g.

```haskell
FoldArgs [(), Bool] Integer
```

evaluates to

```haskell
() -> Bool -> Integer
```

It's also more convenient to store the type of the built-in function in this refined form, because we occasionally want to apply builtins to a bunch of arguments in a type-safe way in tests and if we stored the type of each builtin as some arbitrary `a` rather than the refined `FoldArgs args res`, we wouldn't be able to do that.

Note that the denotation, i.e. the second field of `BuiltinMeaning`, does not participate in script evaluation in any way, for that we have the third field of type `cost -> BuiltinRuntime val`, which, given a cost model, provides the runtime denotation of a builtin, i.e. the thing that actually gets evaluated at runtime. We will discuss runtime denotations in great detail below, but let's take a detour and see how built-in functions are type checked.

### Type checking built-in functions

The `TypeScheme` of a built-in function (the first field of `BuiltinMeaning`) is defined like this (some constraints are omitted via `<...>` for clarity -- those are only used for testing):

```haskell
-- | The type of type schemes of built-in functions.
-- @args@ is a list of types of arguments, @res@ is the resulting type.
-- E.g. @Text -> Bool -> Integer@ is encoded as @TypeScheme val [Text, Bool] Integer@.
data TypeScheme val (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: (KnownTypeAst (UniOf val) res, <...>)
        => TypeScheme val '[] res
    TypeSchemeArrow
        :: (KnownTypeAst (UniOf val) arg, <...>)
        => TypeScheme val args res -> TypeScheme val (arg ': args) res
    TypeSchemeAll
        :: (KnownSymbol text, KnownNat uniq, KnownKind kind)
        => Proxy '(text, uniq, kind)
        -> TypeScheme val args res
        -> TypeScheme val args res
```

Let's break it down:

1. `TypeSchemeResult` only stores the resulting type of a built-in function in the form of a `KnownTypeAst` constraint (more on that later).
2. `TypeSchemeArrow` stores the type of an argument of the builtin, also in the form of a `KnownTypeAst` constraint, and the rest of the type scheme. A builtin having a `TypeSchemeArrow` in its `TypeScheme` at a specific position means that this is where the builtin expects a term argument of a certain Haskell/Plutus type.
3. Similarly a `TypeSchemeAll` expresses "the builtin takes a type argument at this position". Which means that the Plutus type of the builtin has an `all (x :: kind)` quantifier at this position. Hence we store the textual name of the type variable (`text`), its unique-within-the-type-signature-of-the-builtin index (`uniq`) and the kind of the variable (`kind`) inside of the `TypeSchemeAll`, as well as the rest of the type scheme. `Proxy` is just to give convenient access to the Haskell type variables storing the information about the Plutus type variable. Instead of using Haskell type variables, we could've demoted all the information to the term level and store `Text`, `Unique` and `Kind` directly (as opposed to providing access to them through the constraints), but we didn't want to hardcode Plutus-specific `Kind` in there and it doesn't matter anyway. The reason why we end up having that information at the type level in the first place is that we get it from the Haskell type of the denotation, which lives at the type level. The reason why we get it from there is that it saves us from typing it manually, which is error-prone and way too laborious.

Note how term-level arguments are reflected in the `args` index of a `TypeScheme` and type-level aren't. TODO

Here's a concrete example of how a `TypeScheme` for `DivideInteger` might look like if we were to construct it directly for a particular type of evaluator's value (each evaluator defines its own type of value, in our example it's `CekValue`):

```haskell
divideIntegerTypeScheme ::
    TypeScheme
        (CekValue DefaultUni fun ann)
        '[Integer, Integer]
        (EvaluationResult Integer)
divideIntegerTypeScheme = TypeSchemeArrow $ TypeSchemeArrow TypeSchemeResult
```

`DivideInteger` takes two `Integer` arguments, hence `'[Integer, Integer]` at the type level and two `TypeSchemeArrow`s at the term level.

In the actual code we don't construct type schemes for specific types of values as that would be a lot of duplicate code and instead we just carry some constraints around specifying what the type of value needs to satisfy in order for it to be usable within a `TypeScheme`. In general, we really try and don't duplicate code and instead use ad hoc polymorphism, which we optimize heavily when it matters.

In order to infer the type of a built-in function, we convert its `TypeScheme` to the Plutus type:

```haskell
typeSchemeToType :: TypeScheme val args res -> Type TyName (UniOf val) ()
```

via straightforward recursion on the spine of the `TypeScheme`. During that process we need to convert the original Haskell types of arguments to their Plutus counterparts and this is exactly what `KnownTypeAst` is responsible for.




                    Builtin.TypeScheme
                   *       *          *
                  *        *           *
 Builtin.KnownKind Builtin.KnownTypeAst Builtin.KnownType
                                      *        |
                                       *       |
                                        Builtin.Polymorphism

### Runtime denotations

Here's how the type of runtime denotations is defined:

```haskell
-- | A 'BuiltinRuntime' represents a possibly partial builtin application, including an empty
-- builtin application (i.e. just the builtin with no arguments).
--
-- Applying or type-instantiating a builtin peels off the corresponding constructor from its
-- 'BuiltinRuntime'.
--
-- 'BuiltinResult' contains the cost (an 'ExBudget') and the result (a @MakeKnownM val@) of the
-- builtin application. The cost is stored strictly, since the evaluator is going to look at it
-- and the result is stored lazily, since it's not supposed to be forced before accounting for the
-- cost of the application. If the cost exceeds the available budget, the evaluator discards the
-- the result of the builtin application without ever forcing it and terminates with evaluation
-- failure. Allowing the user to compute something that they don't have the budget for would be a
-- major bug.
data BuiltinRuntime val
    = BuiltinResult ExBudget ~(MakeKnownM val)
    | BuiltinExpectArgument (val -> BuiltinRuntime val)
    | BuiltinExpectForce (BuiltinRuntime val)
```

When a partial builtin application represented as a `BuiltinRuntime` is being forced at runtime, this results in the `BuiltinExpectForce` being peeled off of that `BuiltinRuntime` (if the outermost constructor is not `BuiltinExpectForce`, then it's an evaluation failure).

Similarly, when evaluation stumbles upon a built-in function applied to an argument, the `BuiltinExpectArgument` is peeled off of the `BuiltinRuntime` representing the possibly already partially applied builtin (giving an evaluation failure if the outermost constructor is not `BuiltinExpectArgument`) and the continuation stored in that constructor gets fed the argument. This way we collect all arguments first and only when `BuiltinResult` is reached those arguments get unlifted and fed to the Haskell denotation of the builtin. The denotation then gets evaluated and its result gets lifted into a `val` in the `MakeKnownM` monad providing access to the error and logging effects (only these two), since built-in functions have the capacity to fail and to emit log messages.

Each built-in function gets its own `BuiltinRuntime`, since the runtime behavior of different built-in functions is distinct. However for script evaluation we need a data type for "all built-in functions from the given set have a `BuiltinRuntime`" and for that we use this unimaginative definition:

```haskell
data BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinsRuntime :: fun -> BuiltinRuntime val
    }
```

(note the `s` in `BuiltinsRuntime` vs the no `s` in `BuiltinRuntime`).

Since every `BuiltinRuntime` is constructred from a respective `BuiltinMeaning`, we have a function for computing `BuiltinsRuntime` for any set of builtins implementing a `ToBuiltinMeaning` (i.e. such a set that each of its builtins has a `BuiltinMeaning`), given the version of the set and a code model:

```haskell
-- | Calculate runtime info for all built-in functions given meanings of builtins (as a constraint),
-- the version of the set of builtins and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, ToBuiltinMeaning uni fun, HasMeaningIn uni val)
    => BuiltinVersion fun -> cost -> BuiltinsRuntime fun val
```

The `HasMeaningIn` constraint is defined like this:

```haskell
-- | Constraints available when defining a built-in function.
type HasMeaningIn uni val = (Typeable val, ExMemoryUsage val, HasConstantIn uni val)
```

For us of interest is only the `HasConstantIn` part.

### Unlifting & lifting

    `ElaborateFromTo 0 j val a` -- there be dragons, you don't need to understand how it works,
    it's just a bunch of type-level nonsense, all you need to know about it is explained in
    `Default.Builtins`, unless you want to amend how elaboration of polymorphic denotations works,
    which you probably don't

    elaboration is hard, so we need
    `Builtin.Debug` for debugging `ElaborateFromTo` and `makeBuiltinMeaning`.
    `Builtin.Debug` also doubles as testing of the variety of custom type errors that we have.

    `TypeScheme` not on evaluation path -- only about Plutus typing of builtins and tests,
    feel free to add anything to it

    `KnownKind`

    `KnownTypeAst`

    `BuiltinRuntime`
    runtime denotation = denotation + unlifting + lifting + costing

    `Emitter`

    `Builtin.KnownType`

    `Builtin.Polymorphism`

    `HasConstant`

 Each such model is turned into an actual costing function via a highly optimized "runner", such as `runOneArgumentModel`, `runTwoArgumentModel`, `runThreeArgumentModel` etc.
