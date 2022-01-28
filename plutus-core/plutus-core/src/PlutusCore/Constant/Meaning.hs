-- GHC doesn't like the definition of 'makeBuiltinMeaning'.
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE StandaloneKindSignatures  #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- DO NOT enable @StrictData@ in this file as it makes the evaluator slower (even with @~@ put in
-- 'BuiltinRuntime' in the places where it's necessary to have laziness for evaluators to work).

module PlutusCore.Constant.Meaning where

import PlutusPrelude

import PlutusCore.Constant.Function
import PlutusCore.Constant.Kinded
import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Some.GADT
import Data.Type.Bool
import Data.Type.Equality
import GHC.TypeLits

-- | The meaning of a built-in function consists of its type represented as a 'TypeScheme',
-- its Haskell denotation and a costing function (both in uninstantiated form).
--
-- The 'TypeScheme' of a built-in function is used for
--
-- 1. computing the PLC type of the function to be used during type checking
-- 2. checking equality of the expected type of an argument of a builtin and the actual one
--    during evaluation, so that we can avoid unsafe-coercing
--
-- A costing function for a built-in function is computed from a cost model for all built-in
-- functions from a certain set, hence the @cost@ parameter.
data BuiltinMeaning term cost =
    forall args res. BuiltinMeaning
        (TypeScheme term args res)
        (FoldArgs args res)
        (cost -> FoldArgsEx args)
-- I tried making it @(forall term. HasConstantIn uni term => TypeScheme term args res)@ instead of
-- @TypeScheme term args res@, but 'makeBuiltinMeaning' has to talk about
-- @KnownPolytype binds term args res a@ (note the @term@), because instances of 'KnownMonotype'
-- are constrained with @KnownType term arg@ and @KnownType term res@, and so the earliest we can
-- generalize from @term@ to @UniOf term@ is in 'toBuiltinMeaning'.
-- Besides, for 'BuiltinRuntime' we want to have a concrete 'TypeScheme' anyway for performance
-- reasons (there isn't much point in caching a value of a type with a constraint as it becomes a
-- function at runtime anyway, due to constraints being compiled as dictionaries).

-- We tried instantiating 'BuiltinMeaning' on the fly and that was slower than precaching
-- 'BuiltinRuntime's.
-- | A 'BuiltinRuntime' represents a possibly partial builtin application.
-- We get an initial 'BuiltinRuntime' representing an empty builtin application (i.e. just the
-- builtin with no arguments) by instantiating (via 'toBuiltinRuntime') a 'BuiltinMeaning'.
--
-- A 'BuiltinRuntime' contains info that is used during evaluation:
--
-- 1. the 'TypeScheme' of the uninstantiated part of the builtin. I.e. initially it's the type
--      scheme of the whole builtin, but applying or type-instantiating the builtin peels off
--      the corresponding constructor from the type scheme
-- 2. the (possibly partially instantiated) denotation
-- 3. the (possibly partially instantiated) costing function
--
-- All the three are in sync in terms of partial instantiatedness due to 'TypeScheme' being a
-- GADT and 'FoldArgs' and 'FoldArgsEx' operating on the index of that GADT.
data BuiltinRuntime term =
    forall args res. BuiltinRuntime
        (TypeScheme term args res)
        (FoldArgs args res)  -- Must be lazy, because we don't want to compute the denotation when
                             -- it's fully saturated before figuring out what it's going to cost.
        (FoldArgsEx args)    -- We make this lazy, so that evaluators that don't care about costing
                             -- can put @undefined@ here. TODO: we should test if making this strict
                             -- introduces any measurable speedup.

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun term = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime term)
    }

-- | Instantiate a 'BuiltinMeaning' given denotations of built-in functions and a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning term cost -> BuiltinRuntime term
toBuiltinRuntime cost (BuiltinMeaning sch f exF) = BuiltinRuntime sch f (exF cost)

-- | A type class for \"each function from a set of built-in functions has a 'BuiltinMeaning'\".
class (Bounded fun, Enum fun, Ix fun) => ToBuiltinMeaning uni fun where
    -- | The @cost@ part of 'BuiltinMeaning'.
    type CostingPart uni fun

    -- | Get the 'BuiltinMeaning' of a built-in function.
    toBuiltinMeaning :: HasConstantIn uni term => fun -> BuiltinMeaning term (CostingPart uni fun)

-- | Get the type of a built-in function.
typeOfBuiltinFunction :: ToBuiltinMeaning uni fun => fun -> Type TyName uni ()
typeOfBuiltinFunction fun = case toBuiltinMeaning @_ @_ @(Term TyName Name _ _ ()) fun of
    BuiltinMeaning sch _ _ -> typeSchemeToType sch

-- | Calculate runtime info for all built-in functions given denotations of builtins
-- and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, HasConstantIn uni term, ToBuiltinMeaning uni fun)
    => cost -> BuiltinsRuntime fun term
toBuiltinsRuntime cost =
    BuiltinsRuntime . tabulateArray $ toBuiltinRuntime cost . toBuiltinMeaning

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err term) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri

{- Note [Automatic derivation of type schemes]
We use two type classes for automatic derivation of type schemes: 'KnownMonotype' and
'KnownPolytype'. The terminology is due to https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#The_Hindley%E2%80%93Milner_type_system

'KnownMonotype' and 'KnownPolytype' are responsible for deriving monomorphic and polymorphic types,
respectively. 'KnownMonotype' turns every argument that the Haskell denotation of a builtin
receives into a 'TypeSchemeArrow'. We extract the arguments from the type of the Haskell denotation
using the 'GetArgs' type family. 'KnownPolytype' turns every bound variable into a 'TypeSchemeAll'.
We extract variables from the type of the Haskell denotation using the 'ToBinds' type family
(in particular, see the @ToBinds (TypeScheme term args res)@ type instances). Variables are
collected in the order that they appear in (i.e. just like in Haskell). For example, processing
a type signature like

    const
        :: ( a ~ Opaque term (TyVarRep ('TyNameRep "a" 0))
           , b ~ Opaque term (TyVarRep ('TyNameRep "b" 1))
           )
        => b -> a -> b

with 'ToBinds' results in the following list of bindings:

    '[ 'Some ('TyNameRep "b" 1), 'Some ('TyNameRep "a" 0) ]

Higher-kinded type variables are fully supported.

The implementations of the 'KnownMonotype' and 'KnownPolytype' classes are structured in an
inference-friendly manner:

1. we compute @args@ using a type family ('GetArgs') in order to dispatch on the list of
   arguments of a built-in function in a way that doesn't force us to introduce overlapping
   instances
2. the @a -> res@ dependency allows us not to compute @res@ using a type family like with @args@
3. the @args res -> a@ dependency allows us not to mention @a@ in the type of 'knownMonotype'

Polymorphic built-in functions are handled via automatic specialization of all Haskell type
variables as types representing PLC type variables, as long as each Haskell variable appears as a
left argument to @(->)@ and is not buried somewhere inside (i.e. automatic derivation can handle
neither @f a@, @ListRep a@, nor @f Int@. Nor is @a -> b@ allowed to the left of an @(->)@.
Where all lower-case names are Haskell type variables). We'll call functions having such types
"simply-polymorphic". See the docs of 'EnumerateFromTo' for details.

The end result is that the user only has to specify the type of the denotation of a built-in
function and the 'TypeScheme' of the built-in function will be derived automatically. And in the
monomorphic and simply-polymorphic cases no types need to be specified at all.
-}

type family GetArgs a :: [GHC.Type] where
    GetArgs (a -> b) = a ': GetArgs b
    GetArgs _        = '[]

-- | A class that allows us to derive a monotype for a builtin.
class KnownMonotype term args res a | args res -> a, a -> res where
    knownMonotype :: TypeScheme term args res

-- | Once we've run out of term-level arguments, we return a 'TypeSchemeResult'.
instance (res ~ res', KnownType term res) => KnownMonotype term '[] res res' where
    knownMonotype = TypeSchemeResult

-- | Every term-level argument becomes as 'TypeSchemeArrow'.
instance (KnownType term arg, KnownMonotype term args res a) =>
            KnownMonotype term (arg ': args) res (arg -> a) where
    knownMonotype = TypeSchemeArrow knownMonotype

-- | A class that allows us to derive a polytype for a builtin.
class KnownPolytype (binds :: [Some TyNameRep]) term args res a | args res -> a, a -> res where
    knownPolytype :: Proxy binds -> TypeScheme term args res

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype term args res a => KnownPolytype '[] term args res a where
    knownPolytype _ = knownMonotype

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds term args res a) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) term args res a where
    knownPolytype _ = TypeSchemeAll @name @uniq @kind Proxy $ knownPolytype (Proxy @binds)

-- The 'TryUnify' gadget explained in detail in https://github.com/effectfully/sketches/tree/master/poly-type-of-saga/part1-try-unify

-- | Check if two values of different kinds are in fact the same value (with the same kind).
-- A heterogeneous version of @Type.Equality.(==)@.
type (===) :: forall a b. a -> b -> Bool
type family x === y where
    x === x = 'True
    x === y = 'False

type TryUnify :: forall a b. Bool -> a -> b -> GHC.Constraint
class same ~ (x === y) => TryUnify same x y
instance (x === y) ~ 'False => TryUnify 'False x y
instance {-# INCOHERENT #-} (x ~~ y, same ~ 'True) => TryUnify same x y

-- | Unify two values unless they're obviously distinct (in which case do nothing).
-- Allows us to detect and specialize type variables, since a type variable is not obviously
-- distinct from anything else and so the INCOHERENT instance of 'TryUnify' gets triggered and the
-- variable gets unified with whatever we want it to.
type (~?~) :: forall a b. a -> b -> GHC.Constraint
type x ~?~ y = TryUnify (x === y) x y

-- | Get the element at an @i@th position in a list.
type Lookup :: forall a. Nat -> [a] -> a
type family Lookup n xs where
    Lookup _ '[]       = TypeError ('Text "Not enough elements")
    Lookup 0 (x ': xs) = x
    Lookup n (_ ': xs) = Lookup (n - 1) xs

-- | Get the name at the @i@th position in the list of default names. We could use @a_0@, @a_1@,
-- @a_2@ etc instead, but @a@, @b@, @c@ etc are nicer.
type GetName :: GHC.Type -> Nat -> Symbol
type family GetName k i where
    GetName GHC.Type i = Lookup i '["a", "b", "c", "d", "e", "i", "j", "k", "l"]
    GetName _        i = Lookup i '["f", "g", "h", "m", "n"]  -- For higher-kinded types.

-- | Like 'id', but a type constructor.
type Id :: forall a. a -> a
data family Id x

-- | Try to specialize @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one (either @i + 1@ or @i@ depending on whether
-- specialization attempt is successful or not).
-- @f@ is for wrapping 'TyVarRep' (see 'HandleHole' for how this is used).
type TrySpecializeAsVar :: forall k. Nat -> Nat -> (k -> k) -> k -> GHC.Constraint
class TrySpecializeAsVar i j f a | i f a -> j
instance
    ( var ~ f (TyVarRep @k ('TyNameRep (GetName k i) i))
    -- Try to unify @a@ with a freshly created @var@.
    , a ~?~ var
    -- If @a@ is equal to @var@ then unification was successful and we just used the fresh id and
    -- so we need to bump it up. Otherwise @var@ was discarded and so the fresh id is still fresh.
    -- Replacing @(===)@ with @(==)@ causes errors at use site, for whatever reason.
    , j ~ If (a === var) (i + 1) i
    ) => TrySpecializeAsVar i j f (a :: k)

-- | First try to specialize the hole using 'TrySpecializeAsVar' and then recurse on the result of
-- that using 'HandleHoles'.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type HandleHole :: Nat -> Nat -> GHC.Type -> Hole -> GHC.Constraint
class HandleHole i j term hole | i term hole -> j
-- In the Rep context @x@ is attempted to be instantiated as a 'TyVarRep'.
instance
    ( TrySpecializeAsVar i j Id (Id x)  -- The two 'Id's cancel each other.
    , HandleHoles j k term x
    ) => HandleHole i k term (RepHole x)
-- In the Type context @a@ is attempted to be instantiated as a 'TyVarRep' wrapped in @Opaque term@.
instance
    ( TrySpecializeAsVar i j (Opaque term) a
    , HandleHoles j k term a
    ) => HandleHole i k term (TypeHole a)

-- | Call 'HandleHole' over each hole from the list, threading the state (the fresh unique) through
-- the calls.
type HandleHolesGo :: Nat -> Nat -> GHC.Type -> [Hole] -> GHC.Constraint
class HandleHolesGo i j term holes | i term holes -> j
instance i ~ j => HandleHolesGo i j term '[]
instance
      ( HandleHole i j term hole
      , HandleHolesGo j k term holes
      ) => HandleHolesGo i k term (hole ': holes)

-- | If the outermost constructor of the second argument is known and happens to be one of the
-- constructors of the list data type, then the second argument is returned back. Otherwise the
-- first one is returned, which is meant to be a custom type error.
type ThrowOnStuckList :: forall a. [a] -> [a] -> [a]
type family ThrowOnStuckList err xs where
    ThrowOnStuckList _   '[]       = '[]
    ThrowOnStuckList _   (x ': xs) = x ': xs
    ThrowOnStuckList err _         = err

type UnknownTypeError :: forall a any. GHC.Type -> a -> any
type family UnknownTypeError term x where
    UnknownTypeError term x = TypeError
        (         'Text "No instance for ‘KnownTypeAst "
            ':<>: 'ShowType (UniOf term)
            ':<>: 'Text " ("
            ':<>: 'ShowType x
            ':<>: 'Text ")’"
        ':$$: 'Text "Which means"
        ':$$: 'Text "  ‘" ':<>: 'ShowType x ':<>: 'Text "’"
        ':$$: 'Text "is neither a built-in type, nor one of the control types."
        ':$$: 'Text "If it can be represented in terms of one of the built-in types"
        ':$$: 'Text "  then go add the instance (you may need a ‘KnownTypeIn’ one too)"
        ':$$: 'Text "  alongside the instance for the built-in type."
        ':$$: 'Text "Otherwise you may need to add a new built-in type"
        ':$$: 'Text "  (provided you're doing something that can be supported in principle)"
        )

-- | Get the holes of @x@ and recurse into them.
type HandleHoles :: forall a. Nat -> Nat -> GHC.Type -> a -> GHC.Constraint
type HandleHoles i j term x =
    -- Here we detect a stuck application of 'ToHoles' and throw 'UnknownTypeError' on it.
    -- See https://blog.csongor.co.uk/report-stuck-families for a detailed description of how
    -- detection of stuck type families works.
    HandleHolesGo i j term (ThrowOnStuckList (UnknownTypeError term x) (ToHoles x))

-- | Specialize each Haskell type variable in @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type ElaborateFromTo :: Nat -> Nat -> GHC.Type -> GHC.Type -> GHC.Constraint
type ElaborateFromTo i j term a = HandleHole i j term (TypeHole a)

-- See Note [Automatic derivation of type schemes]
-- | Construct the meaning for a built-in function by automatically deriving its
-- 'TypeScheme', given
--
-- 1. the denotation of the builtin
-- 2. an uninstantiated costing function
makeBuiltinMeaning
    :: forall a term cost binds args res j.
       ( binds ~ ToBinds a, args ~ GetArgs a, a ~ FoldArgs args res
       , ElaborateFromTo 0 j term a, KnownPolytype binds term args res a
       )
    => a -> (cost -> FoldArgsEx args) -> BuiltinMeaning term cost
makeBuiltinMeaning = BuiltinMeaning (knownPolytype (Proxy @binds) :: TypeScheme term args res)
