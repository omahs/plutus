{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Builtin.HasConstant
    ( KnownTypeError (..)
    , throwNotAConstant
    , HasConstant (..)
    , HasConstantIn
    , fromValueOf
    , fromValue
    , EqCanonicalResult (..)
    , toEqCanonicalResult
    , fromEqCanonicalResult
    , EqCanonical (..)
    ) where

import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.Name

import Universe

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
class HasConstant term where
    -- Switching from 'MonadError' to 'Either' here gave us a speedup of 2-4%.
    -- | Unwrap from a 'Constant'-like constructor throwing an 'UnliftingError' if the provided
    -- @term@ is not a wrapped Haskell value.
    asConstant :: term -> Either KnownTypeError (Some (ValueOf (UniOf term)))

    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

-- | Wrap a Haskell value (given its explicit type tag) as a @term@.
fromValueOf :: HasConstant term => UniOf term (Esc a) -> a -> term
fromValueOf uni = fromConstant . someValueOf uni
{-# INLINE fromValueOf #-}

-- | Wrap a Haskell value (provided its type is in the universe) as a @term@.
fromValue :: (HasConstant term, UniOf term `Includes` a) => a -> term
fromValue = fromValueOf knownUni
{-# INLINE fromValue #-}

instance HasConstant (Term TyName Name uni fun ()) where
    asConstant (Constant _ val) = pure val
    asConstant _                = throwNotAConstant

    fromConstant = Constant ()

data EqCanonicalResult
    = EqCanonicalTrue
    | EqCanonicalFalse
    | EqCanonicalUnexpectedInput

toEqCanonicalResult :: Bool -> EqCanonicalResult
toEqCanonicalResult True  = EqCanonicalTrue
toEqCanonicalResult False = EqCanonicalFalse

fromEqCanonicalResult :: EqCanonicalResult -> EvaluationResult Bool
fromEqCanonicalResult EqCanonicalTrue            = EvaluationSuccess True
fromEqCanonicalResult EqCanonicalFalse           = EvaluationSuccess False
fromEqCanonicalResult EqCanonicalUnexpectedInput = EvaluationFailure

instance Semigroup EqCanonicalResult where
    EqCanonicalTrue <> res2 = res2
    res1            <> _    = res1

instance Monoid EqCanonicalResult where
    mempty = EqCanonicalTrue

class EqCanonical term where
    eqCanonical :: term -> term -> EqCanonicalResult

instance EqCanonical (Term TyName Name uni fun ()) where
    eqCanonical = undefined
