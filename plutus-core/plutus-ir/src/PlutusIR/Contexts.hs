{-# LANGUAGE LambdaCase #-}
-- | Datatypes representing 'contexts with holes' in Plutus IR terms.
--
-- Useful for focussing on a sub-part of a term and then reconstructing the term, but
-- with the context as a reified datatype that can be inspected and modified.
module PlutusIR.Contexts where

import PlutusCore.MkPlc
import PlutusIR.Core

{- | Takes a term and views it as a head plus a list of arguments, e.g.

@
    [{ f t } u v]
    -->
    (f, [{ _ t } u v])
    ==
    f [TypeArg t, TermArg u, TermArg v]
@
-}
splitApplication :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, [Arg Term tyname name uni fun ann])
splitApplication tm
  = go tm []
  where
    go (Apply ann f arg) args    = go f (TermArg ann arg : args)
    go (TyInst ann f tyArg) args = go f (TypeArg ann tyArg : args)
    go t ctx                     = (t, ctx)

{- Note [Context splitting in a recursive pass]
When writing a recursive pass that processes the whole program, you must be
a bit cautious when using a context split. The context split may traverse
part of the program, which will _also_ be traversed by the main recursive
traversal. This can lead to quadratic runtime.

This is usually okay for something like 'splitApplication', since it is
quadratic in the longest application in the program, which is usually not
significantly long.
-}
