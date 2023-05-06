{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Transform.DelayedArg (delayedArg) where

import PlutusCore qualified as PLC
import UntypedPlutusCore.Core

import Control.Lens
import Control.Monad.Trans.Writer.CPS
import Data.Set (Set)
import Data.Set qualified as Set

{- | Remove `Delay` in arguments, if possible. The goal is to turn
@(\n -> ...Force n...Force n...) (\Delay arg)@ into @(\n -> ...n...n...) arg@.
This transformation is performed if:

    * All occurrences of @arg@ are under @Force@.

    * @arg@ is essentially work-free.

This achieves a similar effect to Plutonomy's "Split Delay" optimization. The difference
is that Split Delay simply splits the @Delay@, turning the above example into
@(\m -> (\n -> ...Force n...Force n...) (Delay m)) arg@, and then relies on other optimizations
like inlining and force-delay-cancel to simplify it further.

The advantages of our approach are:

    * It is very simple to implement

    * It guarantees to not increase the size or the cost of the program.
-}
delayedArg ::
    (PLC.MonadQuote m, PLC.Rename (Term name uni fun a), Ord name) =>
    Term name uni fun a ->
    m (Term name uni fun a)
delayedArg t0 = do
    t <- PLC.rename t0
    pure . uncurry (flip simplifyBodies) $ simplifyArgs (unforcedVars t) t

-- | First pass
unforcedVars :: forall name uni fun a. (Ord name) => Term name uni fun a -> Set name
unforcedVars = execWriter . go
  where
    go :: Term name uni fun a -> Writer (Set name) ()
    go = \case
        Var _ n       -> tell (Set.singleton n)
        Force _ Var{} -> pure ()
        t             -> foldlMOf termSubterms (const go) () t

-- | Second pass
simplifyArgs ::
    forall name uni fun a.
    (Ord name) =>
    Set name ->
    Term name uni fun a ->
    (Term name uni fun a, Set name)
simplifyArgs blacklist = runWriter . go
  where
    go = \case
        Apply appAnn (LamAbs lamAnn n lamBody) (Delay _delayAnn arg)
            | isEssentiallyWorkFree arg
            , n `Set.notMember` blacklist -> do
                tell (Set.singleton n)
                Apply appAnn <$> (LamAbs lamAnn n <$> go lamBody) <*> go arg
        t -> forOf termSubterms t go

-- | Third pass
simplifyBodies :: (Ord name) => Set name -> Term name uni fun a -> Term name uni fun a
simplifyBodies whitelist = go
  where
    go = \case
        Force _forceAnn var@(Var _ n)
            | n `Set.member` whitelist -> var
        t -> t & termSubterms %~ go

isEssentiallyWorkFree :: Term name uni fun a -> Bool
isEssentiallyWorkFree = \case
    LamAbs{}   -> True
    Constant{} -> True
    Delay{}    -> True
    _          -> False
