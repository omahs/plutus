{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StrictData   #-}
module UntypedPlutusCore.Evaluation.Machine.Bytecode.Stack where

import Control.Monad (unless)
import Control.Monad.Catch
import Control.Monad.Primitive
import Control.Monad.ST.Unsafe (unsafeSTToIO)
import Data.Primitive.MutVar qualified as P
import Data.Primitive.PrimArray qualified as P
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as M
import GHC.IO.Unsafe (unsafePerformIO)

{- Note [Avoiding allocation in the stack]
The stack data structure is carefully set up to avoid allocation.

That means that:
1. We use two mutable variables for the storage and the pointer,
rather than a single variable containing a data value, since the
latter would require us to allocate every time we changed anything!
2. We use a mutuble primarry for the pointer, since most other
mutable variable stuctures will box the integer, causing more
allocation.

In some cases this costs us other inefficiency, e.g. it usually
means we need to do two variable lookups in order to get both
parts of the stack data, but this is better than allocating (I think).
-}

-- | The factor by which the stack grows when it runs out of space.
growFactor :: Int
growFactor = 2

-- | A mutable stack.
--
-- The pointer points to the first empty slot in the element in the stack.
data MStack s a = MStack
  { storage :: P.MutVar s (M.MVector s a)
  , pointer :: P.MutablePrimArray s Int
  }

stackSize :: (PrimMonad m) => MStack (PrimState m) a -> m Int
stackSize = getPointer

showMStack :: (PrimMonad m, Show a) => MStack (PrimState m) a -> m String
showMStack stack = do
  p <- getPointer stack
  v <- getStorage stack
  v' <- V.freeze $ M.slice 0 p v
  pure $ "MStack{" ++ show v' ++ "," ++ show p ++ "}"

instance Show a => Show (MStack s a) where
  show s = unsafePerformIO $ unsafeSTToIO $ showMStack s

data StackException = EmptyStackException
  deriving stock (Show)
instance Exception StackException

-- | Allocates a new stack with the given initial size.
newStack :: PrimMonad m => Int -> m (MStack (PrimState m) a)
newStack sz = do
  v <- M.new sz
  vp <- P.newMutVar v
  sp <- P.newPrimArray 1
  P.writePrimArray sp 0 0
  pure (MStack vp sp)

getStorage :: PrimMonad m => MStack (PrimState m) a -> m (M.MVector (PrimState m) a)
getStorage (MStack vp _) = P.readMutVar vp
{-# INLINE getStorage #-}

setStorage :: PrimMonad m => MStack (PrimState m) a -> M.MVector (PrimState m) a -> m ()
setStorage (MStack vp _) = P.writeMutVar vp
{-# INLINE setStorage #-}

getPointer :: PrimMonad m => MStack (PrimState m) a -> m Int
getPointer (MStack _ sp) = P.readPrimArray sp 0
{-# INLINE getPointer #-}

setPointer :: PrimMonad m => MStack (PrimState m) a -> Int -> m ()
setPointer (MStack _ sp) = P.writePrimArray sp 0
{-# INLINE setPointer #-}

-- This function returns the updated storage and pointer
-- in order to avoid having to re-read
-- the pointers after we have done the growing.
ensure :: PrimMonad m => MStack (PrimState m) a -> Int -> m (M.MVector (PrimState m) a, Int)
ensure !stack !requested = do
  v <- getStorage stack
  p <- getPointer stack
  let len = M.length v
      capacity = len - p
  if capacity < requested
  then do
    v' <- M.grow v (len * growFactor)
    setStorage stack v'
    pure (v', p)
  else
    pure (v, p)
-- Want to inline this to make sure we don't allocate a tuple
-- for the return value.
{-# INLINE ensure #-}

pushStack :: PrimMonad m => a -> MStack (PrimState m) a -> m ()
pushStack a !stack = do
  (v, p) <- ensure stack 1
  M.write v p a
  -- TODO: possible integer overflow, need to work out some bounds
  -- on stack size
  setPointer stack (p+1)
{-# INLINE pushStack #-}

popStack :: (MonadThrow m, PrimMonad m) => MStack (PrimState m) a -> m a
popStack !stack = do
  p <- getPointer stack
  unless (p > 0) $ throwM EmptyStackException
  v <- getStorage stack
  let p' = p - 1
  res <- M.read v p'
  setPointer stack p'
  pure res
{-# INLINE popStack #-}
