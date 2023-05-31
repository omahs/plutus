{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
{- |
inspiration taken from src/Generics/EMGM/Functions/ZipWith.hs
and Generics.Regular.Functions.Zip

Perhaps other ideas or things to look at:

<https://hackage.haskell.org/package/semialign>
<https://hackage.haskell.org/package/matchable-0.1.2.1/docs/Data-Matchable.html>
<https://hackage.haskell.org/package/alignment-0.1.0.3/docs/Data-Alignment.html>
-}
module Generics.Deriving.FZip
    ( FZip (fzipWithM)
    , fzipWith
    ) where

import Data.List.NonEmpty
import GHC.Generics
import Control.Monad.Except

class FZip f where
    fzipWithM :: MonadError String m => (a -> b -> m c) -> f a -> f b -> m (f c)
    default fzipWithM :: (MonadError String m, Generic1 f, GFZip (Rep1 f)) => (a -> b -> m c) -> f a -> f b -> m (f c)
    fzipWithM f a b = to1 <$> gfzipWithM f (from1 a) (from1 b)

class GFZip f where
    gfzipWithM :: MonadError String m => (a -> b -> m c) -> f a -> f b -> m (f c)

instance (GFZip a , GFZip b) => GFZip (a :*: b) where
    gfzipWithM f (a1 :*: b1) (a2 :*: b2) = (:*:)
                                            <$> gfzipWithM f a1 a2
                                            <*> gfzipWithM f b1 b2

instance (GFZip a, GFZip b) => GFZip (a :+: b) where
    gfzipWithM f (L1 a1) (L1 a2) = L1 <$> gfzipWithM f a1 a2
    gfzipWithM f (R1 b1) (R1 b2) = R1 <$> gfzipWithM f b1 b2
    gfzipWithM _ _ _ = throwError "not exact"

-- cons with no fields
instance GFZip U1 where
    gfzipWithM _ _ _ = pure U1

-- left biased constant field
instance GFZip (K1 i c) where
  gfzipWithM _ (K1 a1) _ = pure $ K1 a1

-- parameterized field, here the actual zippping happens
instance GFZip Par1 where
    gfzipWithM f (Par1 a) (Par1 b) = Par1 <$> f a b

-- 1-level nested parameter, call the nested type FZip instance
instance FZip f => GFZip (Rec1 f) where
    gfzipWithM f (Rec1 a) (Rec1 b) = Rec1 <$> fzipWithM f a b

-- n-nested parameter
instance (FZip f, GFZip g) => GFZip (f :.: g) where
   gfzipWithM f (Comp1 x1) (Comp1 x2) = Comp1 <$> fzipWithM (gfzipWithM f) x1 x2

-- void
instance GFZip V1 where
    gfzipWithM _ x = case x of {}

-- metadata ignored
instance (GFZip a) => GFZip (M1 i c a) where
  gfzipWithM f (M1 x) (M1 y) = M1 <$> gfzipWithM f x y

fzipWith :: (FZip f, MonadError String m) => (a -> b -> c) -> f a -> f b -> m (f c)
fzipWith f = fzipWithM (\ x y -> pure $ f x y)

deriving anyclass instance FZip []
deriving anyclass instance FZip Maybe
deriving anyclass instance FZip NonEmpty
