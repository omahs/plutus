{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module UntypedPlutusCore.Core.Zip
    ( pzipWith
    , pzip
    , tzipWith
    , tzip
    ) where

import Control.Monad (void, when)
import Control.Monad.Except (MonadError, throwError)
import UntypedPlutusCore.Core.Instance.Eq ()
import UntypedPlutusCore.Core.Type
import Generics.Deriving.FZip

-- | Zip two programs using a combinator function for annotations.
--
-- Throws an error if the input programs are not "equal" modulo annotations.
-- Note that the function is "left-biased", so in case that the 2 input programs contain `Name`s,
-- the output program will contain just the `Name`s of the first input program.
pzipWith :: forall p name uni fun ann1 ann2 ann3 m.
           (p ~ Program name uni fun, (Eq (Term name uni fun ())), MonadError String m)
         => (ann1 -> ann2 -> ann3)
         -> p ann1
         -> p ann2
         -> m (p ann3)
pzipWith f (Program ann1 ver1 t1) (Program ann2 ver2 t2) = do
    when (ver1 /= ver2) $
       throwError "zip: Versions do not match."
    Program (f ann1 ann2) ver1 <$> tzipWith f t1 t2

-- | Zip two terms using a combinator function for annotations.
--
-- Throws an error if the input terms are not "equal" modulo annotations.
-- Note that the function is "left-biased", so in case that the 2 input terms contain `Name`s,
-- the output term will contain just the `Name`s of the first input term.
-- TODO: this is not an optimal implementation
tzipWith :: forall t name uni fun ann1 ann2 ann3 m.
           (t ~ Term name uni fun, Eq (t ()), MonadError String m)
         => (ann1 -> ann2 -> ann3)
         -> t ann1
         -> t ann2
         -> m (t ann3)
tzipWith f term1 term2 = do
    -- Prior establishing t1==t2 avoids the need to check for Eq uni, Eq fun and alpha-equivalence.
    -- Slower this way because we have to re-traverse the terms.
    when (void term1 /= void term2) $
       throwError "zip: Terms do not match."
    fzipWith f term1 term2

-- | Zip 2 programs by pairing their annotations
pzip :: (p ~ Program name uni fun, Eq (Term name uni fun ()), MonadError String m)
     => p ann1
     -> p ann2
     -> m (p (ann1,ann2))
pzip = pzipWith (,)

-- | Zip 2 terms by pairing their annotations
tzip :: (t ~ Term name uni fun, Eq (t ()), MonadError String m)
     => t ann1
     -> t ann2
     -> m (t (ann1,ann2))
tzip = tzipWith (,)
