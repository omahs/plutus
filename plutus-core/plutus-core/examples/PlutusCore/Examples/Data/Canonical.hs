{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusCore.Examples.Data.Canonical
    ( equalsCanonicalViaData
    ) where

import PlutusCore.Core
import PlutusCore.Data as Data
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name
import PlutusCore.Quote

-- |
--
-- > equalsCanonicalViaData =
-- >   /\(a :: *) -> \(toData : a -> data) (x y : a) ->
-- >     equalsCanonical {a} (mkCanonical {a} toData x) (mkCanonical {a} toData y)
equalsCanonicalViaData :: Term TyName Name DefaultUni DefaultFun ()
equalsCanonicalViaData = runQuote $ do
    a      <- freshTyName "a"
    toData <- freshName "toData"
    x      <- freshName "x"
    y      <- freshName "y"
    let mkC = Apply () (TyInst () (Builtin () MkCanonical) $ TyVar () a) $ Var () toData
    return
        . TyAbs () a (Type ())
        . LamAbs () toData (TyFun () (TyVar () a) $ mkTyBuiltin @_ @Data ())
        . LamAbs () x (TyVar () a)
        . LamAbs () y (TyVar () a)
        $ mkIterAppNoAnn (TyInst () (Builtin () EqualsCanonical) $ TyVar () a)
            [ Apply () mkC $ Var () x
            , Apply () mkC $ Var () y
            ]
