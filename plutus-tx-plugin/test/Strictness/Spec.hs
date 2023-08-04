{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Strictness.Spec where

import Test.Tasty.Extras

import PlutusTx qualified as Tx
import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested
    "Strictness"
    [ goldenEvalCekCatch "fAppliedToBottom" $ [fAppliedToBottom]
    , goldenPirReadable "fAppliedToBottom" fAppliedToBottom
    , goldenUPlcReadable "fAppliedToBottom" fAppliedToBottom
    ]

f :: CompiledCode (Integer -> Integer)
f =
  $$( compile
        [||
        \x -> x PlutusTx.+ 1
        ||]
    )

fAppliedToBottom :: CompiledCode Integer
fAppliedToBottom = f `unsafeApplyCode` undefined
