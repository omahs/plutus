{-# LANGUAGE BangPatterns #-}
module Main where

import Common
import Control.DeepSeq (force)
import Control.Exception
import Criterion
import PlutusBenchmark.Common
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Bytecode as B

main :: IO ()
main = do
  let mkBcBM file program =
          -- don't count the undebruijn . unflat cost
          -- `force` to try to ensure that deserialiation is not included in benchmarking time.
          let
              (MachineParameters !costs !runtime) = B.defaultBCParameters
              t = toNamedDeBruijnTerm . UPLC._progTerm $ unsafeUnflat file program
              !benchTerm =
                force $ B.termToInstrs True True costs $ UPLC.termMapNames unNameDeBruijn t
              eval dbt =
                  let (res, _, _) = B.runBC runtime B.restrictingEnormous B.noEmitter dbt
                  in either (error . show) (\_ -> ()) res
          in whnf eval benchTerm
  benchWith mkBcBM
