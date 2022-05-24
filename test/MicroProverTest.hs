module Main (main) where

import System.Exit ( exitFailure
                   , exitSuccess)
import MicroProver

main :: IO ()
main =
  if prover (Imp (Pro 0) (Pro 0))
  && prover (Imp (Pro 999) (Pro 999))
  && prover (Imp Falsity Falsity)
  && prover (Imp (Imp (Imp (Pro 0) (Pro 1)) (Pro 0)) (Pro 0))
  && prover (Imp (Pro 0) (Imp (Imp (Pro 0) (Pro 1)) (Pro 1)))
  && prover (Imp (Pro 0) (Imp (Pro 1) (Imp (Pro 1) (Pro 0))))
  && prover (Imp (Pro 0) (Imp (Imp (Pro 0) Falsity) Falsity))
  && prover (Imp Falsity (Pro 0))
  && prover (Imp (Pro 0) (Imp (Imp (Pro 0) Falsity) Falsity))
  && not (prover Falsity)
  && not (prover (Imp (Pro 0) (Pro 1)))
  && not (prover (Imp (Imp (Pro 1) (Pro 2)) (Pro 2)))
  && not (prover (Imp (Pro 0) Falsity))
  then exitSuccess
  else exitFailure
