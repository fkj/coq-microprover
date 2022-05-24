module Main where

import Options.Applicative
    ( (<**>),
      argument,
      fullDesc,
      header,
      help,
      info,
      metavar,
      progDesc,
      str,
      execParser,
      helper,
      Parser )
import MicroProver
import FormulaParser

data Arguments = Arguments
  { formula :: String
  }

arguments :: Parser Arguments
arguments = Arguments
            <$> argument str (metavar "FORMULA" <> help "Formula to check")

main :: IO ()
main = run =<< execParser opts
  where
    opts = info (arguments <**> helper)
      ( fullDesc
      <> progDesc "Prove or disprove the propositional formula FORMULA"
      <> header "secav-prover - a prover for SeCaV" )

run :: Arguments -> IO ()
run (Arguments s) =
  case parser s of
    Left e -> print e
    Right f -> print $ prover f
