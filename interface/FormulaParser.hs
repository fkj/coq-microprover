module FormulaParser where

import Data.Function (fix)
import MicroProver
import FormulaLexer
    ( mParens,
      mReserved,
      mWhiteSpace )
import Text.Parsec
    ( choice,
      eof,
      many1,
      (<?>),
      parse,
      digit,
      ParseError,
      Parsec )

type SParser a = Parsec String () a

-- Parsing of formulas
proposition :: SParser Form
proposition = mReserved "Pro" *> (Pro <$> (read <$> many1 digit))

implication :: SParser Form
implication = fix $ const $ mReserved "Imp" *> (Imp <$> formula <*> formula)

falsity :: SParser Form
falsity = do mReserved "False"
             pure Falsity

formula :: SParser Form
formula = fix allFormulas
  where
    allFormulas _ = choice
      [ proposition
      , implication
      , falsity
      , mParens formula
      ] <?> "a formula"

parser :: String -> Either ParseError Form
parser = parse (mWhiteSpace *> formula <* eof) ""
