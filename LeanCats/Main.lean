import Init.System.IO
import Lean
import LeanCats.CatParser

-- This function is copied from Jason Rute on StackExchange
-- https://proofassistants.stackexchange.com/questions/4873/how-to-parse-the-content-of-a-string-as-lean-4-code
def parse (file : String) : Lean.MetaM Lean.Expr := do
  let s <- IO.FS.readFile file

  -- parse the string using the current environment
  let env: Lean.Environment <- Lean.getEnv
  let stx?: Except String Lean.Syntax := Lean.Parser.runParserCategory env `model s
  let stx : Lean.Syntax <- Lean.ofExcept stx?

  mkModel stx

def t := parse "LeanCats/tso-00.cat"

#eval parse "LeanCats/tso-00.cat"

#eval t
