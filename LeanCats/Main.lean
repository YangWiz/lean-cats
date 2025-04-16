import Init.System.IO
import LeanCats.CatParser
import Lean

def get_file(path: System.FilePath) : IO String := do
  let file <- IO.FS.readFile path
  sorry

-- This function is copied from Jason Rute on StackExchange
-- https://proofassistants.stackexchange.com/questions/4873/how-to-parse-the-content-of-a-string-as-lean-4-code
unsafe def eval_string (s : String) : Lean.Elab.TermElabM String := do
  -- this make the string into an expression which is of type string
  let s := "(toString (" ++ s ++ ") : String)"

  -- parse the string using the current environment
  let env: Lean.Environment <- Lean.getEnv
  let stx?: Except String Lean.Syntax := Lean.Parser.runParserCategory env `term s
  let stx : Lean.Syntax <- Lean.ofExcept stx?

  -- elaborate the type of the expression
  let tp : Lean.Expr <- Lean.Elab.Term.elabTypeOf stx none

  -- evaluate the expression and return result
  let x <- Lean.Elab.Term.evalTerm String tp stx (safety := Lean.DefinitionSafety.unsafe)
  return x

#eval eval_string "(1: Nat) + 1"
