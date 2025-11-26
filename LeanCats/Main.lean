import Lean
import LeanCats.Macro
import LeanCats.Syntax

open Lean.Meta Lean Expr Elab Command Parser

def eval_string (s : String) : Lean.Elab.Command.CommandElabM Unit := do
  -- parse the string using the current environment
  let env: Lean.Environment <- Lean.getEnv
  let stx?: Except String Lean.Syntax := Lean.Parser.runParserCategory env `command s "<CatFile>"
  let stx : Lean.Syntax <- Lean.ofExcept stx?

  -- We call this function to expand the macro using the Cat macro.
  let catStx <- Lean.Elab.liftMacroM (Lean.Macro.expandMacro? stx)

  match catStx with
  | some stx => {
    Lean.Elab.Command.elabCommand stx
  }
  | none => {
    pure ()
  }

elab "defcat" name:ident " := " "<" filename:str ">" : command => do
    -- Add the declaration to the environment
    eval_string "[model| sc let a = po]"

defcat TSO := <"Cats/tso.cat">

#check sc.a

#check _
