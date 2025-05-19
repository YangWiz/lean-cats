import Init.System.IO
import LeanCats.CatParser
import Lean

-- def get_file(path: System.FilePath) : IO String := do
--   let file <- IO.FS.readFile path
--   sorry

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

def prog :=
  let a = amo | amo
  acyclic a

#reduce prog

def prog₁ :=
  "let com = rf | fr | co
  acyclic po | com"

set_option diagnostics true
#eval (eval_string prog₁)

-- The good news is that the Lean4 is functional programming language, so everything is (alomost) immutable,
-- We don't need to care if the variable is changed after passing it.

-- The strictness of models is defined as, for two different models m₁ and m₂, if the number of accepted
-- program in m₁ is larger than the in m₂, we say m₁ is stronger than m₂: we write it as m₁ > m₂.
-- We use "ayclic relations" to define the disallowed beheviours, so we need to define what's a acyclic.
-- We define acyclic as: ¬(∃x.(x, x) ∈ r+), like in the sc example, we have acyclic po | com, which means,
-- We will omit all the other possible relations contain cyclic, in this step, we need computation.
-- Because some relations are dependent on other relations, we want to check if there is any possiblities that
-- we can find if m₁ is stronger than m₂ without computation.
-- Start with the simplist one acyclic po. We know po does't acyclic, so we have our first lemma:

-- We define program order as (e.linenumber < e.linenumber && e.thread_id == e.thread_id)
-- we define cohenrence order as (e.w.target == e.w.target)
