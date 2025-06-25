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

def prog₁ :=
  "let com = rf
  acyclic po | com"

def t := parse "LeanCats/tso-00.cat"

#eval parse "LeanCats/tso-00.cat"

#eval t

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
