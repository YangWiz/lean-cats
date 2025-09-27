import LeanCats.Syntax
import LeanCats.Relations
import LeanCats.Data

namespace CatSemantics
open CatGrammar
open Data

variable (X : CandidateExecution)

variable (fr_var : Rel Event Event)
variable (co_var : Rel Event Event)

scoped syntax "[expr|" expr "]" : term
scoped syntax "[keyword|" keyword "]" : term
scoped syntax "[assertion|" assertion "]" : term

scoped syntax "[inst|" inst "]" : command
scoped syntax "[model|inst" name command* "]" : model
scoped syntax "[annotable-events|" annotable_events "]" : term -- Set
scoped syntax "[predefined-events|" predefined_events "]" : term
scoped syntax "[reserved|" reserved "]" : term
scoped syntax "[predefined-relations|" predefined_relations "]" : term
scoped syntax "[dsl-term|" dsl_term "]" : term

scoped macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) => `(CatRel.union [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr & $e₂:expr]) => `(CatRel.inter [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr ; $e₂:expr]) => `(Rel.comp [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr * $e₂:expr]) => `(Set.prod [expr| $e₁] [expr| $e₂])
  | `([expr| $e^-1]) => `(Rel.inv [expr| $e])
  | `([expr| $r:reserved]) => `([reserved| $r])
  | `([expr| $t:dsl_term]) => `([dsl-term| $t]) -- environemnt identifiers ρ, introduced by commands.

scoped macro_rules
  | `([dsl-term| $i:ident]) => `($i X) -- Apply the variable X to identifier, otherwise the type signature will has a extra type (CandidateExecution).

scoped macro_rules
  | `([reserved| $r:predefined_relations]) => `([predefined-relations| $r])

scoped macro_rules
  | `([predefined-relations| co]) => `(X.co)
  | `([predefined-relations| po]) => `(X.po)
  | `([predefined-relations| rf]) => `(X.rf)

scoped macro_rules
  | `([keyword| and]) => Lean.Macro.throwUnsupported
  | `([keyword| as]) => Lean.Macro.throwUnsupported
  | `([keyword| begin]) => Lean.Macro.throwUnsupported
  | `([keyword| call]) => Lean.Macro.throwUnsupported
  | `([keyword| do]) => Lean.Macro.throwUnsupported
  | `([keyword| end]) => Lean.Macro.throwUnsupported
  | `([keyword| enum]) => Lean.Macro.throwUnsupported
  | `([keyword| flag]) => Lean.Macro.throwUnsupported
  | `([keyword| forall]) => Lean.Macro.throwUnsupported
  | `([keyword| from]) => Lean.Macro.throwUnsupported
  | `([keyword| fun]) => Lean.Macro.throwUnsupported
  | `([keyword| in]) => Lean.Macro.throwUnsupported
  | `([keyword| instructions]) => Lean.Macro.throwUnsupported
  | `([keyword| let]) => Lean.Macro.throwUnsupported
  | `([keyword| match]) => Lean.Macro.throwUnsupported
  | `([keyword| procedure]) => Lean.Macro.throwUnsupported
  | `([keyword| rec]) => Lean.Macro.throwUnsupported
  | `([keyword| scopes]) => Lean.Macro.throwUnsupported
  | `([keyword| with]) => Lean.Macro.throwUnsupported
  | `([keyword| $a:assertion]) => `([assertion| $a])

scoped macro_rules
  | `([assertion| irreflexive]) => `(Irreflexive)
  | `([assertion| acyclic]) => `(Acyclic)
  | `([assertion| empty]) => `(IsEmpty)

scoped macro_rules
  | `([annotable-events| W]) => `(X.evts.W)
  | `([annotable-events| R]) => `(X.evts.R)
  | `([annotable-events| B]) => `(X.evts.B)
  | `([annotable-events| F]) => `(X.evts.F)
  -- | `([annotable-events| W]) => `(λ E: CandidateExecution ↦ E.evts)

scoped macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW]) => `(λ E: CandidateExecution ↦ E.evts.IW)
  | `([predefined-events| M]) => `(λ E: CandidateExecution ↦ E.evts.W ∪ E.evts.R)
  | `([predefined-events| $a:annotable_events]) => `([annotable-events| $a])

scoped macro_rules
  | `([inst| let $nm = $e]) => `(def $nm := [expr|$e])
  | `([inst| $a:assertion $e as $nm]) => `(def $nm : Prop := [assertion| $a] [expr| $e])
  -- | `([inst| (* $_ *)]) => `(#print "")

-- The value of expr 2 must be a set of values S and the operator returns the set S augmented with the value of expr 1.
-- The cat specification didn't give us the precedence, so we use the Ocaml as the reference.
scoped infixl:61 " ++ " => Set.insert

scoped infixl:61 " * " => Set.prod

scoped infixl:61 " | " => Set.union

scoped infixl:61 " & " => Set.inter

scoped infixl:61 " ; " => Rel.comp

scoped postfix:61 "*" => Relation.ReflTransGen

-- The macro is bidirective (from left to right and from right to left).
scoped postfix:61 "+" => Relation.TransGen

def test₁ : Rel Event Event := X.co

#check test₁

#check (test₁ X)

[inst| let fr = rf^-1 ; co]
[inst| let com = rf | co | fr]
-- [inst| let poo = W*W]
[inst| let ghb = po | com]
-- [assertion| acyclic ghb]

#check fr

end CatSemantics
