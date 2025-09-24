import LeanCats.Syntax
import LeanCats.Relations
import LeanCats.Data

namespace CatSemantics
open CatGrammar

scoped syntax "[expr|" expr "]" : term
scoped syntax "[keyword|" keyword "]" : term
scoped syntax "[inst|" inst "]" : command
scoped syntax "[model|" command* "]" : model
scoped syntax "[assertion|" assertion "]" : term
scoped syntax "[annotable-events|" annotable_events "]" : term -- Set
scoped syntax "[predefined-events|" predefined_events "]" : term

scoped syntax "[predefined-relations]" predefined_relations "]" : term

scoped macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) => `(Event.union [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr & $e₂:expr]) => `(Event.inter [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr ; $e₂:expr]) => `(Event.sequence [expr| $e₁] [expr| $e₂])
  | `([expr| $k:keyword ]) => `([keyword| $k])

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
  | `([annotable-events| W]) => `(λ E: CandidateExecution ↦ E.evts.W)
  | `([annotable-events| R]) => `(λ E: CandidateExecution ↦ E.evts.R)
  | `([annotable-events| B]) => `(λ E: CandidateExecution ↦ E.evts.B)
  | `([annotable-events| F]) => `(λ E: CandidateExecution ↦ E.evts.F)
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
scoped postfix:61 "+" => Relation.TransGen
scoped postfix:61 "^-1" => Rel.inv

-- postfix:61 "?" => Relation: Identity closure.

-- theorem test123 :
--   ∀E : CandidateExecution, IsEmpty E.evts.B :=
--   by
--     intro E

end CatSemantics
