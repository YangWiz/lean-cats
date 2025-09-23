import LeanCats.Syntax
import LeanCats.Relations
import LeanCats.Data

namespace Cats

syntax "[expr|" expr "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[inst|" inst "]" : command
syntax "[model|" command* "]" : model
syntax "[assertion|" assertion "]" : term
syntax "[annotable-events|" annotable_events "]" : term -- Set
syntax "[predefined-events|" predefined_events "]" : term

macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) => `(Event.union [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr & $e₂:expr]) => `(Event.inter [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr ; $e₂:expr]) => `(Event.sequence [expr| $e₁] [expr| $e₂])
  | `([expr| $k:keyword ]) => `([keyword| $k])

macro_rules
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

macro_rules
  | `([assertion| irreflexive]) => `(Irreflexive)
  | `([assertion| acyclic]) => `(Acyclic)
  | `([assertion| empty]) => `(IsEmpty)

-- macro_rules
--   | `([annotable-events| W]) => _

macro_rules
  | `([inst| let $nm = $e]) => `(def $nm := [expr|$e])
  | `([inst| $a:assertion $e as $nm]) => `(def $nm : Prop := [assertion| $a] [expr| $e])
  -- | `([inst| (* $_ *)]) => `(#print "")

-- The value of expr 2 must be a set of values S and the operator returns the set S augmented with the value of expr 1.
-- The cat specification didn't give us the precedence, so we use the Ocaml as the reference.
infixl:61 " ++ " => Set.insert

-- Cartesian product.
infixl:61 " * " => Set.prod

infixl:61 " | " => Set.union

infixl:61 " & " => Set.inter

infixl:61 " ; " => Rel.comp

postfix:61 "*" => Relation.ReflTransGen

postfix:61 "+" => Relation.TransGen

postfix:61 "^-1" => Rel.inv

end Cats

-- theorem test123 :
--   ∀E : CandidateExecution, IsEmpty E.evts.B :=
--   by
--     intro E
