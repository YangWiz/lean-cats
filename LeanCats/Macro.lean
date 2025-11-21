import LeanCats.Syntax
import Lean
import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic

namespace CatSemantics
open Lean Elab Command
open Data

variable (evts : Data.Events)
variable (coConst : IsStrictTotalOrder Event (CatRel.preCo evts))

@[simp] def X : CandidateExecution :=
  {
    evts := evts
    po := CatRel.po evts
    fr := CatRel.fr evts
    rf := CatRel.rf.wellformed evts
    IW := evts.IW
  }

open CatGrammar

scoped syntax "[expr|" expr "]" : term
scoped syntax "[keyword|" keyword "]" : term
scoped syntax "[assertion|" assertion "]" : term

scoped syntax "[inst|" inst "]" : command
scoped syntax (name := model) "[model|" ident command* "]" : command
scoped syntax "[commands|" command* "]" : command
scoped syntax "[annotable-events|" annotable_events "]" : term -- Set
scoped syntax "[predefined-events|" predefined_events "]" : term
scoped syntax "[reserved|" reserved "]" : term
scoped syntax "[predefined-relations|" predefined_relations "]" : term
scoped syntax "[dsl-term|" dsl_term "]" : term

@[command_elab model] def modelElabHelper : CommandElab := fun stx =>
  -- The idea is we use the macro to reduce the syntax first,
  -- then we can use this elaborator to close the namespace.
  match stx with
  | `([model| $n:ident $cmds:command*]) => do
    -- First we create the namespace.
    let addName : TSyntax `command <- `(namespace $n)
    elabNamespace addName

    -- Then we introduce a bunch of variables for our models.
    let evtsVar : TSyntax `command <- `(variable (evts : Data.Events))
    let coConst : TSyntax `command <- `(variable (coConst : IsStrictTotalOrder Event (CatRel.preCo evts)))
    elabVariable evtsVar
    elabVariable coConst

    -- Then we iterate all the commands one by one.
    cmds.forM (fun cmd => elabCommand cmd)
    let endName : TSyntax `command <- `(end $n)
    elabEnd endName
  | _ => throwUnsupportedSyntax

scoped macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) => `(CatRel.union [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr & $e₂:expr]) => `(CatRel.inter [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr ; $e₂:expr]) => `(Rel.comp [expr| $e₁] [expr| $e₂])
  | `([expr| $e₁:expr * $e₂:expr]) => `(Set.prod [expr| $e₁] [expr| $e₂])
  | `([expr| $e^-1]) => `(Rel.inv [expr| $e])
  | `([expr| $r:reserved]) => `([reserved| $r])
  | `([expr| $t:dsl_term]) => `([dsl-term| $t]) -- environemnt identifiers ρ, introduced by commands.

scoped macro_rules
  | `([dsl-term| $i:ident]) => `($i evts coConst) -- Apply the variable X to identifier, otherwise the type signature will has a extra type (CandidateExecution).

scoped macro_rules
  | `([reserved| $r:predefined_relations]) => `([predefined-relations| $r])
  | `([reserved| $e:predefined_events]) => `([predefined-events| $e])

scoped macro_rules
  | `([predefined-relations| fr]) => `((X evts coConst).fr)
  | `([predefined-relations| po]) => `((X evts coConst).po)
  | `([predefined-relations| rf]) => `((X evts coConst).rf)

scoped macro_rules
  | `([predefined-events| W]) => `((X evts coConst).evts.W)

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
  | `([annotable-events| W]) => `((X evts coConst).evts.W)
  | `([annotable-events| R]) => `((X evts coConst).evts.R)
  | `([annotable-events| B]) => `((X evts coConst).evts.B)
  | `([annotable-events| F]) => `((X evts coConst).evts.F)
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

scoped infixl:61 " ∪ " => CatRel.union

scoped postfix:61 "*" => Relation.ReflTransGen

-- The macro is bidirective (from left to right and from right to left).
scoped postfix:61 "+" => Relation.TransGen

[model| res def a := 1]

#check res.a

[inst| let a = po]

#check a

end CatSemantics

open scoped CatSemantics
open scoped CatGrammar
