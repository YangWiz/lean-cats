import LeanCats.Syntax
import Lean
import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic

open Lean Elab Command Term Meta
open Data

syntax "[model|" ident inst* "]" : command
syntax "[expr|" expr "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term

syntax "[inst|" inst "]" : command
syntax "[annotable-events|" annotable_events "]" : term -- Set
syntax "[predefined-events|" predefined_events "]" : term
syntax "[reserved|" reserved "]" : term
syntax "[predefined-relations|" predefined_relations "]" : term
syntax "[dsl-term|" dsl_term "]" : term

macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.union ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr & $e₂:expr]) =>
    `(fun X : CandidateExecution => CatRel.inter ([expr| $e₁] X) ([expr| $e₂] X))

  | `([expr| $e₁:expr ; $e₂:expr]) =>
    `(fun X : CandidateExecution => Rel.comp ([expr| $e₁] X) ([expr| $e₂] X))

  | `([expr| $e₁:expr * $e₂:expr]) =>
    `(fun X : CandidateExecution => Set.prod ([expr| $e₁] X) ([expr| $e₂] X))

  | `([expr| $e^-1]) =>
    `(fun X : CandidateExecution => Rel.inv ([expr| $e] X))

  | `([expr| $r:reserved]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [reserved| $r] evts X)

  | `([expr| $t:dsl_term]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) => [dsl-term| $t] evts X)

macro_rules
  | `([dsl-term| $i:ident]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) => $i evts X)

macro_rules
  | `([reserved| $r:predefined_relations]) => `([predefined-relations| $r])
  | `([reserved| $e:predefined_events]) => `([predefined-events| $e])

-- #check fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
--   X._rf

macro_rules
  | `([predefined-relations| fr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._fr)

  | `([predefined-relations| po]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._po)

  | `([predefined-relations| rf]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._rf)

  | `([predefined-relations| co]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.co.wellformed evts)

macro_rules
  | `([predefined-events| W]) => `((X evts coConst).evts.W)

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

macro_rules
  | `([annotable-events| W]) => `(fun X : CandidateExecution => X.evts.W)
  | `([annotable-events| R]) => `(fun X : CandidateExecution => X.evts.R)
  | `([annotable-events| B]) => `(fun X : CandidateExecution => X.evts.B)
  | `([annotable-events| F]) => `(fun X : CandidateExecution => X.evts.F)

macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW]) => `(λ E: CandidateExecution ↦ E.evts.IW)
  | `([predefined-events| M]) => `(λ E: CandidateExecution ↦ E.evts.W ∪ E.evts.R)
  | `([predefined-events| $a:annotable_events]) => `([annotable-events| $a])

macro_rules
  | `([inst| let $nm = $e]) => `(def $nm := [expr|$e])
  | `([inst| $a:assertion $e as $nm]) => `(def $nm : Prop := [assertion| $a] [expr| $e])
  -- | `([inst| (* $_ *)]) => `(#print "")

macro_rules
  -- Create the model.
  | `([model| $n:ident $x:inst*]) => do
    let nstart <- `(namespace $n)
    let nend <- `(end $n)
    let insts <- x.mapM (fun ins => `([inst| $ins]))
    let ret := #[nstart] ++ insts ++ #[nend]
    return mkNullNode ret

postfix:61 "+" => Relation.TransGen

def a := [predefined-relations| po]
def b := [predefined-relations| rf]
def c := [predefined-relations| co]

#check b

[model| test
  let b = po
  let c = po
  let e = b | c
]

#check test.e
--
-- #check test.e
