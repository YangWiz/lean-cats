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

instance : Coe (TSyntax `cat_ident) (TSyntax `ident) where
  -- Urgly hack.
  coe s :=
  if s.raw.getKind.getString! == "cat_ident_" then
    ⟨s.raw.getArg 0⟩
  else if s.raw.getKind.getString! == "cat_ident_-_" then
    let l : TSyntax `ident := ⟨s.raw.getArg 0⟩
    let r : TSyntax `ident := ⟨s.raw.getArg 2⟩
    mkIdent (l.getId.toString ++ r.getId.toString).toName
  else
    panic! "Failed to converses the cat_ident to ident"

macro_rules
  | `([expr| $e₁:expr | $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.union ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr & $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.inter ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr ; $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      Rel.comp ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e₁:expr * $e₂:expr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.prod ([expr| $e₁] evts X) ([expr| $e₂] evts X))

  | `([expr| $e^-1]) =>
    `(fun X : CandidateExecution => Rel.inv ([expr| $e] X))

  | `([expr| $r:reserved]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [reserved| $r] evts X)

  | `([expr| ($e:expr)]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [expr| $e] evts X)

  | `([expr| $t:dsl_term]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      [dsl-term| $t] evts X)

#check Ident

-- macro_rules
--   | `([cat-ident| $i:ident]) => `($i)
--   | `([cat-ident| $i₁:ident-$i₂:ident]) =>
--     let n₁ := i₁.getId
--     let n₂ := i₂.getId
--     let n := n₁.getString! ++ "_" ++ n₂.getString!
--     let n := mkIdent n.toName
--     `($n)

macro_rules
  | `([dsl-term| $i:cat_ident]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) =>
      $i evts X)

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
  | `([assertion| irreflexive]) => `(CatRel.Irreflexive)
  | `([assertion| acyclic]) => `(CatRel.Acyclic)
  | `([assertion| empty]) => `(CatRel.IsEmpty)

macro_rules
  | `([annotable-events| W]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.W)
  | `([annotable-events| R]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.R)
  | `([annotable-events| B]) => `(fun X : CandidateExecution => X.evts.B)
  | `([annotable-events| F]) => `(fun X : CandidateExecution => X.evts.F)

macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.IW)

  | `([predefined-events| M]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
      => X.evts.W ∪ X.evts.R)

  | `([predefined-events| $a:annotable_events]) => `([annotable-events| $a])


macro_rules
  -- We just ignore the include inst.
  | `([inst| include $_filename:str]) => return mkNullNode
  -- TODO(Don't know how the coe works here, maybe ask others? Like the coe works, okay, but how do I know it's value?)
  | `([inst| let $nm:cat_ident = $e]) =>
    `(def $nm := [expr|$e])
  | `([inst| $a:assertion $e as $nm:cat_ident]) => do

    dbg_trace <- `($nm)

    match nm with
    | t =>
      let a := t.raw
      dbg_trace a.getArgs
      dbg_trace a.getKind.getString!
      dbg_trace "failed to match"
      dbg_trace t
      pure ()

    dbg_trace nm
    dbg_trace a
    dbg_trace e

    `(def $nm (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts) : Prop
      := [assertion| $a] ([expr| $e] evts X))
  -- | `([inst| (* $_ *)]) => `(#print "")

macro_rules
  -- Create the model.
  | `([model| $n:ident $x:inst*]) => do
    let nstart <- `(namespace $n)
    let nend <- `(end $n)
    let insts <- x.mapM (fun ins => `([inst| $ins]))

    -- let insts : Array (TSyntax `command) := #[]
    let ret := #[nstart] ++ insts ++ #[nend]
    return mkNullNode ret

postfix:61 "+" => Relation.TransGen

[inst|
  -- let e = (po | po | po) & po
  acyclic po as new
]

#check new

namespace t₁
def a := 1
end t₁

#check t₁.a

[inst| include "test"]

[inst| let b-c = po]
--
-- #check test.e
