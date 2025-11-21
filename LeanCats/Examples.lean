import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theoriems
import LeanCats.Basic
import LeanCats.Macro

open CatRel
open Data

namespace SC
variable (evts : Data.Events)
variable (coConst : IsStrictTotalOrder Event (preCo evts))

@[simp] def X : CandidateExecution :=
  {
    evts := evts
    po := CatRel.po evts
    fr := CatRel.fr evts
    rf := CatRel.rf.wellformed evts
    IW := evts.IW
  }

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
Sequential Consistency is a memory model where the result of any execution is the same
as if the operations of all threads were executed in some single sequential order,
and the operations of each individual thread appear in this sequence in the order
specified by its program.-/

-- We define the communication between threads as com:
@[simp] def com := (X evts coConst).rf ∪ ((co.wellformed evts) ∪ (X evts coConst).fr)

-- Then we union it with the po, the SC ensures that every instructions are executed in program order.
@[simp] def sc := (com evts coConst) ∪ ((X evts coConst).po)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := Acyclic (sc evts coConst)

end SC

namespace TSO01
variable (evts : Events)
variable (coConst : IsStrictTotalOrder Event (preCo evts))

@[simp] def X : CandidateExecution :=
  {
    evts := evts
    po := CatRel.po evts
    fr := CatRel.fr evts
    rf := CatRel.rf.wellformed evts
    IW := evts.IW
  }

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
A TSO is a memory model that allows the write read out of order in the same thread (write buffer).-/

-- We define the communication between threads as com as in SC:
@[simp] def com := (external evts ∩ (X evts coConst).rf) ∪ (co.wellformed evts ∪ ((X evts coConst).fr))

-- Then we minus the internal read from and W*R from the po, because we allow them to be out of order.
@[simp] def po_tso := (X evts coConst).po ∩ ((prod W W) ∪ (prod R M))

@[simp] def ghb := (po_tso evts coConst) ∪ (com evts coConst)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := Acyclic (ghb evts coConst)

end TSO01

-- The set of accepted candidate executions of SC is the subset of the TSO, because SC rejected more than TSO.
-- Which means sc imples tso, the sc is stronger.
-- In this case, if we find the ghb is acyclic then tso must also be acyclic because sc models more edges.

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsIrrefl
theorem scvtso
  (evts : Data.Events)
  [coConst : IsStrictTotalOrder Event (preCo evts)]
  : SC.assert evts coConst → TSO01.assert evts coConst :=
by
  simp
  intro sc
  apply ayclicMono sc
  intro a b
  intro tso
  cases tso with
  | inl h => {
    simp at h
    apply Or.inr
    obtain ⟨l, r⟩ := h
    exact l
  }
  | inr h => {
    obtain ⟨l⟩ := h
    {
      apply Or.inl
      apply Or.inl
      obtain ⟨l, r⟩ := l
      exact r
    }
    {
      rename_i h
      apply Or.inl
      apply Or.inr
      exact h
    }
  }

-- Automated loading of memory model.
-- Let's define the sc in the cat langague model instead of writing it explicitly.
section Example1
open CatGrammar

end Example1
