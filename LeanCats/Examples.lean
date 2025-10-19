import LeanCats.Data
import LeanCats.Relations

namespace SC
variable (evts : Data.Events)
variable (co : Rel Data.Event Data.Event)

def X : Data.CandidateExecution :=
  {
    evts := evts
    po := Data.Rel.po
    fr := Data.Rel.fr co
    rf := Data.Rel.rf
    IW := evts.IW
  }

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
Sequential Consistency is a memory model where the result of any execution is the same
as if the operations of all threads were executed in some single sequential order,
and the operations of each individual thread appear in this sequence in the order
specified by its program.-/

-- We define the communication between threads as com:
@[simp] def com := CatRel.union (X evts co).rf (CatRel.union co (X evts co).fr)

-- Then we union it with the po, the SC ensures that every instructions are executed in program order.
@[simp] def sc := CatRel.union (com evts co) ((X evts co).po)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := CatRel.Acyclic (sc evts co)

end SC

namespace TSO01
variable (evts : Data.Events)

def X : Data.CandidateExecution :=
  {
    evts := evts
    po := Data.Rel.po
    co := Data.Rel.co
    rf := Data.Rel.rf
    IW := evts.IW
  }

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
A TSO is a memory model that allows the write read out of order in the same thread (write buffer).-/

-- We define the communication between threads as com as in SC:
@[simp] def fr := CatRel.sequence (Rel.inv (X evts).rf) ((X evts).co)
@[simp] def com := CatRel.union (CatRel.external ∪ (X evts).rf) ((X evts).co ∪ (fr evts))

-- Then we minus the internal read from and W*R from the po, because we allow them to be out of order.
@[simp] def po_tso := (X evts).po ∩ ((CatRel.prod CatRel.W CatRel.W) ∪ (CatRel.prod CatRel.R CatRel.M))

@[simp] def ghb := (po_tso evts) ∪ (com evts)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := CatRel.Acyclic (ghb evts)

end TSO01

-- The set of accepted candidate executions of SC is the subset of the TSO, because SC rejected more than TSO.
-- Which means sc imples tso, the sc is stronger.
-- In this case, if we find the ghb is acyclic then tso must also be acyclic because sc models more edges.

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsIrrefl
theorem scvtso : ∀evts : Data.Events, SC.assert evts → TSO01.assert evts :=
by
  intro evts
  intro sc
  simp
  sorry
