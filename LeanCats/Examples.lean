import LeanCats.Data
import LeanCats.Relations

open CatRel
open Data

namespace SC
variable (evts : Data.Events)
variable (co : Rel Data.Event Data.Event)


@[simp] def X : Data.CandidateExecution :=
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
@[simp] def com := union (X evts co).rf (union co (X evts co).fr)

-- Then we union it with the po, the SC ensures that every instructions are executed in program order.
@[simp] def sc := union (com evts co) ((X evts co).po)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := Acyclic (sc evts co)

end SC

namespace TSO01
variable (evts : Events)
variable (co : Rel Event Event)

@[simp] def X : CandidateExecution :=
  {
    evts := evts
    po := Data.Rel.po
    fr := Data.Rel.fr co
    rf := Data.Rel.rf
    IW := evts.IW
  }

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
A TSO is a memory model that allows the write read out of order in the same thread (write buffer).-/

-- We define the communication between threads as com as in SC:
@[simp] def com := union (external ∪ (X evts co).rf) (co ∪ ((X evts co).fr))

-- Then we minus the internal read from and W*R from the po, because we allow them to be out of order.
@[simp] def po_tso := (X evts co).po ∩ ((prod W W) ∪ (prod R M))

@[simp] def ghb := (po_tso evts co) ∪ (com evts co)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := Acyclic (ghb evts co)

end TSO01

-- The set of accepted candidate executions of SC is the subset of the TSO, because SC rejected more than TSO.
-- Which means sc imples tso, the sc is stronger.
-- In this case, if we find the ghb is acyclic then tso must also be acyclic because sc models more edges.

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsIrrefl
theorem scvtso (evts : Data.Events) (co : Rel Data.Event Data.Event) : SC.assert evts co → TSO01.assert evts co :=
by
  simp
  intro sc


  sorry
