import LeanCats.Data
import LeanCats.Relations

namespace SC
variable (X : Data.CandidateExecution)

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
Sequential Consistency is a memory model where the result of any execution is the same
as if the operations of all threads were executed in some single sequential order,
and the operations of each individual thread appear in this sequence in the order
specified by its program.-/

-- We define the communication between threads as com:
@[simp] def fr := CatRel.sequence (Rel.inv X.rf) (X.co)
@[simp] def com := CatRel.union X.rf (CatRel.union X.co (fr X))

-- Then we union it with the po, the SC ensures that every instructions are executed in program order.
@[simp] def sc := CatRel.union (com X) (X.po)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := CatRel.Acyclic (sc X)

end SC

namespace TSO01
variable (X : Data.CandidateExecution)

/-! ### SC (Sequential Consistency) model reperesentation in Lean 4.
A TSO is a memory model that allows the write read out of order in the same thread (write buffer).-/

-- We define the communication between threads as com as in SC:
@[simp] def fr := CatRel.sequence (Rel.inv X.rf) (X.co)
@[simp] def com := CatRel.union (CatRel.external ∪ X.rf) (X.co ∪ (fr X))

-- Then we minus the internal read from and W*R from the po, because we allow them to be out of order.
@[simp] def po_tso := X.po ∩ ((CatRel.prod CatRel.W CatRel.W) ∪ (CatRel.prod CatRel.R CatRel.M))

@[simp] def ghb := (po_tso X) ∪ (com X)

-- We should avoid the cyclic, because the fr in a ghb will leads a overwritten that violates the program order.
@[simp] def assert := CatRel.Acyclic (ghb X)

end TSO01

-- The set of accepted candidate executions of SC is the subset of the TSO, because SC rejected more than TSO.
-- Which means sc imples tso, the sc is stronger.
-- In this case, if we find the ghb is acyclic then tso must also be acyclic because sc models more edges.
theorem scvtso : ∀X : Data.CandidateExecution, SC.assert X → TSO01.assert X :=
by
  intro X
  intro sc
  simp at *
  sorry
