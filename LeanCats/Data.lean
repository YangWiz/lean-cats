import Mathlib.Data.Rel

inductive Thread : Type where
  | mk: Nat -> Thread
deriving BEq, Repr, DecidableEq

abbrev write := "write"
abbrev read := "read"

/-
Actions are of several kinds, which we detail in the course of this article. For now, we
only consider read and write events relative to memory locations. For example, for the
location x, we can have a read of the value 0 noted Rx = 0, or a write of the value 1,
noted Wx = 1. We write proc(e) for the thread holding the event e and addr(e) for its
address, or memory location.
-/
structure Action : Type where
  action : String
  target : String
  -- For read, the value can not be determined at the begining.
  value : Option Nat
  isFirstWrite : Bool
  isFinalWrite : Bool
deriving BEq, Repr, DecidableEq

/-
-/
structure Event where
  (id : String)   -- Unique identifier
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (ln : Nat)        -- Line number or position
  (a : Action) -- Action performed
deriving BEq, Repr, DecidableEq

structure CandidateExecution where
  (E : List Event)
  (po : Rel Event Event)
  (rf : Rel Event Event)
  (co : Rel Event Event)

-- User provided data
-- E: List of events [e₁, e₂ ... ]
-- po : [(e₁, e₂), (e₂, e₃) ...]
-- rf : [(e₃, e₄), (e₄, e₅) ...]
-- co : [(e₁, e₂) ...]

def Rel.empty : Rel Event Event := fun _ _ => False
instance : EmptyCollection (Rel Event Event) := ⟨Rel.empty⟩

namespace CandidateExecution

def empty : CandidateExecution := { E := [], po := Rel.empty, rf := Rel.empty, co := Rel.empty}


def Events (ce : CandidateExecution) : Type :=
  @Set.Elem Event {e | e ∈ ce.E}

def coeRel (ce : CandidateExecution) (r : Rel Event Event) :
  Rel ce.Events ce.Events :=
  fun x y => r x.val y.val

instance {ce : CandidateExecution} :
  Coe (Rel Event Event) (Rel ce.Events ce.Events) :=
  ⟨coeRel ce⟩

structure IsWellFormed (ce : CandidateExecution) where
  poTotal : IsStrictTotalOrder ce.Events (ce.coeRel ce.po)
  -- what else?

def mkExecution
  (E : List Event)
  (po : List (Event × Event))
  (rf : List (Event × Event))
  (co : List (Event × Event))
  : Option CandidateExecution :=
  if po.Nodup ∧ rf.Nodup ∧ co.Nodup
  then
    let po_rel := λ a b ↦ (a, b) ∈ po
    let rf_rel := λ a b ↦ (a, b) ∈ rf
    let co_rel := λ a b ↦ (a, b) ∈ co
    CandidateExecution.mk E po_rel rf_rel co_rel
  else
    none

-- We later prove that this constructor makes well-formed CEs
-- This is not the case right now.
end CandidateExecution
