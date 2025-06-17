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

private structure CandidateExcution where
  (E : List Event)
  (po : Rel Event Event)
  (rf : Rel Event Event)
  (co : Rel Event Event)

-- User provided data
-- E: List of events [e₁, e₂ ... ]
-- po : [(e₁, e₂), (e₂, e₃) ...]
-- rf : [(e₃, e₄), (e₄, e₅) ...]
-- co : [(e₁, e₂) ...]

-- Then we store these values into candidate.
-- We will check if the users inputs are valid first.
def mkExcution
  (E : List Event)
  (po : List (Event × Event))
  (rf : List (Event × Event))
  (co : List (Event × Event))
  : Option CandidateExcution :=
  if po.Nodup ∧ rf.Nodup ∧ co.Nodup
  then
    let po_rel := λ a b ↦ (a, b) ∈ po
    let rf_rel := λ a b ↦ (a, b) ∈ rf
    let co_rel := λ a b ↦ (a, b) ∈ co
    CandidateExcution.mk E po_rel rf_rel co_rel
  else
    none
