import Init.Data.List
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Primitives

inductive Thread : Type where
  | mk: Nat -> Thread

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
  value : Option String

/-
-/
structure Event where
  (id : String)   -- Unique identifier
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (ln : Nat)        -- Line number or position
  (a : Action) -- Action performed

structure Event₁ where
  po : ℕ
  rf : ℕ
  fr : ℕ

-- We define program order as (e.linenumber < e.linenumber && e.thread_id == e.thread_id)
-- we define cohenrence order as (e.w.target == e.w.target)
def po_rel (e₁ e₂ : Event) : Prop := e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id

-- From write to read.
def rf_rel (e₁ e₂ : Event) : Prop := e₁.a.action == write ∧ e₂.a.action == read ∧ (e₁.a.target == e₂.a.target)

-- def data_dependency (e₁ e₂ : Event) : Prop :=

-- coherence order: successive writes to the same location, if they're in the same thread we need to maintain data-dependency order,
-- which means the co follows the program order, if they're in different thread, we don't care the line number.
-- The coherence order gives the order in which all the memory writes to a given location have hit that location in memory
-- In this article: https://diy.inria.fr/doc/herd.html#note11, they defined how to calculate the cohenrence orders,
-- but due to the time limitation, we need to reduce the complexities, by just introduce the init write,
-- and also we'are in the compiler level, we don't need to calculate it using lib,
def co_rel (e₁ e₂ : Event) : Prop :=
  e₁.a.action == write ∧ e₂.a.action == write ∧ e₁.a.target == e₂.a.target ∧
  ((e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id) ∨ (e₁.t_id ≠ e₂.t_id))

def trans : Set (Event × Event) → Set (Event × Event) :=
  fun r => { p | Relation.TransGen (fun a b => (a, b) ∈ r) p.1 p.2 }

-- Step 1: Control flow semantics
def po : Set (Event × Event) := {(a, b) | po_rel a b}

-- Step 2: Data flow semantics
-- The read-from relation rf describes, for any given read, from which write this read could have taken its value.
-- This will give us many possible results for each read event (Wⁿ -> R).
def rf.all_candidates : Set (Event × Event) := {(a, b) | rf_rel a b}

-- TODO(Zhiyang): Verify if this definition is correct.
-- Find all the candidates for a specific event.
def rf (e : Event) : Set (Event × Event) := {(a, b) | b.id == e.id ∧ rf_rel a b}

-- def rf (e : Event) : Set (Event × Event) := {(a, b) | b.id == e.id } ∩ rf.all_candidates

-- For each event, they may have one or more candidate

end Primitives
