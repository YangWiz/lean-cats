import Init.Data.List
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel

inductive Thread : Type where
  | mk: Nat -> Thread

/-
Actions are of several kinds, which we detail in the course of this article. For now, we
only consider read and write events relative to memory locations. For example, for the
location x, we can have a read of the value 0 noted Rx = 0, or a write of the value 1,
noted Wx = 1. We write proc(e) for the thread holding the event e and addr(e) for its
address, or memory location.
-/
inductive Action : Type where
  | write : String -> String -> Action
  | read : String -> String -> Action

/-
-/
structure Event :=
  (id : String)   -- Unique identifier
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (ln : Nat)        -- Line number or position
  (a : Action) -- Action performed

structure Event₁ :=
  po : ℕ
  rf : ℕ
  fr : ℕ

def isReadEvent (e : Event) : Prop :=
  sorry

def isWriteEvent (e : Event) : Prop :=
  sorry

-- We define relation as a set.
def R.mk {α : Type} (a b : α) : Set (α × α) := {(a, b)}

def R.add {α : Type} (a b : α) (r : Set (α × α)) := (R.mk a b) ∪ r

def R.empty {α : Type} : Set (α × α) := {}

def R.seq_comp {α : Type} (set₁ set₂ : Set (α × α)) : Set (α × α)
    := { (x, y) | ∃z, (x, z) ∈ set₁ ∧ (z, y) ∈ set₂}

notation (priority := high) r₁ ";" r₂ => R.seq_comp r₁ r₂

-- Define a calculation of cloure in a very inefficient way.
-- def R.closure {α : Type} [DecidableEq α] (set : Set (α × α)) : Set (α × α) :=
--   let iterate (s : Set (α × α)) (a : α) : Set (α × α)  :=
--     let s' := { (x, y) | ∃z, (x, z) ∈ set ∧ (z, y) ∈ set } ∪ s
--     if (∀e, e ∈ s) then s else iterate s'
--   iterate set

/-
We denote the transitive (resp. reflexive-transitive) closure of a relation r as
r+ (resp. r∗).
-/
inductive RStar {α : Type} (set : Set (α × α)) : α → α → Prop
| base {a b : α} : (a, b) ∈ set → RStar set a b
| step {a b c : α} : RStar set a b → RStar set b c → RStar set a c

def TransClosure {α : Type} (set : Set (α × α)) : Set (α × α) :=
  { (a, b) | RStar set a b }

#check {} = {}

def r₁ := R.mk 1 2
def r₂ := R.add 2 3 r₁
def r₃ := R.add 4 5 r₂

def r := TransClosure r₃

def R.irreflexive {α : Type} (set : Set (α × α)) : Prop :=
  ¬ (∃x, (x, x) ∈ set)

-- We chouldn't find a cycle after we find all the direct/undirect relations.
def R.acyclic {α : Type} (set : Set (α × α)) : Prop :=
  R.irreflexive (TransClosure set)

axiom EventIsUnique (e₁ e₂ : Event) : e₁ ≠ e₂ -- Assume each id is different.

#check Thread.mk 1

def test_event : Event :=
{
  id := "0"
  t_id := 2
  t := Thread.mk 1
  ln := 4
  a := Action.read "" ""
}

def test_event_1 : Event :=
{
  id := "1"
  t_id := 2
  t := Thread.mk 1
  ln := 4
  a := Action.read "" ""
}

def test_event_2 : Event :=
{
  id := "2"
  t_id := 2
  t := Thread.mk 1
  ln := 4
  a := Action.read "" ""
}

-- def po₁ := Rel.base test_event test_event_1 RoE.po (by apply EventIsUnique)
-- def po₂ := Rel.base test_event_1 test_event_2 RoE.po (by apply EventIsUnique)
-- #check po₁

def po_new := R.mk test_event_1 test_event_2
#check po_new

def addr (e : Event) : String :=
  match e.a with
  | Action.read addr' _ => addr'
  | Action.write addr' _ => addr'


/- instruction order lifted to events -/
def po : Set (Event × Event) := R.empty

/- links a write w to a read r taking its value from w -/
def rf : Set (Event × Event) := R.empty
/- total order over writes to the same memory location -/
def co : Set (Event × Event) := R.empty

def fr : Set (Event × Event) := R.empty

/-
The function ppo, given an execution (E, po, co, rf), returns the preserved program
order.
-/
def ppo : Set (Event × Event) := R.empty

/- program order restricted to the same memory location -/
def po_loc : Set (Event × Event) :=
  { (x, y) | (x, y) ∈ po ∧ addr x = addr y }

/- links a read r to a write w′ co-after the write w from which r takes its value -/
def com : Set (Event × Event) :=
  fr ∪ rf ∪ co

/-
The function fences returns the pairs of events in program order that are separated by
a fence, when given an execution.
-/
def fences : Set (Event × Event) := R.empty

def WR : Set (Event × Event) := R.empty

/-
We can only reorder WR in TSO, so other orders are preserved.
TSO has a write buffer so that the write operations maybe propgated out of order.
-/
def TSO_ppo : Set (Event × Event) := po \ WR

/-
The function prop returns the pairs of writes ordered by the propagation order, given
an execution.
-/
def test₁ := R.add test_event test_event_1 po

-- Example how we check if a relation is satisfied.
theorem check_if_in : (test_event, test_event_1) ∈ test₁ :=
  by
    constructor
    aesop

/-
An example of SC
  input data: (ppo, fences, prop)
-/

-- A relation on natural numbers
def lessThan : Rel Nat Nat := fun a b => a < b

-- A relation on custom types
structure Person where
  name : String
  age : Nat

def olderThan : Rel Person Person := fun p q => p.age > q.age
#check olderThan
