import Init.Data.List
import Mathlib.Data.Set.Basic

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
inductive TransClosure {α : Type} (R : Set (α × α)) : α → α → Prop
  | base {a b : α} : (a, b) ∈ R → TransClosure R a b
  | trans {a b c : α} : TransClosure R a b → TransClosure R b c → TransClosure R a c

def transitiveClosure {α : Type} (R : Set (α × α)) : Set (α × α) :=
  { (a, b) | TransClosure R a b }

def R.irreflexive {α : Type} (set : Set (α × α)) :=
  ¬ (∃x, x ∈ transitiveClosure set)

-- theorem RelIsRstar {α : Type } {a b c d : α}:


-- #check Rel.seq (Rel.base 1 2 RoE.fr (by decide)) (Rel.base 2 3 RoE.fr (by decide))
-- #check (Rel.base 1 2 RoE.fr (by decide)) ; (Rel.base 2 3 RoE.fr (by decide))
--
-- def test_seq := (Rel.base 1 2 RoE.fr (by decide)) ; (Rel.base 2 3 RoE.fr (by decide))
-- #check test_seq

-- Check if clusore fullfill the reflexive.
-- def test_star := RStar.refl 1
-- #check test_star

axiom EventIsUnique (e₁ e₂ : Event) : e₁ ≠ e₂ -- Assume each id is different.

#check Thread.mk 1
-- def mk (e : Event) : Excution := {E := ∅, po := Unit, rf := e, fr := e}

--  (w, r) ∈ WR means that w is a write and r a read.
-- inductive RWPair : Prop -> Prop
-- where
--   | WR (e₁ e₂ : Event) : RWPair (Rel e₁ e₂)
--   | RR (e₁ e₂ : Event) : RWPair (Rel e₁ e₂)
--   | WW (e₁ e₂ : Event) : RWPair (Rel e₁ e₂)
--   | RW (e₁ e₂ : Event) : RWPair (Rel e₁ e₂)

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
  id := "1"
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

--def rr := Rel.base test_event test_event_1 (RoE.RR test_event test_event_1 (sorry))
--
--def RRpo {e₁ e₂ : Event} (h : isReadEvent e₁ ∧ isReadEvent e₂) := Rel RoE.po e₁ e₂ -> Rel (RoE.RR e₁ e₂ h) e₁ e₂
--#check RRpo (sorry)

-- We write po ∩ WR for the write-read pairs in program order
-- def po (e₁ e₂ : Event) := RoE.po e₁ e₂
-- def po_1 := po test_event test_event -- This can be used as an assumption.

-- #check po_1

-- #check Event
--
-- def rfe (e₁ e₂ : Event) :=
--   Rel RoE.rf e₁ e₂ ∧ e₁.t_id ≠ e₂.t_id
--
-- #check True

-- po\WR for all pairs in program order except the write-read pairs.
-- def test_poNWR (e₁ e₂ : Event) := RoE (Rel e₁ e₂) -> ¬ RWPair (Rel e₁ e₂)
-- #check test_poNWR test_event test_event

-- We write proc(e) for the thread holding the event e.
inductive EventProp (e : Event) : Type
where
  | proc : EventProp e
  | addr : EventProp e

-- Playground
-- We define a communication as for all events e₁ and e₂, it should be po or rf or fr relations.
-- def com (e₁ e₂ : Event) := Rel RoE.rf e₁ e₂ ∨ Rel RoE.fr e₁ e₂ ∨ Rel RoE.co e₁ e₂
--
-- def po_test₁ := Rel.base test_event test_event_1 RoE.po (by apply EventIsUnique)
-- def po_test₂ := Rel.base test_event_1 test_event_2 RoE.po (by apply EventIsUnique)
--
-- def acyclic {roe₁ roe₂ : RoE} {e₁ e₂ e₃ : Event} (_ : Rel roe₁ e₁ e₂) (_ : Rel roe₂ e₂ e₃) :=
--   Rel (RoE.comp roe₁ roe₂) e₁ e₃ -> e₁ ≠ e₃ -> True
--
-- def t₁ := acyclic po_test₁ po_test₂
-- #check t₁

-- First get all the sequential composition
-- Get all the relations that are po-loc and com, then try to find all the acyclic(po-loc ∪ com)

-- First we use a very naive implementation to check acyclic, every time we get a new relation from the
-- source code
-- The time complexity is O(n²). We create a working list, every time we got a new relation, we need to

-- inductive Acyclic {} {Rel}

-- inductive Relation {α : Type} : Type
-- where
--   | base : Set (α × α)
-- def a := Set (ℕ × ℕ)
