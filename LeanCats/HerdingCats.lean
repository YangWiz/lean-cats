import Init.Data.List

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

/-
For a given location x the coherence order is a total strict order on the write events to location x.
-/

/-
We define a Relation as α -> α -> Prop
Executions are tuples (E, po, rf, co), which consist of a set of events E,
giving a semantics to the instructions, and three relations over events: po, rf, and co
Relation over Events.

See Table II. Glossary of Relations.
-/

inductive RoE : Prop
where
  -- Foundational relations
  | po
  | rf
  | fr
  -- Read write pair relations
  | RR (e₁ e₂ : Event) (h : isReadEvent e₁ ∧ isReadEvent e₂) : RoE
  | RW (e₁ e₂ : Event) (h : isReadEvent e₁ ∧ isWriteEvent e₂) : RoE
  | WR (e₁ e₂ : Event) (h : isWriteEvent e₁ ∧ isReadEvent e₂) : RoE
  | WW (e₁ e₂ : Event) (h : isWriteEvent e₁ ∧ isWriteEvent e₂) : RoE
  -- Architectural order
  | co
  | comp : RoE -> RoE -> RoE

/-
This is used for expressing sequential composition.
-/
notation (priority := high) r₁ ";" r₂ => RoE.comp r₁ r₂

/-
Inductive predicates are used to prove something, so it has difference with inductive type.
-/
inductive Rel {α : Type} : RoE -> α -> α -> Prop
where
  | base (a b : α) (r : RoE) (h : a ≠ b) : Rel r a b
  | seq_comp {r₁ r₂ : RoE} {a b c : α} : Rel r₁ a b -> Rel r₂ b c -> Rel (r₁;r₂) a c
  -- We write irreflexive(r) to express the irreflexivity of r (i.e., ¬(∃x.(x, x) ∈ r))
  -- There is no way to represent ∃x, (x, x) ∈ r, so it's irreflexivity indeed.

/-
We denote the transitive (resp. reflexive-transitive) closure of a relation r as
r+ (resp. r∗).
-/
inductive RStar {α : Type} : Prop -> Prop
where
  | base (r : RoE) (a b : α) (h : a ≠ b)  : Rel r a b -> RStar (Rel r a b) -- We should contains relation itself
  -- | refl (a : α) : RStar (Rel a a)
  | trans (r : RoE) (a b c : α) : Rel r a b -> Rel r b c -> RStar (Rel r a c)

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

def po₁ := Rel.base test_event test_event_1 RoE.po (by apply EventIsUnique)
def po₂ := Rel.base test_event_1 test_event_2 RoE.po (by apply EventIsUnique)
#check po₁

def rr := Rel.base test_event test_event_1 (RoE.RR test_event test_event_1 (sorry))

def RRpo {e₁ e₂ : Event} (h : isReadEvent e₁ ∧ isReadEvent e₂) := Rel RoE.po e₁ e₂ -> Rel (RoE.RR e₁ e₂ h) e₁ e₂
#check RRpo (sorry)

-- We write po ∩ WR for the write-read pairs in program order
-- def po (e₁ e₂ : Event) := RoE.po e₁ e₂
-- def po_1 := po test_event test_event -- This can be used as an assumption.

-- #check po_1

#check Event

def rfe (e₁ e₂ : Event) :=
  Rel RoE.rf e₁ e₂ ∧ e₁.t_id ≠ e₂.t_id

#check True

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
def com (e₁ e₂ : Event) := Rel RoE.rf e₁ e₂ ∨ Rel RoE.fr e₁ e₂ ∨ Rel RoE.co e₁ e₂

def acyclic := 1
