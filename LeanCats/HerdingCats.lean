inductive Thread (n : ℕ) where
  | t_id: Thread n
/-
Inductive predicates are used to prove something, so it has difference with inductive type.
-/
inductive Rel {α : Type} : α -> α -> Prop
where
  | base (a b : α) (h : a ≠ b) : Rel a b
  | seq {a b c : α} : Rel a b -> Rel b c -> Rel a c
  -- We write irreflexive(r) to express the irreflexivity of r (i.e., ¬(∃x.(x, x) ∈ r))
  -- There is no way to represent ∃x, (x, x) ∈ r, so it's irreflexivity indeed.

/-
We denote the transitive (resp. reflexive-transitive) closure of a relation r as
r+ (resp. r∗).
-/
inductive RStar {α : Type} : Prop -> Prop
where
  | base (a b : α) (h : a ≠ b) : Rel a b -> RStar (Rel a b) -- We should contains relation itself
  -- | refl (a : α) : RStar (Rel a a)
  | trans (a b c : α) : Rel a b -> Rel b c -> RStar (Rel a c)

/-
This is used for expressing sequential composition.
-/
notation (priority := high) r₁ ";" r₂ => Rel.seq r₁ r₂

#check Rel.seq (Rel.base 1 2 (by decide)) (Rel.base 2 3 (by decide))
#check (Rel.base 1 2 (by decide)) ; (Rel.base 2 3 (by decide))

def test_seq := (Rel.base 1 2 (by decide)) ; (Rel.base 2 3 (by decide))
#check test_seq

-- Check if clusore fullfill the reflexive.
-- def test_star := RStar.refl 1
-- #check test_star

/-
-/
inductive Event : Type
where
  | mk : Event

theorem EventIsUnique (e₁ e₂ : Event) :
  e₁ ≠ e₂ := sorry

/-
We define a Relation as α -> α -> Prop
Executions are tuples (E, po, rf, co), which consist of a set of events E,
giving a semantics to the instructions, and three relations over events: po, rf, and co
-/
inductive Excution {e₁ e₂ : Event} (R : Rel e₁ e₂) : Type
where
  | po: Excution (Rel.base e₁ e₂ (by apply EventIsUnique)) -- Try to define that the event is unique.
  | rf: Excution (Rel.base e₁ e₂ (by apply EventIsUnique))
  | fr: Excution (Rel.base e₁ e₂ (by apply EventIsUnique))

-- def mk (e : Event) : Excution := {E := ∅, po := Unit, rf := e, fr := e}

/-
Actions now have two types: read and write.
We specify that an action either reads or writes a value at a specific location.
We write proc(e) for the thread holding the event e and addr(e) for its
address, or memory location.
-/
inductive Action (a : α) (v : ℕ) : Type where
  | write: Action a v
  | read:  Action a v

#check Thread 1
#check Event

-- We write proc(e) for the thread holding the event e.
inductive EventProp (e : Event) : Type
where
  | proc : EventProp e
  | addr : EventProp e
