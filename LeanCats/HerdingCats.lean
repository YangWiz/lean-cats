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
inductive RStar {α : Type} (R : α -> α -> Prop) : α -> α → Prop
where
  | base (a b : α) : R a b -> RStar R a b -- We should contains relation itself
  | refl (a : α) : RStar R a a
  | trans (a b c : α) : R a b -> R b c -> RStar R a c

/-
This is used for expressing sequential composition.
-/
notation (priority := high) r₁ ";" r₂ => Rel.seq r₁ r₂

#check Rel.seq (Rel.base 1 2 (by decide)) (Rel.base 2 3 (by decide))
#check (Rel.base 1 2 (by decide)) ; (Rel.base 2 3 (by decide))

/-
-/
structure Event :=
  id : ℕ
  thread : T -- Thread that holds the current instruction.
  PC : ℕ -- Program Counter or Line number for executing instruction.
  action : Action

/-
We define a Relation as α -> α -> Prop
Executions are tuples (E, po, rf, co), which consist of a set of events E,
giving a semantics to the instructions, and three relations over events: po, rf, and co
-/
structure Excution :=
  -- E: Set
  -- po: Event -> Event -> Prop
  -- rf: Event -> Event -> Prop
  fr: Event -> Event -> Prop

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
