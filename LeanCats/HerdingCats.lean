import Init.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import Mathlib.Order.FixedPoints
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic -- For Fintype
import LeanCats.Data

namespace Primitives
structure Event₁ where
  po : ℕ
  rf : ℕ
  fr : ℕ

instance : DecidableEq (Event × Event) :=
  inferInstance

@[simp] def rel.domain (input : List Event) : Finset (Event × Event) :=
  Multiset.ofList (input.product input) |>.toFinset

@[simp] def rel_incl
  {α : Type}
  (E : List α)
  (r₁ r₂ : List α -> Rel α α)
  : Prop :=
  ∀x ∈ E, ∀ y ∈ E, r₁ E x y -> r₂ E x y

instance
  {α : Type}
  (E : List α)
  [DecidableEq α]
  (r₁ r₂ : List α -> Rel α α)
  [DecidableRel (r₁ E)]
  [DecidableRel (r₂ E)]
  : Decidable (rel_incl E r₁ r₂) :=
  by
    simp
    infer_instance

@[simp] def internal (E : List Event) (e₁ e₂ : Event) : Prop
  := e₁.t_id = e₂.t_id ∧ E.contains e₁ ∧ E.contains e₂
instance (E : List Event) (e₁ e₂ : Event) : Decidable (internal E e₁ e₂) :=
  by
    simp
    infer_instance

-- transitive_closure rf' co'

variable (rf' co' : Rel Event Event)
#check ¬ (∃x, Relation.TransGen (fun x y ↦ rf' x y ∨ co' x y) x x)

def test : Prop := 2 = 2

def prop : ∀ prop ∈ [test], prop :=
by
  simp
  intro prop
  intro h
  rw [h]
  unfold test
  simp

#reduce rf'

-- Declare 'a' and 'b' as natural numbers for the following definitions
variable (a b : Nat)

-- 'a' and 'b' are implicitly parameters to this definition
def mySum : Nat := a + b

#eval mySum 1 2

@[simp] def rf (E : List Event) (e₁ e₂ : Event) : Prop
  := e₁.a.action = write ∧ e₂.a.action = read ∧ (e₁.a.target = e₂.a.target) ∧ e₁.a.value = e₂.a.value ∧ E.contains e₁ ∧ E.contains e₂
instance (E : List Event) (e₁ e₂ : Event) : Decidable (rf E e₁ e₂) :=
  by
    simp
    infer_instance

@[simp] def po (E : List Event) (e₁ e₂ : Event) : Prop :=
  e₁.ln < e₂.ln ∧ e₁.t_id = e₂.t_id ∧ internal E e₁ e₂
instance (E : List Event) (e₁ e₂ : Event) : Decidable (po E e₁ e₂) :=
  by
    simp
    infer_instance

instance (E : List Event) : DecidableRel (po E) :=
  by
    infer_instance

@[simp] def pre_co (E : List Event) (e₁ e₂ : Event) : Prop
  := e₁.a.action = write ∧ e₂.a.action = write ∧ e₁.a.target = e₂.a.target ∧ E.contains e₁ ∧ E.contains e₂

instance (E : List Event) (e₁ e₂ : Event) : Decidable (pre_co E e₁ e₂) :=
  by
    simp
    infer_instance

instance (E : List Event) : DecidableRel (pre_co E) :=
  by
    infer_instance

@[simp] def partial_order.strict
  {α : Type}
  (r : Rel α α)
  (E : List α)
  : Prop :=
  (∀ x ∈ E, ∀ y ∈ E, ∀ z ∈ E, r x y → r y z → r x z) ∧
  (∀ x ∈ E, ¬r x x)

instance {α : Type}
  [DecidableEq α]
  (r : Rel α α)
  [DecidableRel r]
  (E : List α)
  : Decidable (partial_order.strict r E) :=
  by
    simp
    infer_instance

@[simp] def linear_strict_order {α : Type} (r : Rel α α) (xs : List α) : Prop :=
  partial_order.strict r xs ∧
  ∀ x1 ∈ xs, ∀ x2 ∈ xs, x1 ≠ x2 → r x1 x2 ∨ r x2 x1  -- Totality

instance {α : Type} [DecidableEq α]
  (r : Rel α α) [DecidableRel r] (xs : List α)
  : Decidable (linear_strict_order r xs) :=
by
  simp
  infer_instance

@[simp] def is_write_same_loc (loc : String) (e : Event) := e.a.action = write ∧ e.a.target = loc

instance (loc : String) (e : Event) : Decidable (is_write_same_loc loc e) :=
by
  simp
  infer_instance

@[simp] def co_well_formed
  (E : List Event)
  (locs : List String)
  (co : List Event -> Rel Event Event)
  [DecidableRel (co E)]
  : Prop :=
  rel_incl E co pre_co ∧
  ∀loc ∈ locs, linear_strict_order (co E) (E.filter (is_write_same_loc loc))

instance
  (E : List Event)
  (locs : List String)
  (co : List Event -> Rel Event Event)
  [DecidableRel (co E)]
  : Decidable (co_well_formed E locs co) :=
by
  unfold co_well_formed
  unfold linear_strict_order
  infer_instance

@[simp] def fr (E : List Event) (co : List Event -> Rel Event Event) (e₁ e₂ : Event) : Prop :=
  ∃ w ∈ E, w.a.action = write ∧ rf E w e₁ ∧ co E w e₂

instance
  (E : List Event)
  (co : List Event -> Rel Event Event)
  [DecidableRel (co E)]
  (e₁ e₂ : Event)
  : Decidable (fr E co e₁ e₂) :=
  by
    simp
    infer_instance

-- This get all the possible coherence order for a specific location.
@[simp] def co.Wx (e : Event) : Prop := sorry

@[simp] def IW.rel (e : Event) : Bool :=
  e.a.isFirstWrite

@[simp] def FW.rel (e : Event) : Bool :=
  e.a.isFinalWrite

@[simp] def W.rel (e : Event) : Bool :=
  e.a.action = write

@[simp] def Ws (lst : List Event) : List Event := lst.filter (fun e ↦ e.a.action = write)

-- All events that access to the same location.
@[simp] def loc.rel (e₁ e₂ : Event) : Bool :=
  e₁.a.target = e₂.a.target

@[simp] def irreflexivity {α : Type} (r : α -> α -> Prop) := ¬ (∃ a, (r a a))

@[simp] def irreflexivity.set {α : Type} (r : Finset (α × α)) :=
  ¬ (∃ a, (a, a) ∈ r)

@[reducible]
def rel (a b : Nat) : Prop := b = a + 1

-- Step 1: Control flow semantics
-- From write to read.
@[simp] def candadites (input : List Event) := input.product input |>.eraseDups

@[simp] def cross {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | s1 :: s =>
    let ts := cross s
    -- We want to put all the element from the head to the remaining result.
    s1.foldl (fun r e1 =>
      r ++ ts.map (fun t => e1 :: t)
    ) []

-- We can inverse the relation (a -> b) to (b -> a).
def relation_inverse {α : Type} (lst : List (α × α)) : List (α × α) :=
  lst.map (fun p ↦ (p.snd, p.fst))
--
-- def partitiOnX {α : Type} (loc : String) (s : Set α) : Set (Set α) :=
--   { set |  }

@[simp] def co0.cal (input : List Event) :=
  let candidates := candadites input
  let loc := candidates.filter (λ p ↦ loc.rel p.1 p.2)
  let IW := input.filter (λ p ↦ IW.rel p)
  let FW := input.filter (λ p ↦ FW.rel p)
  let W := input.filter (λ p ↦ W.rel p)
  loc ∩ ((IW.product (W \ IW)) ∪ ((W \ FW).product FW))

#synth DecidableRel (rf {})

@[simp] def co0 (input : List Event) (a b : Event) : Prop :=
  co0.cal input |>.contains (a, b)

instance (input : List Event) : DecidableRel (co0 input) :=
by
  unfold co0
  unfold co0.cal
  simp
  infer_instance

-- Check if element a comes before b in the relation
@[simp] def comes_before {α : Type} [DecidableEq α] (bound : List α) (rel : Rel α α) (a b : α) : Prop :=
  ∀ x ∈ bound, ∀ y ∈ bound, rel x y -> a = x ∧ b = y

instance {α : Type} [DecidableEq α] (bound : List α) (rel : Rel α α) [DecidableRel rel] (a b : α) :
  Decidable (comes_before bound rel a b) :=
  by
    unfold comes_before
    infer_instance

-- Check if a list respects the relation (is a valid linearization)
@[simp] def respects_relation {α : Type} [DecidableEq α] (rel : Rel α α) [DecidableRel rel] (lst : List α) : Bool :=
  lst.zip lst.tail |>.all fun (a, b) =>
    ¬(comes_before lst rel b a)

instance {α : Type} [DecidableEq α] (bound : List α) (rel : Rel α α) [DecidableRel rel] :
  Decidable (respects_relation rel bound) :=
  by
    unfold respects_relation
    infer_instance

-- Find all valid linearizations
@[simp] def linearizations
  {α : Type}
  [DecidableEq α]
  (elements : List α)
  (rel : Rel α α)
  [DecidableRel rel]
  : List (List α) :=
  (elements.permutations).filter (respects_relation rel)

-- This function collects all the possible locations in the input program.
@[simp] def get_all_locs (input : List Event) : List String :=
  input.foldl (λ acc val ↦ val.a.target :: acc) [] |>.eraseDups

-- Check if a list respects the relation (is a valid linearization)
@[simp] def linearisations
  {α : Type}
  [DecidableEq α]
  (elements : List α)
  (rel : Rel α α)
  [DecidableRel rel]
  : List (List (α)) :=
  (elements.permutations).filter (λ sort ↦ linear_strict_order rel sort)

@[simp] def Wx (input : List Event) : List (List Event) :=
  (get_all_locs input).map (λ loc ↦ input.filter (λ e ↦ is_write_same_loc loc e))

-- allCox contains 1. List of all possible co candidates for each location.
@[simp] def allCox (input : List Event) : List (List (List Event)) :=
  (Wx input).map (fun ws ↦ linearizations ws (co0 input))

-- We fetch one possible candidate for each location, then append them together as one candidate execution.
@[simp] def allCo (input : List Event) : List (List (List Event)) := cross (allCox input)

-- After flatten, we know each candidate is a list of events we want.
@[simp] def co.Es (input : List Event) : List (List Event) := (cross (allCox input)).map (λ candidate ↦ candidate.flatten) |>.eraseDups

-- Transform all the sorted events for a specific location to pairs in each candidate, and flatten the candidate.
@[simp] def co'' (input : List Event) (a b : Event) : Prop :=
  (allCo input).map (λ candidate ↦ (candidate.map (λ ws_x ↦ ws_x.zip ws_x.tail)).flatten)
  |>.any (λ candidate ↦ candidate.contains (a, b))

instance (input : List Event) : DecidableRel (co'' input) :=
by
  unfold co''
  infer_instance

-- def co (E : List Event) (a b : Event) : Prop
--   := (allCo E).flatten.contains ()
--
-- lemma allCo_well_formed
--   (input : List Event)
--   : co_well_formed input [] (allCo input).flatten
--
@[simp] def rf_well_formed (E : List Event) (rf' : List Event -> Rel Event Event) : Prop :=
  partial_order.strict (rf' E) E ∧
  ∀ r ∈ E, r.a.action = read ->
    (∃ w ∈ E, rf' E w r) ∧
    (∀ w₁ ∈ E, ∀ w₂ ∈ E, rf' E w₁ r -> rf' E w₂ r -> w₁ = w₂)

instance
  (E : List Event)
  (rf : List Event -> Rel Event Event)
  [DecidableRel (rf E)] : Decidable (rf_well_formed E rf) :=
by
  unfold rf_well_formed
  infer_instance

@[simp] def is_read (e : Event) : Prop := e.a.action = read

instance (e : Event) : Decidable (is_read e) :=
  by
    unfold is_read
    infer_instance

-- input : all the events.
-- The corss is similiar to co, we have all the reads on (write x), then we pick one out and union with reads on other location write (e.g. y)
@[simp] def rf.Es (input : List Event) : List (List Event) :=
  let reads : List Event := (input.filter (is_read)).eraseDups
  let rx : List (List Event) := reads.map (λ r ↦ input.filter (λ w ↦ rf input w r)) |>.eraseDups
  -- This line is because we only have write events in the candidate, we need to add our reads (one read can read from different possible writes, but in one one candiate the read can only have exact one source to read).
  (cross rx).map (λ ws ↦ reads ++ ws)

@[simp] def validate
  (input : List Event)
  : Prop
  :=
    (rf.Es input).all (λ E ↦ rf_well_formed E rf) ∧
    (co.Es input).all (λ E ↦ co_well_formed E (get_all_locs input) co'')

instance (input : List Event) : Decidable (validate input) :=
by
  unfold validate
  infer_instance

-- def mkCandidateExcution (E : List Event) (rf : Rel Event Event) (co : Rel Event Event) (po : Rel Event Event) :=
--   sorry

end Primitives
