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

#check List

#check Relation.TransGen

instance : DecidableEq (Event × Event) :=
  inferInstance

@[simp] def rel.domain (input : List Event) : Finset (Event × Event) :=
  Multiset.ofList (input.product input) |>.toFinset

-- We define program order as (e.linenumber < e.linenumber && e.thread_id == e.thread_id)
-- we define cohenrence order as (e.w.target == e.w.target)
@[simp] def po (e₁ e₂ : Event) : Prop := e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id

@[simp] def bound.po (bound : List Event) (e₁ e₂ : Event) : Prop := e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id ∧ e₁ ∈ bound ∧ e₂ ∈ bound
--
instance (e₁ e₂ : Event) : Decidable (po e₁ e₂) :=
  show Decidable (e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id) from
    inferInstanceAs (Decidable (_ ∧ _))

--
-- def data_dependency (e₁ e₂ : Event) : Prop :=

-- coherence order: successive writes to the same location, if they're in the same thread we need to maintain data-dependency order,
-- which means the co follows the program order, if they're in different thread, we don't care the line number.
-- The coherence order gives the order in which all the memory writes to a given location have hit that location in memory
-- In this article: https://diy.inria.fr/doc/herd.html#note11, they defined how to calculate the cohenrence orders,
-- but due to the time limitation, we need to reduce the complexities, by just introduce the init write,
-- and also we'are in the compiler level, we don't need to calculate it using lib,
@[simp] def co (e₁ e₂ : Event) : Prop :=
  -- Same location and both are writes
  (e₁.a.target = e₂.a.target) ∧
  (e₁.a.action = write) ∧
  (e₂.a.action = write) ∧
  -- Different events (irreflexivity), makes sure it's strict order (no cycle).
  ¬ (e₁ == e₂)

instance (e₁ e₂ : Event) : Decidable (co e₁ e₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

-- This get all the possible coherence order for a specific location.
@[simp] def co.Wx (e : Event) : Prop := sorry

@[simp] def IW (e : Event) : Prop :=
  e.a.isFirstWrite

@[simp] def FW (e : Event) : Prop :=
  e.a.isFinalWrite

@[simp] def Wx (loc : String) (e : Event) : Prop :=
  e.a.target = loc

@[simp] def Ws (lst : List Event) : List Event := lst.filter (fun e ↦ e.a.action = write)

-- All events that access to the same location.
@[simp] def loc (e₁ e₂ : Event) : Prop :=
  e₁.a.target = e₂.a.target

-- @[simp] def trans (r : Event -> Event -> Prop) : Set (Event × Event) :=
--   { p | Relation.TransGen r p.1 p.2 }

@[simp] def irreflexivity {α : Type} (r : α -> α -> Prop) := ¬ (∃ a, (r a a))


@[simp] def irreflexivity.set {α : Type} (r : Finset (α × α)) :=
  ¬ (∃ a, (a, a) ∈ r)

@[reducible]
def rel (a b : Nat) : Prop := b = a + 1

-- instance (a b : Nat) : Decidable (rel a b) :=
--   show Decidable (rel a b) from
--     inferInstance (_)

def getPathLength (h_trans_gen : Relation.TransGen r a c) : Nat :=
  match h_trans_gen with
  | single => 1

-- Input is a list of events.
def tc_operator {α : Type} (r : α → α → Prop) (s : Set (α × α)) : Set (α × α) :=
  { (a, b) | r a b} ∪ {(a, c) | ∃ b, (a, b) ∈ s ∧ (b, c) ∈ s}

@[simp] def all (input : List Event) : List (Event × Event) := input.product input

@[simp] def tc_base
  (r : Event -> Event -> Prop) [DecidableRel r] (elems : List Event) : List (Event × Event) :=
  let all := all elems
  all |>.filter (fun p ↦ r p.1 p.2)

-- inductive TransComp where
--   | base {a b : Event} {r : Event -> Event -> Prop} : r a b -> TransComp
-- (1, 2) (2, 3) (3, 4) (4, 5)
-- (1, 2) (2, 3) (3, 4) (4, 5) (1, 3) (2, 4) (3, 5)
-- (1, 2) (2, 3) (3, 4) (4, 5) (1, 3) (2, 4) (3, 5) (1, 4) (2, 5) (1, 5)

-- We know there will be a fix-point that when (tc.product tc).any is false, then the tc_step won't produce more results.
@[simp] def tc_step
  (input : List Event)
  (tc : List (Event × Event))
  : List (Event × Event) :=
  (all input).filter (fun p₁ ↦ (tc.product tc).any (fun p₂ ↦ (p₁.1 = p₂.1.1 ∧ p₁.2 = p₂.2.2 ∧ p₂.1.2 = p₂.2.1))) ++ tc

@[simp] def is_transitive
  (db : List (Event × Event)) -- database
  (rel: (Event × Event))
  : Bool
  := (db.product db).any (fun joint_rel ↦ (rel.1 = joint_rel.1.1 ∧ rel.2 = joint_rel.2.2 ∧ joint_rel.1.2 = joint_rel.2.1))

-- This can give us one transition step, if we want to keep anything in the input,
-- The transition step is the elems.length
-- We define a function that computes the most length we need.

-- This is the descending version of transitive closure step.
@[simp] def tc_step'
  (bound: List (Event × Event))
  (tc : List (Event × Event))
  : List (Event × Event) :=
  bound.filter (is_transitive tc) ++ tc

-- This is the descending version of transitive closure N steps.
-- Essentially, it's get some data out of the bound (all pairs).
@[simp] def tc_step_N'
  (n : Nat)
  (bound : List (Event × Event))
  (tc : List (Event × Event))
  : List (Event × Event) :=
  match n with
  | 0 => tc
  | n' + 1 =>
    let prev_tc := tc_step' bound tc
    let filtered_bound := bound.filter (fun p ↦ p ∉ prev_tc)
    tc_step_N' n' filtered_bound (prev_tc)

-- To prove, if it remains same with n and n+1 rounds, then n+1+n' is also same.
-- lemma fixpoint
--   : tc_step_N' n bound tc = tc_step_N' (n+1) bound tc -> tc_step_N' n bound tc = tc_step_N' (n + n') bound tc :=
--   by
--     intro h₁
--     induction n with
--     | zero => {
--       unfold tc_step_N'
--       split
--       {
--         rfl
--       }
--       {
--         aesop
--         unfold is_transitive
--         aesop
--       }
--     }
--     | succ n' ih => {
--
--     }
--
@[simp] def tc_step_N
  (n : Nat)
  (input : List Event)
  (tc : List (Event × Event))
  : List (Event × Event) :=
  match n with
  | 0 => tc
  | n' + 1 => tc_step_N n' input (tc_step input tc)

@[simp] def comp_tc (elems : List Event) (r : Event → Event → Prop)
  [DecidableRel r] : List (Event × Event) :=
  tc_step_N (elems.length) elems (tc_base r elems)

-- Well founded computation, maybe eaiser to prove.
@[simp] def comp_tc_by_wd (events: List Event) (r : Event -> Event -> Prop)
  [DecidableRel r] : List (Event × Event) :=
  let direct_tc := tc_base r events

  let rec comp (diff_before : Nat) (bound : List (Event × Event)) (tc : List (Event × Event)) : List (Event × Event) :=
    let new_tc := tc_step' bound tc
    let filtered_bound := bound.filter (fun p ↦ p ∉ new_tc)

    if bound.length = diff_before then
      tc
    else
      comp filtered_bound.length filtered_bound new_tc

  termination_by (diff_before)
  decreasing_by by

  comp ((all events).length - direct_tc.length) (all events) direct_tc

-- Then this comp_tc' becomes move the data from (all input) to another (tc)
-- We know this tc is always decreasing, and after N times, it will remain same.
-- N times later it will contain all the TransGen that is in tc.
-- We just need to prove that after N times, you can't find more TransGen
-- Then we know all TransGen is in the tc_step_N
-- Because all the possible pairs are bouneded by the all input.
-- It's a transformation from a larger set to a subet.
-- And it's monotonic.
-- THere will be a point that all the current.
@[simp] def comp_tc' (elems : List Event) (r : Event → Event → Prop)
  [DecidableRel r] : List (Event × Event) :=
  tc_step_N' (elems.length) (all elems) (tc_base r elems)

@[simp] def acyclic {α : Type} [BEq α] (tc : List (α × α)) : Bool :=
  tc.any (fun p => p.1 == p.2)

@[simp] def cyclic {α : Type} [BEq α] (tc : List (α × α)) : Bool :=
  ¬ (acyclic tc)

-- TransGen: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Relation.TransGen
@[simp] def acyclic_predicates {α : Type} (search_space : List α) (r : α -> α -> Prop) : Prop :=
  ∀ e ∈ search_space, ¬(∃e, Relation.TransGen r e e)

-- Step 1: Control flow semantics
-- From write to read.
@[simp] def rf (e₁ e₂ : Event) : Prop := e₁.a.action == write ∧ e₂.a.action == read ∧ (e₁.a.target == e₂.a.target)

#check rf

instance (e₁ e₂ : Event) : Decidable (rf e₁ e₂) :=
  show Decidable (e₁.a.action == write ∧ e₂.a.action == read ∧ (e₁.a.target == e₂.a.target)) from
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

#synth DecidableRel rf

-- Step 2: Data flow semantics
-- The read-from relation rf describes, for any given read, from which write this read could have taken its value.
-- This will give us many possible results for each read event (Wⁿ -> R).
@[simp] def rf.set : Set (Event × Event) := {(a, b) | rf a b}

-- Set of all the writes.
def W : Set (Event) := { x | x.a.action = write }

-- def rf (e : Event) : Set (Event × Event) := {(a, b) | b.id == e.id } ∩ rf.all_candidates

-- For each event, they may have one or more candidate

-- We can provide a db to this function so that the caller can fetch the value via index.
def get_set {α : Type} (db : List (Set α)) (i : Fin db.length) : Set (Set α) := { db.get i }

def db.mk {α : Type} : List (Set α) := []
def db.add {α : Type} (db : List (Set α)) (elem : Set α) : List (Set α) := db ++ [elem]

partial def groupBySndEq (xs : List (Event × Event)) : List (List (Event × Event)) :=
  match xs with
  | [] => []
  | x :: xs' =>
    let (equal, rest) := xs'.partition (·.snd == x.snd)
    (x :: equal) :: groupBySndEq rest

partial def groupByFstEq (xs : List (Event × Event)) : List (List (Event × Event)) :=
  match xs with
  | [] => []
  | x :: xs' =>
    let (equal, rest) := xs'.partition (·.fst == x.fst)
    (x :: equal) :: groupBySndEq rest

-- coherence order is already been filtered by the same location, we just use the location of first elem in pair to group them.
partial def groupByLoc (xs : List (Event × Event)) : List (List (Event × Event)) :=
  match xs with
  | [] => []
  | x :: xs' =>
    let (equal, rest) := xs'.partition (·.fst.a.target == x.fst.a.target)
    (x :: equal) :: groupByLoc rest

-- coherence order is already been filtered by the same location, we just use the location of first elem in pair to group them.
partial def groupByLocEvent (xs : List Event) : List (List Event) :=
  match xs with
  | [] => []
  | x :: xs' =>
    let (equal, rest) := xs'.partition (·.a.target == x.a.target)
    (x :: equal) :: groupByLocEvent rest

def List.permutation {α : Type} (lst : List α) : List (List α) :=
  match lst with
  | [] => [[]]
  | x :: xs =>
    let remains := List.permutation xs
    remains.foldl (fun acc perm =>
      acc ++ (List.range (perm.length + 1)).map (fun i =>
        let (before, after) := perm.splitAt i
        before ++ [x] ++ after
      )
    ) []

-- https://diy.inria.fr/doc/herd.html#sec%3Aprimitive
-- cartisan product.
def cross {α : Type} : List (List α) → List (List α)
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

-- Iterative application of tc_step
def S_iter (k : Nat) (elems : List Event) (initial_tc : List (Event × Event)) : List (Event × Event) :=
  match k with
  | 0 => initial_tc
  | Nat.succ k_prev => tc_step elems (S_iter k_prev elems initial_tc)

-- Prove that tc_step_N is equivalent to S_iter
lemma tc_step_N_eq_S_iter (n : Nat) (elems : List Event) (initial_tc : List (Event × Event)) :
    tc_step_N n elems initial_tc = S_iter n elems initial_tc := by
  induction n with
  | zero => simp [tc_step_N, S_iter]
  | succ n' ih =>
    rw [tc_step_N, S_iter]
    rw [<-ih]

end Primitives
