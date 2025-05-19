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

-- We define program order as (e.linenumber < e.linenumber && e.thread_id == e.thread_id)
-- we define cohenrence order as (e.w.target == e.w.target)
@[simp] def po (e₁ e₂ : Event) : Prop := e₁.ln < e₂.ln ∧ e₁.t_id == e₂.t_id
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
@[simp] def tc_step
  (input : List Event)
  (tc : List (Event × Event))
  : List (Event × Event) :=
  (all input).filter (fun p₁ ↦ (tc.product tc).any (fun p₂ ↦ (p₁.1 = p₂.1.1 ∧ p₁.2 = p₂.2.2 ∧ p₂.1.2 = p₂.2.1))) ++ tc

@[simp] def tc_step_N
  (n : Nat)
  (input : List Event)
  (tc : List (Event × Event))
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  : List (Event × Event) :=
  match n with
  | 0 => tc_base r input
  | n' + 1 => tc_step_N n' input (tc_step input tc) r

@[simp] def comp_tc (elems : List Event) (r : Event → Event → Prop)
  [DecidableRel r] : List (Event × Event) :=
  tc_step_N (elems.length * elems.length) elems (tc_base r elems) r

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
--
-- def partitiOnX {α : Type} (loc : String) (s : Set α) : Set (Set α) :=
--   { set |  }


end Primitives
