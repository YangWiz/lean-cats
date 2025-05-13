import Init.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import Mathlib.Order.FixedPoints
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic -- For Fintype

namespace Primitives

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
@[simp] def comp_tc {α : Type} (elements : List α) (relation : α → α → Prop)
  [BEq α] [DecidableRel relation] : List (α × α) :=
  let direct_pairs := elements.product elements |>.filter (fun p => relation p.1 p.2)

  let expand (pairs : List (α × α)) : List (α × α) :=
    let new_pairs := pairs.flatMap (fun p1 =>
      pairs.flatMap (fun p2 =>
        if p1.2 == p2.1 && !(pairs.contains (p1.1, p2.2)) then
          [(p1.1, p2.2)]
        else
          []
      )
    )
    (pairs ++ new_pairs).eraseDups

  let max_iterations := elements.length * elements.length

  -- Use fold to iterate the fixed point computation
  List.range max_iterations |>.foldl
    (fun acc _ =>
      let next := expand acc
      if next.length == acc.length then acc else next)
    direct_pairs

def tc_operator {α : Type} (r : α → α → Prop) (s : Set (α × α)) : Set (α × α) :=
  { (a, b) | r a b} ∪ {(a, c) | ∃ b, (a, b) ∈ s ∧ (b, c) ∈ s}

#eval comp_tc [1, 2, 3] rel

#eval comp_tc [2, 3, 4] rel

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


-- TODO(Zhiyang): filter out the ones that the first one must be initial write.
def rf.candidates (prog : List Event) := cross (groupBySndEq (comp_tc prog rf))

--
-- def partitiOnX {α : Type} (loc : String) (s : Set α) : Set (Set α) :=
--   { set |  }

section Test

-- @[simp] def e₁ := Event.mk "1" 1 (Thread.mk 1) 1 (Action.mk write "x" none false false)
-- @[simp] def e₂ := Event.mk "2" 1 (Thread.mk 1) 2 (Action.mk read "x" none false false)
@[simp] def e₃ := Event.mk "3" 2 (Thread.mk 2) 1 (Action.mk write "x" none false false)
@[simp] def e₄ := Event.mk "4" 2 (Thread.mk 2) 2 (Action.mk read "x" none false false)
@[simp] def e₅ := Event.mk "5" 2 (Thread.mk 2) 3 (Action.mk write "x" none false false)

@[simp] def test_list := [e₃, e₄, e₅]
-- @[simp] def real_relation (e₁ e₂ : Event) (h : e₁ ∈ test_list ∧ e₂ ∈ test_list) := rf e₁ e₂

@[simp] def test_ayc := acyclic (comp_tc test_list po ++ comp_tc test_list rf ++ comp_tc test_list co)

@[simp] def test_syc := cyclic (comp_tc test_list po ++ comp_tc test_list rf)

def rf_lst := comp_tc test_list rf
--
def po_lst := comp_tc test_list po
--
def co_lst := comp_tc test_list co

def cp_lst := rf_lst ++ po_lst ++ co_lst

#eval comp_tc test_list co
#eval cp_lst
#eval acyclic cp_lst

-- Example of there are many different read from relations.
@[simp] def Wx1 := Event.mk "1" 1 (Thread.mk 1) 1 (Action.mk write "x" none false false)
@[simp] def Wx2 := Event.mk "2" 1 (Thread.mk 1) 2 (Action.mk write "x" none false false)
@[simp] def rd1 := Event.mk "3" 1 (Thread.mk 1) 3 (Action.mk read "x" none false false)
@[simp] def rd2 := Event.mk "4" 1 (Thread.mk 1) 4 (Action.mk read "x" none false false)

@[simp] def rf_test := [Wx1, Wx2, rd1, rd2]
@[simp] def rf_all := comp_tc rf_test rf

#eval rf_all

#eval rf_all.length

def test_ret := groupBySndEq rf_all
#eval test_ret.length
#eval rf_all
#eval test_ret

def candidates_rf := cross test_ret
#eval candidates_rf.head!

def co.candidates (events : List Event) : List (List (Event × Event)) :=
  -- First we need to get all the write events.
  -- Then we need to group them by their location.
  let wsx := groupByLocEvent (Ws events)
  -- Then we get all the sorted list.
  let ordered_ws := wsx.map (fun lst ↦ List.permutation lst)

  -- The outer list is all the permutations (sort) of the events, then we need to convert all the permutations to pairs.
  let ws_pairs := ordered_ws.map (fun outer_lst ↦ outer_lst.map (fun inner_lst ↦ inner_lst.dropLast.zip inner_lst.tail))
  -- They must all write to the same location and irrelexsive (We alrady groupped them indeed).
  let ws_pairs_x := ws_pairs.map (fun outer_lst ↦ outer_lst.filter (fun inner_lst ↦ inner_lst.all (fun p ↦ p.fst.a.target == p.snd.a.target ∧ ¬(p.fst == p.snd))))
  -- Make sure initial write always comes first.
  let ws_pairs_x_iw := ws_pairs_x.map (fun outer_lst ↦ outer_lst.filter (fun inner_lst ↦ inner_lst.all (fun p ↦ ¬ p.snd.a.isFirstWrite)))

  -- Generate all the candidates.
  (cross ws_pairs_x_iw).map (fun lst ↦ lst.flatten)

end Test

section coTest
@[simp] def wx1 := Event.mk "1" 1 (Thread.mk 1) 1 (Action.mk write "x" none true false)
@[simp] def wx2 := Event.mk "2" 1 (Thread.mk 1) 2 (Action.mk write "x" none false false)
@[simp] def wx3 := Event.mk "3" 1 (Thread.mk 1) 3 (Action.mk write "x" none false false)
@[simp] def wx4 := Event.mk "4" 1 (Thread.mk 1) 4 (Action.mk write "x" none false false)
@[simp] def wx5 := Event.mk "3" 1 (Thread.mk 1) 3 (Action.mk write "y" none true false)
@[simp] def wx6 := Event.mk "4" 1 (Thread.mk 1) 4 (Action.mk write "y" none false false)

def co_test := [wx1, wx2, wx3, wx4, wx5, wx6]

-- first we need to get all the write events.
def ws := Ws co_test
def Wxs := groupByLocEvent ws

#eval Wxs

def ordered_ws := Wxs.map (fun lst ↦ List.permutation lst)

#eval ordered_ws

-- Then we get all the sorted list, and the first one has to be the IW.
-- The outer list is all the permutations (sort) of the events, then we need to convert all the permutations to pairs.
def ws_pairs := ordered_ws.map (fun outer_lst ↦ outer_lst.map (fun inner_lst ↦ inner_lst.dropLast.zip inner_lst.tail))
#eval ws_pairs.head!.head!

-- They must all write to the same location and irrelexsive (We alrady groupped them indeed).
def ws_pairs_x := ws_pairs.map (fun outer_lst ↦ outer_lst.filter (fun inner_lst ↦ inner_lst.all (fun p ↦ p.fst.a.target == p.snd.a.target ∧ ¬(p.fst == p.snd))))

#eval ws_pairs_x.head!.length
#eval ws_pairs.head!.length

-- Make sure initial write always comes first.
def ws_pairs_x_iw := ws_pairs.map (fun outer_lst ↦ outer_lst.filter (fun inner_lst ↦ inner_lst.all (fun p ↦ ¬ p.snd.a.isFirstWrite)))

#eval ws_pairs_x_iw.head!.length
#eval ws_pairs_x_iw.tail.head!.length

def co_candidates := (cross ws_pairs_x_iw).map (fun inner_lst ↦ inner_lst.flatten)

#eval co_candidates.head!.length -- Should be 2.

def co₁ := co_candidates.head!
#eval co₁

#eval relation_inverse co₁

end coTest

-- This section introduces the test for message passing program.
-- Copy from the SB.litmus example: https://diy.inria.fr/doc/herd.html
section mp_test

-- initial write is on the virtual thread 0.
@[simp] def iwx := Event.mk "1" 0 (Thread.mk 0) 0 (Action.mk write "x" (some 0) true false)
@[simp] def iwy := Event.mk "2" 0 (Thread.mk 0) 0 (Action.mk write "y" (some 0) true false)

@[simp] def twx1 := Event.mk "3" 1 (Thread.mk 1) 1 (Action.mk write "x" none false false)
@[simp] def twy1 := Event.mk "4" 2 (Thread.mk 2) 1 (Action.mk write "y" none false false)

@[simp] def trx2 := Event.mk "5" 1 (Thread.mk 1) 2 (Action.mk read "x" none false false)
@[simp] def try2 := Event.mk "6" 2 (Thread.mk 2) 2 (Action.mk read "y" none false false)

def mp_prog := [iwx, iwy, twx1, twy1, trx2, try2]

def mp_rf_candidates := cross (groupBySndEq (comp_tc mp_prog rf))
def mp_po_candidate := comp_tc mp_prog po
def mp_co_candidates := co.candidates mp_prog

-- We get four possibilities which is same with the example in inria.
#eval mp_rf_candidates
#eval mp_po_candidate
#eval mp_co_candidates

def rfpo := mp_rf_candidates.product [mp_po_candidate]
-- We need to erase all the duplications to mimic the set property and we also need to union the pair.
def rfpo₁ := rfpo.map (fun rels ↦ (rels.fst ++ rels.snd).eraseDups)
#eval rfpo₁.length = 4 -- should be 4

-- Then we need to create from read.
-- This reverse corresponding to ^-1
def inversed_rd := mp_rf_candidates.map (relation_inverse)

-- Then we need to get the ; (sequence): (i.e., (x, y) ∈ (r1 ; r2 ) ↔ ∃z.(x, z) ∈ r1 ∧ (z, y) ∈ r2 )
def seq (candidate_l candidate_r: List (Event × Event)) : List (Event × Event) :=
  candidate_l.foldl (fun acc lhs ↦
    acc ++ (candidate_r.filter (fun rhs ↦ lhs.snd == rhs.fst)).map (fun p ↦ (lhs.fst, p.snd))
  ) []

#eval (mp_rf_candidates.eraseIdx 0).head!
def fst := relation_inverse mp_rf_candidates.head!

def test_fr := seq fst mp_co_candidates.head!
#eval test_fr

def fr.candidates (rf_all co_all : List (List (Event × Event))) : List (List (Event × Event)) :=
  (((rf_all).product co_all).map (fun frco_pair ↦ seq (relation_inverse frco_pair.fst) frco_pair.snd)).filter (fun fr ↦ fr.length > 0)

def union (l r : List (Event × Event)) : List (Event × Event) :=
  (l ++ r).eraseDups

def fr_all := fr.candidates mp_rf_candidates mp_co_candidates
#eval fr_all.length = 3

#eval fr_all

-- rf^-1;co
def frGen (rf_set co_set : List (Event × Event)) : List (Event × Event) :=
  seq (relation_inverse rf_set) (co_set)

-- Now anaysis this program.
-- (* Group communication relations together *)
-- let com = rf | fr | co
-- (* Sequential consistency condition *)
-- acyclic po | com as sc

-- This one is wrong
-- def final := union rfpo₁ fr_all
-- #eval final.length

-- We can now see we have rf, co, po, these three are base relation, the fr is derived by rf and co.
-- We should first connect these relation.
abbrev AllCandidates := List (List (Event × Event))
abbrev RelSet := List (Event × Event)

abbrev poIdx := Fin 1
abbrev rfIdx := Fin 2
abbrev coIdx := Fin 3

abbrev CatEnv := Std.HashMap String RelSet

#check List CatEnv

-- Use cross to connect them.
-- def connect (l r : AllCandidates) : List (Std.HashMap String RelSet) :=
--   (l.product r).foldl (fun acc p ↦ acc ++ [p.fst, p.snd]) []

end mp_test

def seq_prop {α : Type} (r₁ r₂ : α -> α -> Prop) : α -> α -> Prop :=
  let t1 := Subrelation r₁ r₂
  sorry

infix:50 (priority:=high) " ; " => seq_prop

theorem seq₁ {α : Type} {r₁ r₂ : α -> α -> Prop} : ∀ x y, (r₁;r₂) x y ↔ ∃z, r₁ x z ∧ r₂ z y := sorry

-- First prove the subset, then use Set to prove TransGen.
-- The definition of TransGen is:
-- TransGen r a z if and only if there exists a sequence a r b r ... r z of length at least 1 connecting a to z.
-- [(x, y) : ∃z, (x, z) ∧ (z, y)]
@[simp] def comp_tc_co (elems : List Event) : List (Event × Event) :=
  -- Find all possible relations.
  let all := elems.product elems
  -- Base step.
  let base_tc := all |>.filter (fun p ↦ co p.1 p.2)

  let rec comp_tc_in (n : Nat) (curr_tc : List (Event × Event)) : List (Event × Event) :=
    -- find all the indirect connect ones (Can't be itself).
    match n with
    | 0 =>
      curr_tc
    | n' + 1 =>
      let step_tc : List (Event × Event) :=
        all.product all
        |>.filter (fun p ↦ p.1.2 == p.2.1 && curr_tc.contains p.1 && curr_tc.contains p.2)
        |>.map (fun pr ↦ (pr.1.1, pr.2.2))
      let ret_tc := (step_tc ++ curr_tc).eraseDups

      comp_tc_in n' ret_tc

  comp_tc_in (base_tc.length * base_tc.length) base_tc

-- @[simp] def comp_tc''' {α : Type} (elems : List α) (r : α → α → Prop)
--   [BEq α] [DecidableEq (α × α)] [DecidableRel r] : Finset (α × α) :=
--   -- Find all possible relations.
--   let all := elems.product elems
--   -- Base step.
--   let base_tc := Multiset.ofList all |>.filter (fun p ↦ r p.1 p.2)
--
--   let rec comp_tc_in (n : Nat) (curr_tc : Finset (α × α)) : Finset (α × α) :=
--     -- find all the indirect connect ones (Can't be itself).
--     match n with
--     | 0 =>
--       curr_tc
--     | n' + 1 =>
--       let new_edges := Finset.biUnion curr_tc (fun p₁ =>
--       Finset.biUnion curr_tc (fun p₂ =>
--         if p₁.2 = p₂.1 then
--           Finset.singleton (p₁.1, p₂.2)
--         else
--           Finset.empty
--       )
--     )
--
--       comp_tc_in n' ret_tc
--
--   comp_tc_in (base_tc.card * base_tc.card) base_tc.toFinset

def t := (comp_tc [1, 2, 3] (rel)).toFinset.toSet

#check t ∪ t

#check t

#eval comp_tc [1, 7, 8, 9, 10] (rel)

-- theorem comp_tc_is_tc'
--   (a b : Event)
--   (lst : List Event)
--   (h₁ : a ∈ lst)
--   (h₂ : b ∈ lst) :
--   (Relation.TransGen co a b) ↔ (a, b) ∈ comp_tc_co lst := by
--     apply Iff.intro
--     {
--       intro htrans
--       simp
--       induction lst with
--       | cons head tail tail_ih => {
--         induction htrans with
--         | single hr => {
--           unfold comp_tc_co.comp_tc_in
--           simp
--           split
--           {
--             aesop
--           }
--           {
--             unfold comp_tc_co.comp_tc_in at tail_ih
--             simp_all
--             aesop
--           }
--         }
--         | tail => {
--           unfold comp_tc_co.comp_tc_in at tail_ih
--           unfold comp_tc_co.comp_tc_in
--           simp_all
--
--         }
--       }
--       | nil => {
--         contradiction
--       }
--     }
--     {
--       intro comp
--       _
--     }

def relComp {α : Type} (r₁ r₂ : List (α × α)) : List (α × α) := sorry

@[simp] def composite {α : Type} (r₁ r₂ : Set (α × α)) : Set (α × α) := {(x, y) | ∃z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂}

@[simp] def composite_k_times {α : Type} (r : Set (α × α)) (n : Nat) : Set (α × α) :=
  match n with
  | 0 => r
  | n' + 1 => composite r (composite_k_times r n')

@[simp] def composite_star {α : Type} (r : Set (α × α)) : Set (α × α) :=
  ⋃ k : Nat, composite_k_times r k

def composite_inf {α : Type} [DecidableEq α] (r : Set (α × α)) : Set (α × α) :=
  OrderHom.lfp (OrderHom.mk (fun s => r ∪ composite r s) (by
    sorry
  ))

instance {α : Type} {r : α -> α -> Prop} {a b : α} [DecidableRel r] : Decidable (Relation.TransGen r a b) := sorry

#check po

-- po has only one.
-- read from has many.

-- Suppose we have two rf candidates.
-- Now this is wrong, we need try to express it by grouping.
-- But in the end it's a union.
@[simp] def rf1 := rf
@[simp] def rf2 := rf

-- def input : Finset Event := {}
@[simp] def input_test : Set Nat := {1, 2, 3}

@[simp] def test_singleton : Set (Set (Nat × Nat)) := { {(a, b) | b = i ∧ a ∈ input_test } | i ∈ input_test }

lemma test_sin : {(1, 3), (2, 3), (3, 3)} ∈ test_singleton :=
  by
    simp
    aesop


def all_rd : Set Event := { e | e.a.action = read }

def all_wt: Set Event := { e | e.a.action = write }

def rw_pairs1 : Set (Event × Event) := { (a, b) | (a ∈ all_rd) -> (b ∈ all_wt) }

def rw_pairs : Set (Event × Event) := { (a, b) | (a ∈ all_rd) ∧ (b ∈ all_wt) }

def groupByRead : Set (Set (Event × Event)) :=
  {{ (a, b) | (a, b) ∈ rw_pairs ∧ b = i} | i ∈ all_wt}

def newcross : Set (Set (Event × Event)) := sorry

@[simp] def newunion (a b : Event) : Prop := po a b ∨ co a b
@[simp] def trans := Relation.TransGen newunion

@[simp] def rt₁ (a b : Event) := rf1 a b ∨ newunion a b
@[simp] def rt₂ (a b : Event) := rf2 a b ∨ newunion a b

@[simp] def acyc := ¬(∃x : Event, trans x x)


@[simp] def retrel (a b : Event) := rt₁ a b ∧ rt₂ a b
@[simp] def ret := {(a, b) | retrel a b ∧ ¬(Relation.TransGen retrel a b)}
@[simp] def rfset := {(a, b) | rf1 a b}

#check ret ⊆ rfset

-- We got a big union, we filter out all the set that is acyclic, and then check if they're equal:

end Primitives
