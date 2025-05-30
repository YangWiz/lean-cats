import LeanCats.HerdingCats

open Primitives
-- TODO(Zhiyang): filter out the ones that the first one must be initial write.
def rf.candidates (prog : List Event) := cross (groupBySndEq (comp_tc prog rf))

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

#eval (comp_tc test_list co).eraseDups
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

end mp_test

def relComp {α : Type} (r₁ r₂ : List (α × α)) : List (α × α) := sorry

@[simp] def composite {α : Type} (r₁ r₂ : Set (α × α)) : Set (α × α) := {(x, y) | ∃z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂}

@[simp] def composite_k_times {α : Type} (r : Set (α × α)) (n : Nat) : Set (α × α) :=
  match n with
  | 0 => r
  | n' + 1 => composite r (composite_k_times r n')

@[simp] def composite_star {α : Type} (r : Set (α × α)) : Set (α × α) :=
  ⋃ k : Nat, composite_k_times r k

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

def input : Finset Event := {}

def all_rd : Set Event := { e | e.a.action = read }

def all_wt: Set Event := { e | e.a.action = write }

-- def rw_pairs1 : Set (Event × Event) := { (a, b) | (a ∈ all_rd) -> (b ∈ all_wt) }

def rw_pairs : Set (Event × Event) := { (a, b) | (a ∈ all_rd) ∧ (b ∈ all_wt) }

def groupByRead : Set (Set (Event × Event)) :=
  {{ (a, b) | (a, b) ∈ rw_pairs ∧ b = i} | i ∈ all_wt}

def newcross : Set (Set (Event × Event)) := sorry

@[simp] def newunion (a b : Event) : Prop := po a b ∨ co a b
@[simp] def trans' := Relation.TransGen newunion

@[simp] def rt₁ (a b : Event) := rf1 a b ∨ newunion a b
@[simp] def rt₂ (a b : Event) := rf2 a b ∨ newunion a b

@[simp] def acyc := ¬(∃x : Event, trans' x x)

@[simp] def retrel (a b : Event) := rt₁ a b ∧ rt₂ a b
@[simp] def ret := {(a, b) | retrel a b ∧ ¬(Relation.TransGen retrel a b)}
@[simp] def rfset := {(a, b) | rf1 a b}

#check ret ⊆ rfset

-- We got a big union, we filter out all the set that is acyclic, and then check if they're equal:
