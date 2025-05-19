import LeanCats.HerdingCats

open Primitives

lemma tc_step_N_swap
  (n : Nat)
  (input : List Event)
  (tc : List (Event × Event)) :
  tc_step_N n input (tc_step input tc) = tc_step input (tc_step_N n input tc) :=
  by
    induction n generalizing tc with
    | zero => {
      aesop
    }
    | succ n' h' => {
      rw [tc_step_N]
      rw [tc_step_N]
      rw [h' (tc_step input tc)]
    }

lemma tc_step_N_add (input : List Event) (m n : Nat) (tc : List (Event × Event)) :
  tc_step_N (m + n) input tc = tc_step_N n input (tc_step_N m input tc) := by
  induction m generalizing n with
  | zero =>
    simp [tc_step_N]
  | succ m' ih =>
    repeat rw [tc_step_N]
    have h : tc_step_N (m' + n + 1) input tc = tc_step_N (n + 1) input (tc_step_N m' input tc) :=
      by
        apply ih (n + 1)
    nth_rewrite 2 [tc_step_N] at h
    rw [Nat.add_assoc]
    nth_rewrite 2 [Nat.add_comm]
    rw [<-Nat.add_assoc]
    rw [h]
    nth_rewrite 2 [tc_step_N_swap]
    rfl

lemma tc_base_is_tc
  {a b : Event}
  (r : Event -> Event -> Prop)
  (elems : List Event)
  [DecidableRel r]
  : (a, b) ∈ tc_base r elems -> Relation.TransGen r a b :=
  by
    intro h
    simp_all
    have rab : r a b :=
      by
        aesop
    apply Relation.TransGen.single
    exact rab

lemma tc_step_contains_prev_step
  (input : List Event)
  {a b : Event}
  (tc : List (Event × Event))
  : (a, b) ∈ tc_step input tc -> (a, b) ∈ tc_step input (tc_step input tc) :=
  by
    aesop

lemma tc_N_succ_steps_includes_N_succ
  (input : List Event)
  (n : Nat)
  (tc : List (Event × Event))
  : tc_step_N n input tc ⊆ tc_step_N (n+1) input tc :=
    by
      intro h
      induction n with
      | zero => {
        aesop
      }
      | succ n' h' => {
        intro h''
        unfold tc_step_N
        unfold tc_step_N
        rw [tc_step_N_swap]
        rw [tc_step_N_swap]
        apply tc_step_contains_prev_step
        unfold tc_step_N at h''
        rw [tc_step_N_swap] at h''
        exact h''
      }

-- This is the tail definition of the TransGen.
lemma tc_step_trans
  {a b c: Event}
  (input : List Event)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (h₁ : (a, b) ∈ tc_base r input)
  (h₂ : (b, c) ∈ tc_base r input) :
  (a, c) ∈ tc_step input (tc_base r input) :=
  by
    simp
    apply Or.inl
    aesop

lemma tc_step_tranGen
  {a b: Event}
  (input : List Event)
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  {ha : a ∈ input}
  {hb : b ∈ input}
  {tc : List (Event × Event)}
  (hab : (a, b) ∈ tc_step input (tc))
  (htrans : ∀a b, (a, b) ∈ tc -> Relation.TransGen r a b) :
  Relation.TransGen r a b :=
  by
    aesop
    have transaw : Relation.TransGen r a w :=
    by
      apply (htrans a w) left

    have transwb : Relation.TransGen r w b :=
    by
      apply (htrans w b) right

    apply Relation.TransGen.trans transaw transwb

lemma tc_step_trans'
  {a b c: Event}
  (input : List Event)
  {ha : a ∈ input}
  {hb : b ∈ input}
  {hc : c ∈ input}
  {tc : List (Event × Event)}
  (h₁ : (a, b) ∈ tc)
  (h₂ : (b, c) ∈ tc) :
  (a, c) ∈ tc_step input (tc) :=
  by
    induction tc with
    | nil => {
      aesop
    }
    | cons head tail tail_ih => {
      aesop
    }

lemma tc_step_N_trans
  {n : Nat}
  {a b c: Event}
  (input : List Event)
  {ha : a ∈ input}
  {hb : b ∈ input}
  {hc : c ∈ input}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (h₁ : (a, b) ∈ tc_step_N n input (tc_base r input))
  (h₂ : (b, c) ∈ tc_step_N n input (tc_base r input)) :
  (a, c) ∈ tc_step_N (n+1) input (tc_base r input) :=
  by
    unfold tc_step_N
    rw [tc_step_N_swap]
    apply tc_step_trans'
    exact ha
    exact hb
    exact hc
    exact h₁
    exact h₂

lemma tc_N_steps_in_tc_N_succ'
  {a b : Event}
  (n : Nat)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  : (a, b) ∈ tc_step_N n input (tc_base r input) -> (a, b) ∈ tc_step_N (n+1) input (tc_base r input) :=
    by
      intro h
      induction n with
      | zero => {
        aesop
      }
      | succ n' ih => {
        apply tc_N_succ_steps_includes_N_succ
        apply h
      }

lemma tc_step_base_transGen
  {a b: Event}
  (input : List Event)
  {ha : a ∈ input}
  {hb : b ∈ input}
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  (h : (a, b) ∈ tc_step input (tc_base r input)) :
  Relation.TransGen r a b :=
  by
    simp_all
    aesop
    {
      have hawTrans : Relation.TransGen r a w :=
      by
        apply Relation.TransGen.single
        exact right_1

      have hwbTrans : Relation.TransGen r w b :=
      by
        apply Relation.TransGen.single
        exact right

      apply Relation.TransGen.trans hawTrans hwbTrans
    }
    {
      apply Relation.TransGen.single
      exact h_2
    }

lemma TransGen_tc_step
  {a b c: Event}
  (input : List Event)
  {ha : a ∈ input}
  {hc : c ∈ input}
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  (tc : List (Event × Event))
  (habi : (a, b) ∈ tc)
  (hbci : (b, c) ∈ tc) :
  (a, c) ∈ tc_step input tc :=
  by
    aesop

lemma tc_N_steps_is_tc
  {a b: Event}
  (n : Nat)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  {ha : a ∈ input}
  {hb : b ∈ input}
  {tc : List (Event × Event)}
  (htrans : ∀ a b, (a, b) ∈ tc -> Relation.TransGen r a b)
  : (a, b) ∈ tc_step_N n input tc -> Relation.TransGen r a b := by
    intro h'
    induction n generalizing tc with
    | zero => {
      unfold tc_step_N at h'
      apply htrans
      exact h'
    }
    | succ n' h'' => {
      sorry
    }

lemma comp_tc_towards_tc
  {a b : Event}
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  (input : List Event) :
  a ∈ input
  -> b ∈ input
  -> (a, b) ∈ comp_tc input r
  -> Relation.TransGen r a b := by
    intro ha hb
    unfold comp_tc
    intro h
    apply tc_N_steps_is_tc
    exact ha
    exact hb
    have hbase : ∀ (a b : Event), (a, b) ∈ (tc_base r input) → Relation.TransGen r a b :=
    by
      intro a b
      intro h'
      simp at h'
      apply And.right at h'
      apply Relation.TransGen.single
      exact h'

    exact hbase
    exact h

lemma tc_base_in_product
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event) :
  tc_base r input ⊆ input.product input :=
  by
    aesop

lemma tc_step_in_product
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event) :
  tc_step input (tc_base r input) ⊆ input.product input :=
  by
    aesop

lemma tc_step_N_in_product
  (n : Nat)
  (input : List Event)
  (tc : List (Event × Event))
  (h : tc ⊆ input.product input) :
  tc_step_N n input tc ⊆ input.product input :=
  by
    induction n with
    | zero => {
      simp
      exact h
    }
    | succ n' ih => {
      unfold tc_step_N
      rw [tc_step_N_swap]
      aesop
    }

-- Every pairs are connected (transitive)
-- This states that the product contains all the possible results.
-- lemma tc_comp_upper_bound
--   {a b : Event}
--   (r : Event -> Event -> Prop)
--   [DecidableRel r]
--   (input : List Event)
--   (ha : a ∈ input)
--   (hb : b ∈ input) :
--   (comp_tc input r) ⊆ input.product input :=
--   by
--     intro p hcomp
--     unfold comp_tc at hcomp
--     apply (tc_step_N_in_product r (input.length * input.length) input)
--     exact hcomp


-- We want to calcualte the maximum or minimum pairs we can add for each round.
-- We need to specify the mimimum rounds that can make sure we can find all the pairs.
-- Suppose we only filter out one pair in each round, then we need at least (tc.product tc).length to get all the pairs.
-- 1. First we need to make sure that the input.product input is the upper bound, we can't find any more pair that is out of this bound.

-- Every pairs are connected (transitive)
-- This states that the product contains all the possible results.
lemma tc_comp_upper_bound
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  (input : List Event) :
  (comp_tc input r) ⊆ input.product input :=
  by
    unfold comp_tc
    apply tc_step_N_in_product
    aesop


-- We need to prove, after some iterations the (a, b) won't be changed
-- The computation is limited by input, so the input.product input is what we can calcuate at most.
-- a ∧ b ∈ input means the all possible results are combinations of (a, b)
lemma tc_towards_comp_tc
  {a b : Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event) :
  a ∈ input
  -> b ∈ input
  -> Relation.TransGen r a b
  -> (a, b) ∈ comp_tc input r :=
  by
    intro ha
    intro hb
    intro htrans
    unfold comp_tc
    induction htrans with
    | single hrel => {
      -- TODO(Zhiyang): Every pair in tc_comp is r a b
      sorry
    }
    | tail htrans hrel ih => {
      sorry
    }

theorem tc_comp_is_tc
  {a b : Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input) :
  Relation.TransGen r a b <-> (a, b) ∈ comp_tc input r :=
  by
    apply Iff.intro
    {
      intro htrans
      apply tc_towards_comp_tc
      {
        exact ha
      }
      {
        exact hb
      }
      {
        exact htrans
      }
    }
    {
      intro hcomp
      apply comp_tc_towards_tc
      {
        exact ha
      }
      {
        exact hb
      }
      {
        exact hcomp
      }
    }
