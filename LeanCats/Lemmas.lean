import LeanCats.HerdingCats

open Primitives

lemma tc_step_N_swap
  (n : Nat)
  (tc : List (Event × Event)) :
  tc_step_N n (tc_step tc) = tc_step (tc_step_N n tc) :=
  by
    induction n generalizing tc with
    | zero => {
      simp
    }
    | succ n' h' => {
      rw [tc_step_N]
      rw [tc_step_N]
      rw [h' (tc_step tc)]
    }

lemma tc_step_N_add (m n : Nat) (tc : List (Event × Event)) :
  tc_step_N (m + n) tc = tc_step_N n (tc_step_N m tc) := by
  induction m generalizing n with
  | zero =>
    simp [tc_step_N]
  | succ m' ih =>
    repeat rw [tc_step_N]
    have h : tc_step_N (m' + n + 1) tc = tc_step_N (n + 1) (tc_step_N m' tc) :=
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
  {a b : Event}
  (tc : List (Event × Event))
  : (a, b) ∈ tc_step tc -> (a, b) ∈ tc_step (tc_step tc) :=
  by
    aesop

lemma tc_step_contains_input
  (tc : List (Event × Event))
  : tc ⊆ tc_step tc :=
  by
    simp

lemma tc_N_succ_steps_includes_N_succ
  (n : Nat)
  (tc : List (Event × Event))
  : tc_step_N n tc ⊆ tc_step_N (n+1) tc :=
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

lemma tc_N_steps_in_tc_N_succ
  {a b : Event}
  (n : Nat)
  (tc : List (Event × Event))
  : (a, b) ∈ tc_step_N (n+1) tc -> (a, b) ∈ tc_step_N (n) tc :=
    by
      intro h
      induction n generalizing tc with
      | zero => {
        aesop
      }
      | succ n' h' => {
        apply (h' (tc_step tc)) h
      }

lemma tc_N_steps_in_tc_N_succ'
  {a b : Event}
  (n : Nat)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  : (a, b) ∈ tc_step_N (n+1) (tc_base r input) -> (a, b) ∈ tc_step_N (n) (tc_base r input) :=
    by
      intro h
      apply tc_N_steps_in_tc_N_succ
      aesop

lemma tc_N_steps_is_tc
  {a b : Event}
  (n : Nat)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  : (a, b) ∈ tc_step_N n (tc_base r input) -> Relation.TransGen r a b := by
    intro h'
    induction n with
    | zero => {
      simp at h'
      have hrab : r a b :=
        by
          aesop
      apply Relation.TransGen.single
      exact hrab
    }
    | succ n' h'' => {
      apply h''
      apply tc_N_steps_in_tc_N_succ'
      exact h'
    }

lemma comp_tc_towards_tc
  {a b : Event}
  (r : Event -> Event -> Prop)
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
    apply h

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
  tc_step (tc_base r input) ⊆ input.product input :=
  by
    aesop

lemma tc_step_N_in_product
  (r : Event -> Event -> Prop)
  (n : Nat)
  [DecidableRel r]
  (input : List Event) :
  tc_step_N n (tc_base r input) ⊆ input.product input :=
  by
    induction n with
    | zero => {
      simp
    }
    | succ n' ih => {
      unfold tc_step_N
      rw [tc_step_N_swap]
      rw [tc_step]
      intro p
      simp only [List.mem_append]
      intro h

      cases h with
      | inl h' => {
        have pair_in_tcstep : p ∈ tc_step_N n' (tc_base r input) :=
        by
          apply List.mem_of_mem_filter
          exact h'

        exact ih pair_in_tcstep
      }
      | inr h' => {
        exact ih h'
      }
    }

-- Every pairs are connected (transitive)
-- This states that the product contains all the possible results.
lemma tc_comp_upper_bound
  {a b : Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input) :
  (comp_tc input r) ⊆ input.product input :=
  by
    intro p hcomp
    unfold comp_tc at hcomp
    apply (tc_step_N_in_product r (input.product input).length input)
    exact hcomp

-- This is used to prove the fix point.
lemma tc_comp_upper_bound'
  {a b : Event}
  {n : Nat}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event) :
  a ∈ input
  -> b ∈ input
  -> tc_step_N n (tc_base r input) ⊆ (comp_tc input r) :=
  by
    intro ha hb p hcomp
    unfold comp_tc
    induction n with
    | zero => {
      simp at hcomp
      have hprod : p ∈ input.product input :=
      by
        aesop

      sorry
    }
    | succ n' => {
      sorry
    }

-- This is the tail definition of the TransGen.
lemma tc_step_trans
  {a b c: Event}
  (prev_tc : List (Event × Event))
  (h₁ : (a, b) ∈ prev_tc)
  (h₂ : (b, c) ∈ prev_tc) :
  (a, c) ∈ tc_step prev_tc :=
  by
    simp
    apply Or.inl
    sorry

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
