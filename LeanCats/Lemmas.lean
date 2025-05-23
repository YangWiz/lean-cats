import LeanCats.HerdingCats
import Mathlib.Tactic.Linarith.Frontend

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
lemma tc_step__base_trans
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

lemma imm_in_tc_base
  {r}
  [DecidableRel r]
  {a b: Event}
  (input : List Event)
  {tc : List (Event × Event)}
  (h₁ : (a, b) ∈ tc_base r input) :
  b ∈ input :=
  by
    induction tc with
    | nil => {
      aesop
    }
    | cons head tail tail_ih => {
      aesop
    }

lemma imm_in_tc_step_N
  {n}
  {r}
  [DecidableRel r]
  {a b: Event}
  (input : List Event)
  {tc : List (Event × Event)}
  (h₁ : (a, b) ∈ tc_step_N n input (tc_base r input)) :
  b ∈ input :=
  by
    induction n with
    | zero => {
      aesop
    }
    | succ n' ih => {
      apply ih
      sorry
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

lemma tc_base_in_tc_step_N
  {r}
  [DecidableRel r]
  (n : Nat)
  (input : List Event) :
  tc_base r input ⊆ tc_step_N n input (tc_base r input) :=
  by
    induction n with
    | zero => {
      simp
    }
    | succ n' ih => {
      unfold tc_step_N
      rw [tc_step_N_swap]
      aesop
    }

lemma tc_step_N_base_trans
  (n : Nat)
  {a b c: Event}
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input)
  (hc : c ∈ input)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (h₁ : (a, b) ∈ tc_step_N n input (tc_base r input))
  (h₂ : (b, c) ∈ tc_base r input) :
  (a, c) ∈ tc_step_N (n+1) input (tc_base r input) :=
  by
    unfold tc_step_N
    rw [tc_step_N_swap]
    apply tc_step_trans'
    exact ha
    exact hb
    exact hc
    exact h₁
    apply tc_base_in_tc_step_N
    exact h₂

lemma tc_step_N_base_trans'
  (n : Nat)
  (a b c: Event)
  (input : List Event)
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (h₁ : (a, b) ∈ tc_step_N n input (tc_base r input))
  (h₂ : (b, c) ∈ tc_base r input) :
  (a, c) ∈ tc_step_N (n+1) input (tc_base r input) :=
  by
    unfold tc_step_N
    rw [tc_step_N_swap]
    sorry

-- lemma tc_comp_trans
--   {n : Nat}
--   {a b c: Event}
--   (input : List Event)
--   {ha : a ∈ input}
--   {hb : b ∈ input}
--   {hc : c ∈ input}
--   (r : Event -> Event -> Prop)
--   [DecidableRel r]
--   (h₁ : (a, b) ∈ comp_tc input r)
--   (h₂ : (b, c) ∈ comp_tc input r) :
--   (a, c) ∈ comp_tc input r :=
--   by
--     unfold comp_tc at *
--     rw [tc_step_N_swap]
--     apply tc_step_trans'
--     exact ha
--     exact hb
--     exact hc
--     exact h₁
--     apply tc_base_in_tc_step_N
--     exact h₂

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
  (a b: Event)
  {n : Nat}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input)
  {tc : List (Event × Event)}
  (htrans : ∀ a b, (a, b) ∈ tc -> Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b)
  : (a, b) ∈ tc_step_N n input tc -> Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b := by
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
  -> Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b := by
    intro ha hb
    unfold comp_tc
    intro h
    apply tc_N_steps_is_tc a b r input ha hb

    have hbase : (a, b) ∈ (tc_base r input) → Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b :=
    by
      intro h'
      simp at h'
      apply And.right at h'
      apply Relation.TransGen.single
      aesop

    sorry

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

-- We want to calcualte the maximum or minimum pairs we can add for each round.
-- We need to specify the mimimum rounds that can make sure we can find all the pairs.
-- Suppose we only filter out one pair in each round, then we need at least (tc.product tc).length to get all the pairs.
-- 1. First we need to make sure that the input.product input is the upper bound, we can't find any more pair that is out of this bound.
-- 2. We split the tc_comp, for a b in it, we can find TransGen (a, b) ∧ TransGen (b, c) in previous round, for a b we can need to find (a, e) and (e, b) ...
-- 3. We find the longest path, use tc_step_N to represent it then because all other steps are smaller than it, it's the subset of setp_N max_len

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

lemma tc_base_is_r
  {a b: Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input) :
  r a b ↔ (a, b) ∈ tc_base r input :=
  by
    apply Iff.intro
    {
      simp_all
    }
    {
      simp_all
    }

-- Try to find the event from decoupling the TransGen a b, to say all the intermediate val we say c, is in input.
-- where c is ∃c, a, c ∨ c, d ...
-- TransGen r a z if and only if there exists a sequence a r b r ... r z of length at least 1 connecting a to z.
lemma tc_comp_N_monotonic
  {i k : Nat}
  {tc : List (Event × Event)}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event) :
  tc_step_N i input tc ⊆ tc_step_N (i+k) input tc :=
  by
    rw [tc_step_N_add]
    induction k with
    | zero => {
      simp
    }
    | succ n' ih => {
      rw [tc_step_N]
      rw [tc_step_N_swap]
      aesop
    }

lemma tc_comp_includes_all

lemma tc_comp_includes_all
  {a b : Event}
  {r}
  {n}
  [DecidableRel r]
  {input : List Event}
  (htrans : Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b) :
  (a, b) ∈ comp_tc input r -> (a, b) ∈ tc_step_N n input (tc_base r input) :=
  by
    intro h
    aesop

-- We need to prove, after some iterations the (a, b) won't be changed
-- The computation is limited by input, so the input.product input is what we can calcuate at most.
-- a ∧ b ∈ input means the all possible results are combinations of (a, b)
lemma tc_towards_comp_tc
  {r : Event -> Event -> Prop}
  {a b : Event}
  [DecidableRel r]
  (input : List Event) :
  a ∈ input
  -> b ∈ input
  -> Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b
  -> (a, b) ∈ comp_tc input r :=
  by
    intro ha
    intro hb
    intro htrans
    unfold comp_tc
    unfold tc_step_N

    split
    {
      aesop
    }
    {
      rename_i heq
      rename_i n'
      rename_i n
      rw [<-tc_step_N]
      induction htrans with
      | single hrel => {
        apply tc_base_in_tc_step_N
        aesop
      }
      | tail htrans hrel ih => {
        rename_i c'
        rename_i b'

        apply tc_step_N_base_trans' n' a b' c'
        {
          induction n with
          | zero => {
            apply tc_comp_includes_all
            {
              exact htrans
            }
            {
              aesop
            }
          }
          | succ n'' ih => {
            exact ih
          }
        }
        {
          aesop
        }
      }
    }

#check tc_step_N_trans
    -- apply tc_step_N_base_trans input.length input ha hb hc r

    -- induction htrans with
    -- | single hrel => {
    --   rename_i b
    --   apply tc_base_in_tc_step_N
    --   simp
    --   apply And.intro
    --   apply And.intro
    --   exact ha
    --   exact hb
    --   exact hrel
    -- }
    -- | tail htrans hrel ih => {
    --   rename_i c'
    --   rename_i b'
    --   -- apply tc_step_N_base_trans input r
    --   -- have htransab' : Relation.TransGen r a b' :=
    --   -- by
    --   --   apply Relation.TransGen.tail
    --   --   exact htrans
    --   --   exact hrel
    --   -- apply tc_towards_comp_tc at htransab'
    --   -- rename_i htransab''
    -- }

-- For any events a, b we can always find a path.

-- lemma tc_towards_comp_tc'
--   {a b : Event}
--   [DecidableRel r]
--   (input : List Event) :
--   a ∈ input
--   -> b ∈ input
--   -> Relation.TransGen r a b
--   -> (a, b) ∈ comp_tc' input r :=
--   by
--     intro ha
--     intro hb
--     intro htrans
--     unfold comp_tc'
--     induction htrans with
--     | single hrel => {
--
--     }
--     | tail htrans rel ih => {
--       unfold tc_step_N'
--       split
--       {
--
--       }
--       {
--         rename_i len
--         rename_i n
--         rename_i n'
--         induction n
--       }
--     }

lemma is_transitive_transGen
  {a b : Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (tc : List (Event × Event))
  (h : ∀p ∈ tc, Relation.TransGen r p.1 p.2)
  : is_transitive tc (a, b) -> Relation.TransGen r a b :=
  by
    simp
    intro e
    intro h₁
    intro h₂
    have hae : Relation.TransGen r a e :=
    by
      apply h (a, e)
      exact h₁

    have heb : Relation.TransGen r e b :=
    by
      apply h (e, b)
      exact h₂

    apply Relation.TransGen.trans hae heb

-- If the pair is not in the (all input), then it's not a transGen.

theorem tc_comp_is_tc
  {a b : Event}
  (r : Event -> Event -> Prop)
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input) :
  Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b <-> (a, b) ∈ comp_tc input r :=
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
      sorry
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

-- tc_step_N number of elements can't larger than the (all input).
-- lemma test_length_lim : tc_step_N := sorry

-- lemma tc_step'_N_swap
--   (n : Nat)
--   (input : List Event)
--   (tc : List (Event × Event)) :
--   tc_step_N' n input (tc_step input tc) = tc_step input (tc_step_N n input tc) :=
--   by
--     induction n generalizing tc with
--     | zero => {
--       aesop
--     }
--     | succ n' h' => {
--       rw [tc_step_N]
--       rw [tc_step_N]
--       rw [h' (tc_step input tc)]
--     }

@[simp] def tc_step_N_NoDup
  (n : Nat)
  (bound : List (Event × Event))
  (tc : List (Event × Event))
  (htc : tc.Nodup)
  (hb : bound.Nodup)
  : tc_step_N' n bound tc |>.Nodup :=
  by
    induction n with
    | zero => {
      simp
      exact htc
    }
    | succ n' ih => {
      unfold tc_step_N'
      sorry
    }

-- @[simp] lemma tc_base_NoDup
--   (r : Event -> Event -> Prop)
--   [DecidableRel r]
--   (input : List Event)
--   (hinput : input.Nodup)
--   : tc_base r input |>.Nodup :=
--   by
--     simp [List.Nodup]
--     have prod_nodup : input.product input |>.Nodup :=
--     by
--       simp [List.Nodup] at *
--       induction input with
--       | nil => {
--         simp [List.product]
--       }
--       | cons head tail ih => {
--
--       }

@[simp] def tc_step_NoDup
  (n : Nat)
  (bound : List (Event × Event))
  (tc : List (Event × Event))
  (htc : tc.Nodup)
  (hb : bound.Nodup)
  : tc_step' bound tc |>.Nodup :=
  by
    induction n with
    | zero => {
      simp

    }
    | succ n' ih => {
      unfold tc_step_N'
      sorry
    }

instance
  {a b : Event}
  {r : Event -> Event -> Prop}
  [DecidableRel r]
  (input : List Event)
  (ha : a ∈ input)
  (hb : b ∈ input) : Decidable (Relation.TransGen (fun x y => r x y ∧ x ∈ input ∧ y ∈ input) a b) :=
  by
    rw [tc_comp_is_tc r input ha hb]
    apply List.instDecidableMemOfLawfulBEq

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
    rw [tc_step_N_swap]

def S (k : Nat) (elems : List Event) (r : Event → Event → Prop) [DecidableRel r] : List (Event × Event) :=
  S_iter k elems (tc_base r elems)

lemma comp_tc_eq_S_len (elems : List Event) (r : Event → Event → Prop) [DecidableRel r] :
    comp_tc elems r = S elems.length elems r := by
  simp [comp_tc, S, tc_step_N_eq_S_iter]
