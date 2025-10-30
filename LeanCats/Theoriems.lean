import LeanCats.Relations
import LeanCats.Data
open CatRel
open Data

lemma internalImpliesPoOrPoMinusOne {e₁ e₂ : Event} (evts : Events) :
  internal evts e₁ e₂ -> e₁ ≠ e₂ -> Rel.po evts e₁ e₂ ∨ Rel.po evts e₂ e₁ :=
  by
    simp
    intro he₁in
    intro he₂in
    intro htideq
    intro hneq
    simp [Rel.po]
    have hidneq : e₁.id ≠ e₂.id :=
      by
        intro hideq
        apply hneq
        apply Iff.mpr
        apply evts.uniqueId
        exact hideq

    have hle_or_gt : e₁.id < e₂.id ∨ e₁.id > e₂.id :=
      by
        apply Iff.mp
        apply Nat.ne_iff_lt_or_gt
        exact hidneq

    induction hle_or_gt with
    | inl h => {
      apply Or.inl
      apply And.intro
      {
        aesop
      }
      {
        exact h
      }
    }
    | inr h => {
      apply Or.inr
      apply And.intro
      {
        simp [Eq.comm]
        aesop
      }
      {
        aesop
      }
    }

lemma rf_fr_is_co (evts : Events) (co : Events -> Rel Event Event) (e₁ e₂ e₃ : Event) :
  (rf.wellformed evts e₁ e₂ ∧ fr evts co e₂ e₃) = co evts e₁ e₃ :=
  by
    simp
    apply Iff.intro
    {
      intro hrffr
      have hrf : rf.wellformed evts e₁ e₂ := by apply And.left hrffr
      have hfr : fr evts co e₂ e₃ := by apply And.right hrffr
      simp at hfr
      have hwunique : e₂.act.op = Op.read -> (∃w, isWrite w ∧ rf evts w e₂) ∧ (∀ w₁ w₂, rf evts w₁ e₂ -> rf evts w₂ e₂ -> w₁ = w₂) :=
      by
        exact hrf.wExtAndUnique

      simp at *
      let ⟨w, hw⟩ := hfr
      -- At this point, what we want to get is w is e₁.
      have sameW :
        (∃ w, w.act.op = Op.write ∧ rf evts w e₂)
        ∧ ∀ (w₁ w₂ : Event), rf evts w₁ e₂ → rf evts w₂ e₂ → w₁ = w₂ :=
      by
        apply hwunique
        apply hrf.rRead
      have hwe₁ : (e₁ = w) :=
      by
        apply And.right sameW
        {
          obtain ⟨hrfin, hunique⟩ := hrf
          exact hrfin
        }
        {
          obtain ⟨left, mid, right⟩ := hw
          exact mid
        }

      obtain ⟨left, mid, right⟩ := hw
      rw [<-hwe₁] at right
      exact right
    }
    {
      sorry
    }
