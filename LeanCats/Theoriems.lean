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
