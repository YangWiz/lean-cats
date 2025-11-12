import LeanCats.Relations
import LeanCats.Data
open Relation
open CatRel
open Data

-- Relation composition (Relation sequence in cat definition).
infix:61 ";" => Comp

def phx (r₁ r₂ : Rel Event Event) := ReflGen (TransGen (r₁ ; r₂))

@[simp] def hx (r₁ r₂ : Rel Event Event) := (ReflGen r₁ ; phx r₁ r₂) ; ReflGen r₂

lemma hxIsTransitive
  (r₁ r₂ : Rel Event Event)
  (hr₁ : Transitive r₁)
  (hr₂ : Transitive r₂)
  : Transitive (hx r₁ r₂) :=
  by
    unfold Transitive
    intro x y z
    intro hxy
    intro hyz
    simp at hxy
    unfold Comp at hxy

-- Key lemma
lemma CycleInUnionImpliesCycleInComp
  {r₁ r₂ : Rel Event Event}
  (hnrlxr₁ : Irreflexive r₁)
  (hnrlxr₂ : Irreflexive r₂)
  (htransr₁ : Transitive r₁)
  (htransr₂ : Transitive r₂) :
  Irreflexive (TransGen (r₁ ∪ r₂)) -> Irreflexive (TransGen (r₁ ; r₂)) := sorry


lemma internalImpliesPoOrPoMinusOne {e₁ e₂ : Event} (evts : Events) :
  internal evts e₁ e₂ -> e₁ ≠ e₂ -> po evts e₁ e₂ ∨ po evts e₂ e₁ :=
  by
    simp
    intro he₁in
    intro he₂in
    intro htideq
    intro hneq
    simp [po]
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

lemma rfAndFrIsCo (evts : Events) (co : Events -> Rel Event Event) (e₁ e₂ e₃ : Event) :
  (rf.wellformed evts e₁ e₂ ∧ fr evts co e₂ e₃) -> co evts e₁ e₃ :=
  by
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

-- lemma scIsTransitive (evts : Events) (co : Events -> Rel Event Event) : Transitive (sc evts co) :=
--   by
--     unfold Transitive
--     intro a b c
--     intro hab
--     intro hbc

class StrictPartialOrder (r : Rel Event Event) extends IsStrictOrder Event r, IsAsymm Event r

lemma strictPartialOrderImpliesAcyclic
  {r : Rel Event Event}
  [hr : StrictPartialOrder r]
  (e : Event) :
  ¬TransGen r e e :=
  by
    rw [Relation.transGen_eq_self]
    {
      apply hr.irrefl
    }
    {
      unfold Transitive
      apply hr.trans
    }

--- tso : Relation.TransGen
---   (Rel.po evts ∩ (prod W W ∪ prod R (R ∪ W)) ∪ union (external evts ∪ Rel.rf evts) (co evts ∪ Rel.fr evts co)) x x
--- ⊢ Relation.TransGen (fun x y => (Rel.rf evts x y ∨ co evts x y ∨ Rel.fr evts co x y) ∨ Rel.po evts x y) ?x ?x
