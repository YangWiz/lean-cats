import LeanCats.Data

namespace CatRel
open Data

@[simp] def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
@[simp] def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y
@[simp] def sequence (r₁ r₂ : Rel Event Event) := fun x z ↦ ∃ y, r₁ x y ∧ r₂ y z

-- Not sure if this is the correct definition of cartesian product.
def prod (s₁ s₂ : Set Event) : Rel Event Event := λ e₁ e₂ ↦ e₁ ∈ s₁ ∧ e₂ ∈ s₂

#check Rel.inv

instance instUnionRelEvents : Union (Event → Event → Prop) := ⟨union⟩
instance : Union (Rel Event Event) := instUnionRelEvents
instance : Inter (Rel Event Event) := ⟨inter⟩

@[simp] def R : Set Event :=
  λ e ↦ e.act.op = Op.read

@[simp] def W : Set Event :=
  λ e ↦ e.act.op = Op.write

@[simp] def M : Set Event :=
  R ∪ W

@[simp] def Rel.prod (lhs rhs : List Event -> Event -> Prop) (E : List Event) (e₁ e₂ : Event) : Prop :=
  lhs E e₁ ∧ rhs E e₂

@[simp] def Rel.prod' (lhs rhs : Event -> Prop) : Rel Event Event :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

@[simp] def Acyclic (r : Rel Event Event) : Prop
  := Irreflexive (Relation.TransGen r)

@[simp] def Rel.internal (e₁ e₂ : Event) : Prop :=
  e₁.t_id = e₂.t_id

@[simp] def Rel.external (e₁ e₂ : Event) : Prop :=
  ¬ (Rel.internal e₁ e₂)

@[simp] def Rel.ident (X : CandidateExecution) (e₁ e₂ : Event) : Prop :=
  e₁ = e₂ -- ∧ e₁ ∈ X.evts

@[simp] def Rel.empty (_ _ : Event) : Prop :=
  False

@[simp] def Rel.loc (e₁ e₂ : Event) : Prop :=
  e₁.act.target = e₂.act.target

@[simp] def Rel.ext (e₁ e₂ : Event) : Prop :=
  e₁.t_id ≠ e₂.t_id

@[simp] def complus (evts : Events) (co : Events -> Rel Event Event) e1 e2 :=
  Rel.rf evts e1 e2 ∨ co evts e1 e2 ∨ Rel.fr evts co e1 e2 ∨
  sequence (co evts) (Rel.rf evts) e1 e2 ∨ sequence (Rel.fr evts co) (Rel.rf evts) e1 e2

-- instance PartialOrder: PartialOrder (Rel.rf evts e₁ e₂) :=
--   {
--     le_antisymm := _
--   }
structure rf (evts : Events) (e₁ e₂ : Event) where
  -- left one in the evts.
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : e₁.act.op = Op.write
  rRead : e₂.act.op = Op.read
  sameTarget : e₁.act.target = e₂.act.target

@[simp] def rf.wellformed (evts : Events) : Rel Event Event :=
  λ e₁ e₂ ↦ rf evts e₁ e₂
  ∧ ∀ r : Event, r.act.op = Op.read -> (∃w, rf evts w r)
  ∧ (∀ w₁ w₂, rf evts w₁ r -> rf evts w₂ r -> w₁ = w₂)

instance rf.strictOrder (evts : Events) : IsStrictOrder Event (rf evts) where
  irrefl :=
  by
    intro e
    intro hin
    have h₁ : e.act.op = Op.write := by apply hin.lWrite
    have h₂ : e.act.op = Op.read := by apply hin.rRead
    rw [h₁] at h₂
    contradiction
  trans :=
  by
    intro a b c
    intro hrfab
    intro hrfbc
    have lIn : a ∈ evts := by apply hrfab.lIn
    have rIn : c ∈ evts := by apply hrfbc.rIn
    have lWrite : a.act.op = Op.write := by apply hrfab.lWrite
    have rRead : c.act.op = Op.read := by apply hrfbc.rRead
    have sameTarget : a.act.target = c.act.target :=
    by
      have abSameTarget : a.act.target = b.act.target := by apply hrfab.sameTarget
      have bcSameTarget : b.act.target = c.act.target := by apply hrfbc.sameTarget
      rw [abSameTarget]
      rw [bcSameTarget]

    exact {
      lIn := lIn
      rIn := rIn
      lWrite := lWrite
      rRead := rRead
      sameTarget := sameTarget
    }

end CatRel
