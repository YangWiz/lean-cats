import LeanCats.Data

namespace CatRel
open Data

def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y
def sequence (r₁ r₂ : Rel Event Event) := fun x z ↦ ∃ y, r₁ x y ∧ r₂ y z

instance instUnionRelEvents : Union (Event → Event → Prop) := ⟨union⟩
instance : Union (Rel Event Event) := instUnionRelEvents
instance : Inter (Rel Event Event) := ⟨inter⟩

@[simp] def fr (rf co : Rel Event Event) (e₁ e₂ : Event) : Prop :=
  ∃w, w.act.op = Op.write ∧ rf w e₁ ∧ co w e₂

@[simp] def R (e : Event) : Prop :=
  e.act.op = Op.read

@[simp] def W (e : Event) : Prop :=
  e.act.op = Op.write

@[simp] def M (e : Event) : Prop :=
  R e ∨ W e

@[simp] def Rel.prod (lhs rhs : List Event -> Event -> Prop) (E : List Event) (e₁ e₂ : Event) : Prop :=
  lhs E e₁ ∧ rhs E e₂

@[simp] def Rel.prod' (lhs rhs : Event -> Prop) : Rel Event Event :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

@[simp] def Acyclic (r : Rel Event Event) : Prop
  := Irreflexive (Relation.TransGen r)

@[simp] def Rel.internal (evts : Set Event) (e₁ e₂ : Event) : Prop :=
  e₁.t_id = e₂.t_id ∧ e₁ ∈ evts ∧ e₂ ∈ evts

@[simp] def Rel.external (evts : Set Event) (e₁ e₂ : Event) : Prop :=
  ¬ (Rel.internal evts e₁ e₂)

@[simp] def Rel.ident (X : CandidateExecution) (e₁ e₂ : Event) : Prop :=
  e₁ = e₂ -- ∧ e₁ ∈ X.evts

@[simp] def Rel.empty (_ _ : Event) : Prop :=
  False

@[simp] def Rel.loc (e₁ e₂ : Event) : Prop :=
  e₁.act.target = e₂.act.target

@[simp] def Rel.ext (e₁ e₂ : Event) : Prop :=
  e₁.t_id ≠ e₂.t_id

end CatRel
