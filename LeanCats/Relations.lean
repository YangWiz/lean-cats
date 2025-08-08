import LeanCats.Data

abbrev Rty := Rel Event Event

abbrev E := List Event

namespace Event

def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y
def sequence (r₁ r₂ : Rel Event Event) := fun x z ↦ ∃ y, r₁ x y ∧ r₂ y z

instance instUnionRelEvents : Union (Event → Event → Prop) := ⟨union⟩
instance : Union (Rel Event Event) := instUnionRelEvents
instance : Inter (Rel Event Event) := ⟨inter⟩


@[simp] def fr (rf : Rty) (co : Rty) (e₁ e₂ : Event) : Prop :=
  ∃w, w.a.action = write ∧ rf w e₁ ∧ co w e₂

@[simp] def R (E : List Event) (e : Event) : Prop :=
  e ∈ E ∧ e.a.action = read

@[simp] def W (E : List Event) (e : Event) : Prop :=
  e ∈ E ∧ e.a.action = write

@[simp] def M (E : List Event) (e : Event) : Prop :=
  R E e ∨ W E e

@[simp] def Rel.prod (lhs rhs : List Event -> Event -> Prop) (E : List Event) (e₁ e₂ : Event) : Prop :=
  lhs E e₁ ∧ rhs E e₂

@[simp] def Rel.prod' (lhs rhs : Event -> Prop) : Rty :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

@[simp] def Acyclic (r : Rel Event Event) : Prop
  := Irreflexive (Relation.TransGen r)

end Event
