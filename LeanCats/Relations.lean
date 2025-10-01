import LeanCats.Data

namespace CatRel
open Data

def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y
def sequence (r₁ r₂ : Rel Event Event) := fun x z ↦ ∃ y, r₁ x y ∧ r₂ y z

-- Not sure if this is the correct definition of cartesian product.
def prod (s₁ s₂ : Set Event) : Rel Event Event := λ e₁ e₂ ↦ e₁ ∈ s₁ ∧ e₂ ∈ s₂

#check Rel.inv

@[simp] def internal : Rel Event Event :=
  λ e₁ e₂ ↦ e₁.t_id = e₂.t_id

@[simp] def external : Rel Event Event :=
  λ e₁ e₂ ↦ ¬(internal e₁ e₂)

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

end CatRel
