import LeanCats.Data

namespace CatRel
open Data

@[simp] def union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y
@[simp] def inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y

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

@[simp] def isWrite (e : Event) : Prop :=
  e.act.op = Op.write

structure rf (evts : Events) (e₁ e₂ : Event) : Prop where
  -- left one in the evts.
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : e₁.act.op = Op.write
  rRead : e₂.act.op = Op.read
  sameTarget : e₁.act.target = e₂.act.target

@[simp] def fr (evts : Events) (co : Events -> Rel Event Event) (e1 e2 : Event) : Prop :=
  ∃w, isWrite w ∧ rf evts w e1 ∧ co evts w e2

instance (evts : Events) : IsStrictOrder Event (rf evts) where
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

    exact ⟨lIn, rIn, lWrite, rRead, sameTarget⟩

-- This defines:
-- Write event must exists
-- Write equlity (If the two write events write to the same read event, then these two writes are the same)
structure rf.wellformed (evts : Events) (e₁ e₂ : Event) extends rf evts e₁ e₂ where
  wExtAndUnique {r} : r.act.op = Op.read ->
    (∃w, isWrite w ∧ rf evts w r)
    ∧ (∀ w₁ w₂, rf evts w₁ r -> rf evts w₂ r -> w₁ = w₂)

def comPlus (evts : Events) (co : Events -> Rel Event Event) (e₁ e₂ : Event) :=
  rf evts e₁ e₂ ∨ co evts e₁ e₂ ∨ fr evts co e₁ e₂
  ∨ Relation.Comp (co evts) (rf evts) e₁ e₂ ∨ Relation.Comp (fr evts co) (rf evts) e₁ e₂

def com (evts : Events) (co : Events -> Rel Event Event) (e₁ e₂ : Event) :=
  rf evts e₁ e₂ ∨ co evts e₁ e₂ ∨ fr evts co e₁ e₂


end CatRel
