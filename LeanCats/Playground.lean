import Init.Data.List
import Mathlib.Data.Set.Basic

def comp_tc {α : Type} (elements : List α) (relation : α → α → Prop)
  [BEq α] [DecidableRel relation] : List (α × α) :=
  let direct_pairs := elements.product elements |>.filter (fun p => relation p.1 p.2)

  let expand (pairs : List (α × α)) : List (α × α) :=
    let new_pairs := pairs.flatMap (fun p1 =>
      pairs.flatMap (fun p2 =>
        if p1.2 == p2.1 && !(pairs.contains (p1.1, p2.2)) then
          [(p1.1, p2.2)]
        else
          []
      )
    )
    (pairs ++ new_pairs).eraseDups

  let max_iterations := elements.length * elements.length

  -- Use fold to iterate the fixed point computation
  List.range max_iterations |>.foldl
    (fun acc _ =>
      let next := expand acc
      if next.length == acc.length then acc else next)
    direct_pairs

def x : {n : ℕ // 4 ≤ n} := ⟨4, le_refl 4⟩

#eval x

variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩
