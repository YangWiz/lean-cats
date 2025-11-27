import LeanCats.Macro
import LeanCats.Reader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theoriems
import LeanCats.Basic

defcat <"tso.cat">
defcat <"sc.cat">

theorem scvtso
  (evts : Data.Events)
  [IsStrictTotalOrder Data.Event (CatRel.preCo evts)]
  (X : CandidateExecution evts)
  : sc.sc evts X → tso.tso evts X :=
by
  unfold sc.sc
  simp
  intro sc
  apply ayclicMono sc
  simp
  intro a b
  intro tso

  cases tso with
  | inl h => {
    simp at h
    apply Or.inl
    obtain ⟨l, r⟩ := h
    exact l
  }
  | inr h => {
    obtain ⟨l⟩ := h
    {
      apply Or.inr
      apply Or.inl
      exact l
    }
    {
      rename_i h
      apply Or.inr
      apply Or.inr
      aesop
    }
  }
