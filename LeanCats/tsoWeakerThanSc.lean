import LeanCats.Macro
import LeanCats.Reader
import LeanCats.Data
import LeanCats.Relations
import LeanCats.Theoriems
import LeanCats.Basic

-- -- include "cos.cat"
-- [model| sc
--   let com = rf | co | fr
--   let poo = po & (W*W | R*M)
--
--   let ghb = po | com
--   acyclic ghb as new
-- ]
--
-- [model| tso
--   let com_tso = rf | co | fr
--   let po_tso = po & (W*W | R*M)
--   let ghb = po_tso | com_tso
--   acyclic ghb as new
-- ]
--
-- #check sc.new
-- #check tso.new

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
  intro a b
  intro tso
  cases tso with
  | inl h => {
    simp at h
    apply Or.inr
    obtain ⟨l, r⟩ := h
    exact l
  }
  | inr h => {
    obtain ⟨l⟩ := h
    {
      apply Or.inl
      apply Or.inl
      obtain ⟨l, r⟩ := l
      exact r
    }
    {
      rename_i h
      apply Or.inl
      apply Or.inr
      exact h
    }
  }
