import LeanCats.Data
import LeanCats.Relations

open Data
open CatRel

/-- Each execution is abstracted to a candidate execution 〈evts , po, rf, co, IW, sr〉 providing
This definination is different with the formal semantics, because the `co` is defined in [stdlib.cat](https://github.com/herd/herdtools7/blob/2a7599f8ecdbde0ed67925daf6534c1a0c26d535/herd-www/cat_includes/stdlib.cat) and
by computation, so should declare it as the base relation. -/
structure CandidateExecution
  (evts : Events)
  [IsStrictTotalOrder Event (preCo evts)]
  where
  (evts : Events)
  (_po : Rel Event Event)
  (_rf : Rel Event Event)
  (_fr : Rel Event Event)
  (_IW : Set Event)
