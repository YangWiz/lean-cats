import Mathlib.Data.Rel

inductive Thread : Type where
  | mk: Nat -> Thread
deriving BEq, Repr, DecidableEq

inductive Op : Type where
  | write : Op
  | read : Op
  | fence : Op
  | branch : Op
deriving BEq, Repr, DecidableEq

structure Action : Type where
  op: Op
  target : String
  -- For read, the value can not be determined at the begining.
  value : Option Nat
  isFirstWrite : Bool
  isFinalWrite : Bool
deriving BEq, Repr, DecidableEq

/-
-/
structure Event where
  (id : String)   -- Unique identifier
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (ln : Nat)        -- Line number or position
  (a : Action) -- Action performed
deriving BEq, Repr, DecidableEq

-- Events can be (for brevity this is not an exhaustive list):
-- writes, gathered in the set W, including the the set IW of initial writes coming from the prelude of the program;
-- reads, gathered in the set R;
-- branch events, gathered in the set B;
-- fences, gathered in the set F.
structure Events where
  (W : Set Event)
  (IW : Set Event)
  (R : Set Event)
  (B : Set Event)
  (F : Set Event)

def Events.empty : Events :=
  {
    W := {}
    IW := {}
    R := {}
    B := {}
    F := {}
  }

def Events.Inhabited : Inhabited Events :=
  { default := Events.empty }

-- Each execution is abstracted to a candidate execution 〈evts , po, rf, IW, sr〉 providing
structure CandidateExecution where
  (evts : Events)
  (po : Rel Event Event)
  (rf : Rel Event Event)
  (IW : Set Event)
  (sr : Rel Event Event)

def Rel.empty : Rel Event Event := fun _ _ => False
instance : EmptyCollection (Rel Event Event) := ⟨Rel.empty⟩

namespace CandidateExecution

def empty [Inhabited Events] : CandidateExecution :=
  { evts := default , po := Rel.empty, rf := Rel.empty, sr := Rel.empty, IW := {} }

-- def Events (ce : CandidateExecution) : Type :=
--   @Set.Elem Event {e | e ∈ ce.E}
--
-- def coeRel (ce : CandidateExecution) (r : Rel Event Event) :
--   Rel ce.Events ce.Events :=
--   fun x y => r x.val y.val
--
-- instance {ce : CandidateExecution} :
--   Coe (Rel Event Event) (Rel ce.Events ce.Events) :=
--   ⟨coeRel ce⟩
--
-- structure IsWellFormed (ce : CandidateExecution) where
--   poTotal : IsStrictTotalOrder ce.Events (ce.coeRel ce.po)
--   -- what else?

-- We later prove that this constructor makes well-formed CEs
-- This is not the case right now.
end CandidateExecution
