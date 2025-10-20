import Mathlib.Data.Rel

namespace Data

inductive Thread : Type where
  | mk: Nat -> Thread
deriving Inhabited, BEq, Repr, DecidableEq

inductive Op : Type where
  | write : Op
  | read : Op
  | fence : Op
  | branch : Op
deriving Inhabited, BEq, Repr, DecidableEq

structure Action : Type where
  op: Op
  target : String
  -- For read, the value can not be determined at the begining.
  value : Option Nat
  isFirstWrite : Bool
  isFinalWrite : Bool
deriving Inhabited, BEq, Repr, DecidableEq

structure Event where
  (id : Nat)   -- Unique identifier
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (ln : Nat)        -- Line number or position
  (act : Action) -- Action performed
deriving Inhabited, BEq, Repr, DecidableEq

abbrev evt := Event

inductive error

inductive Judgement
  | Allowed : Judgement
  | Forbidden: Judgement

-- Events can be (for brevity this is not an exhaustive list):
-- writes, gathered in the set W, including the the set IW of initial writes coming from the prelude of the program;
-- reads, gathered in the set R;
-- branch events, gathered in the set B;
-- fences, gathered in the set F.
structure Events where
  (uniqueId : ∀e₁ e₂ : Event, e₁ = e₂ -> e₁.id = e₁.id)
  (W : Set Event)
  (IW : Set Event)
  (R : Set Event)
  (B : Set Event)
  (F : Set Event)
  (RMW : Set Event)

instance : Membership Event Events where
  mem evts evt := evt ∈ evts.B ∪ evts.F ∪ evts.IW ∪ evts.R ∪ evts.RMW ∪ evts.W

def Rel.rf (e₁ e₂ : Event) : Prop :=
  e₁.act.op = Op.write ∧ e₂.act.op = Op.read ∧ e₁.act.target = e₂.act.target

def Rel.fr (co : Rel Event Event) (e₁ e₂ : Event) : Prop :=
  ∃ w: Event, w.act.op = Op.write ∧ Rel.rf w e₁ ∧ co w e₂

def Rel.po (e₁ e₂ : Event) : Prop :=
  e₁.t_id = e₂.t_id ∧ e₁.ln < e₂.ln

/-- Each execution is abstracted to a candidate execution 〈evts , po, rf, co, IW, sr〉 providing
This definination is different with the formal semantics, because the `co` is defined in [stdlib.cat](https://github.com/herd/herdtools7/blob/2a7599f8ecdbde0ed67925daf6534c1a0c26d535/herd-www/cat_includes/stdlib.cat) and
by computation, so should declare it as the base relation. -/
structure CandidateExecution where
  (evts : Events)
  (po : Rel Event Event)
  (rf : Rel Event Event)
  (fr : Rel Event Event)
  (IW : Set Event)

end Data
