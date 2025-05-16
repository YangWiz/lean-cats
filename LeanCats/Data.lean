inductive Thread : Type where
  | mk: Nat -> Thread
deriving BEq, Repr, DecidableEq

abbrev write := "write"
abbrev read := "read"

/-
Actions are of several kinds, which we detail in the course of this article. For now, we
only consider read and write events relative to memory locations. For example, for the
location x, we can have a read of the value 0 noted Rx = 0, or a write of the value 1,
noted Wx = 1. We write proc(e) for the thread holding the event e and addr(e) for its
address, or memory location.
-/
structure Action : Type where
  action : String
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
