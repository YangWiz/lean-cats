import LeanCats.Data
import LeanCats.AST

namespace LitmusParser

def ins2event
  (t_id : Nat)
  (thread : Thread)
  (ins : LitmusAST.Instruction)
  (id : String) : Event :=
  {
    id := id
    t_id := t_id
    t := thread
    ln := ins.line_num
    a := ins.action
  }

def prog2events (prog : LitmusAST.Program) (start_id : Nat) : List Event × Nat :=
  let thread : Thread := Thread.mk prog.thread
  let ins2event := ins2event prog.thread thread

  let rec process_instructions (instructions : List LitmusAST.Instruction) (curr_id : Nat) : List Event × Nat :=
    match instructions with
    | [] => ([], curr_id)
    | ins :: rest =>
      let id_str := toString curr_id
      let event := ins2event ins id_str
      let (rest_events, next_id) := process_instructions rest (curr_id + 1)
      (event :: rest_events, next_id)

  process_instructions prog.instructions start_id

def zip_instructions (insts : List Event) : Set (Event × Event) :=
  -- [r₁ r₂ r₂] -> [r₁ r₂] [r₂ r₃] -> [(r₁, r₂), (r₂, r₃)]
  -- edge caes: return []
  let insts₁ := insts.eraseIdx 0
  let insts₂ := insts.dropLast

  let insts := insts₁.zip insts₂

  -- accumulate all the relations.
  -- insts.foldl Primitives.R.add Primitives.R.empty
  sorry

-- def get_po (litmus : LitmusAST.Litmus) : Relation :=
--   let start : Nat := 0
--
--   let rec process_programs (program : List LitmusAST.Program) (curr_id : Nat) : List (List Event) × Nat :=
--     match program with
--     | [] => ([], curr_id)
--     | prog :: rest =>
--       let (prog_events, next_id) := prog2events prog curr_id
--       let (rest_programs_events, final_id) := process_programs rest next_id
--       (prog_events :: rest_programs_events, final_id)
--
--   let (all_program_events, _) := process_programs litmus.programs start
--
--   let events_list := all_program_events.map zip_instructions
--
--   -- events_list.foldl Set.union R.empty
--   sorry

def get_rf (litmus : LitmusAST.Litmus) : Relation :=
  sorry

def get_fr (litmus : LitmusAST.Litmus) : Relation :=
  sorry

-- There are lots of algorithms to find the read-from relation, like use-def chains (worklist to find)
-- But for the sake of simplicity, we just use brute-force O(N!).

end LitmusParser
