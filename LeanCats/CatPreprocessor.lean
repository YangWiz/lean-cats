
namespace String
@[specialize]
def foldl2Aux {α : Type u} (f : α → Char → Char → α) (s : String) (stopPos : Pos) (i : Pos) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (String.lt_next s i)
    let nextIdx := s.next i
    match s.get? nextIdx with
      | none => a
      | some next =>
         foldl2Aux f s stopPos nextIdx (f a (s.get i) next)
  else a
termination_by stopPos.1 - i.1

@[inline] def foldl2 {α : Type u} (f : α → Char → Char → α) (init : α) (s : String) : α :=
  foldl2Aux f s s.endPos 0 init
end String

inductive InComment
  | entering
  | inside
  | leaving
  | outside
deriving Inhabited

@[inline]
private def process (accIncomment : String × InComment)  : Char → Char → String × InComment :=
  let ⟨acc, inComment⟩ := accIncomment
  fun c₁ c₂ => match c₁,c₂ with
  | '(', '*' => match inComment with
    | .outside => (acc, .entering)
    | .entering => panic! s!"Error (entering block, first) when removing comments at {acc}."
    | .leaving => panic! s!"Error (leaving block, first) when removing comments at {acc}."
    | .inside => (acc, .inside)
  | c@'*', ')' => match inComment with
    | .inside => (acc, .leaving)
    | .entering => (acc, .inside)
    | .leaving => panic! s!"Error (leaving block, second) when removing comments at {acc}."
    | .outside => (acc.push c, .outside)
  | c, _ => match inComment with
    | .inside => (acc, .inside)
    | .outside => (acc.push c, .outside)
    | .entering => match c with
      | '*' => (acc, .inside)
      | _ => panic! s!"Error (entering block) when removing comments at {acc}"
    | .leaving => match c with
      | ')' => (acc, .outside)
      | _ => panic! s!"Error (leaving block) when removing comments at {acc}"

def removeComments (input : String) : String :=
  -- add a `\n` in the end that should be ignored by size-2 window
  (input.push '\n').foldl2 process ({data := []}, .outside) |>.1

#eval removeComments "(**)"
#eval removeComments "(*)"
#eval removeComments "some(*)stuff"
#eval removeComments "some(**) stuff"
#eval removeComments "some(* stuff*) here"
#eval removeComments "some(*) stuff*) here"
#eval removeComments "(****)"
#eval removeComments "*)(****)(**)*("
#eval removeComments "this is a line \n(* \n a multi-line comment \n *)\n and then some "
