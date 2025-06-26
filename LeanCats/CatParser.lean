import Mathlib.Data.Rel
import LeanCats.Data
import Lean

section CatParser
open Lean.Meta Lean Lean.Expr Elab

abbrev Rty := Rel Event Event

abbrev E := List Event

declare_syntax_cat keyword
declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model

syntax "co" : keyword
syntax "rf" : keyword
syntax "fr" : keyword
syntax "po" : keyword
syntax "W" : keyword
syntax "R" : keyword
syntax "M" : keyword
syntax "emptyset" : keyword

syntax keyword : dsl_term
syntax num : dsl_term
syntax ident : dsl_term
syntax "(" expr ")" : dsl_term

syntax dsl_term : expr

syntax:50 expr:50 "|" expr:51 : expr
syntax expr "&" expr : expr
syntax:60 expr:60 "*" expr:61 : expr
syntax expr "^" expr : expr
syntax expr "+" expr : expr
syntax expr "-" expr : expr

syntax "let" ident "=" expr : inst
syntax "acyclic" expr : inst
syntax "irreflexive" expr : inst
syntax "empty" expr : inst
syntax "(*" ident* "*)" : inst
syntax "include" str : inst

syntax inst* : model

instance : Union (Rel Event Event) where
  union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y

instance : Inter (Rel Event Event) where
  inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y

@[simp] def fr' (rf' : Rty) (co' : Rty) (e₁ e₂ : Event) : Prop :=
  ∃w, w.a.action = write ∧ rf' w e₁ ∧ co' w e₂

@[simp] def R' (E : List Event) (e : Event) : Prop :=
  e ∈ E ∧ e.a.action = read

@[simp] def W' (E : List Event) (e : Event) : Prop :=
  e ∈ E ∧ e.a.action = write

@[simp] def M' (E : List Event) (e : Event) : Prop :=
  R' E e ∨ W' E e

@[simp] def Rel.prod (lhs rhs : List Event -> Event -> Prop) (E : List Event) (e₁ e₂ : Event) : Prop :=
  lhs E e₁ ∧ rhs E e₂

@[simp] def Rel.prod' (lhs rhs : Event -> Prop) : Rty :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

@[simp] def Acyclic (r : Rel Event Event) : Prop
  := Irreflexive (Relation.TransGen r)

@[simp] def mkAcyclicExpr (rel : Expr) : MetaM Expr := do
  mkAppM ``Acyclic #[rel]

@[simp] def mkIrreflexive (rel : Expr) : MetaM Expr := do
  mkAppM ``Irreflexive #[rel]

@[simp] def mkkeyword (E rf' co' po' : Expr) : Syntax -> MetaM Expr
  | `(keyword | emptyset) => return const ``List []
  | `(keyword | rf) => return rf'
  | `(keyword | co) => return co'
  | `(keyword | po) => return po'
  | `(keyword | W) => mkAppM `W' #[E]
  | `(keyword | R) => mkAppM `R' #[E]
  | `(keyword | M) => mkAppM `M' #[E]
  | `(keyword | fr) => mkAppM `fr' #[rf', co']
  | _ => throwUnsupportedSyntax

@[reducible, simp] def I (x : Rty) : Rty := x

mutual
partial def mkTerm (E rf' co' po' : Expr) (ctx : Array Name) : Syntax -> MetaM Lean.Expr
  | `(dsl_term | $lit:keyword ) => do
    mkkeyword E rf' co' po' lit
  | `(dsl_term | $lit:ident ) => do
    -- Look up the identifier in the context
    println! ctx
    match ctx.findIdx? (· == lit.getId) with
    | some idx =>
      let ret := .app (.const ``I []) (.bvar idx)
      return ret
    | none => throwError s!"Unknown identifier: {lit.getId}"
  | `(dsl_term | ( $e:expr )) => do
    mkExpr E rf' co' po' ctx e
  | _ => do
    println! "Failed to parse term"
    throwUnsupportedSyntax

partial def mkExpr (E rf' co' po' : Expr) (ctx : Array Name) : Syntax -> MetaM Lean.Expr
  | `(expr| $t:dsl_term ) => do
    mkTerm E rf' co' po' ctx t
  | `(expr | $e₁:expr * $e₂:expr) => do
    let lhs <- mkExpr E rf' co' po' ctx e₁
    let rhs <- mkExpr E rf' co' po' ctx e₂
    mkAppM ``Rel.prod' #[lhs, rhs]
  | `(expr | $e₁:expr | $e₂:expr)  => do
    let lhs <- mkExpr E rf' co' po' ctx e₁
    let rhs <- mkExpr E rf' co' po' ctx e₂
    mkAppM ``Union.union #[lhs, rhs]
  | `(expr | $e₁:expr & $e₂:expr) => do
    let lhs <- mkExpr E rf' co' po' ctx e₁
    let rhs <- mkExpr E rf' co' po' ctx e₂
    mkAppM ``Inter.inter #[lhs, rhs]
  | _ => do
    println! "Failed to parse binOp"
    throwUnsupportedSyntax
end

-- We need to create a body using recursion (we need to process the left, then this one), so we need a foldr.
-- We use a nameMap to store store the binding.
def mkInstruction (E : Expr) (rf' co' po' : Expr) (ctx : Array Name) (stx : Syntax) (restIns : Expr) : MetaM (Option Expr) :=
  match stx with
  | `(inst | let $i:ident = $e:expr) => do
    let ret := letE i.getId (.const `Rty []) (<-mkExpr E rf' co' po' ctx e) restIns true
    return ret
  | `(inst | acyclic $e:expr) => do
    let acyc <- mkAppM ``Acyclic #[<-mkExpr E rf' co' po' ctx e]
    mkAppM ``And #[acyc, restIns]
  | `(inst | irreflexive $e:expr) => do
    let irfx <- mkAppM ``Irreflexive #[<-mkExpr E rf' co' po' ctx e]
    mkAppM ``And #[irfx, restIns]
  | `(inst | (* $_:ident* *)) =>
    return none
  | `(inst | include $_:str) =>
    return none
  | _ => throwUnsupportedSyntax

-- This is used to collect all the binders.
-- We don't support variable shadowing.
def collectLetBindings (instructions : Array Syntax) : Array Name :=
  (instructions.filterMap fun stx =>
    match stx with
    | `(inst | let $i:ident = $_:expr) => some i.getId
    | _ => none).reverse

section test

def test : Rty := fun _ _ ↦ true
def testE : E := []

def mkModelTest : Syntax -> MetaM Expr
  | `(model| $ins:inst* ) => do
    let E : Expr := .const ``testE []
    let rf' : Expr := .const ``test []
    let co' : Expr := .const ``test []
    let po' : Expr := .const ``test []

    -- Create the base case (likely True or unit)
    let baseExpr : Expr := .const ``True []
    let ctx := collectLetBindings ins.raw

    ins.foldrM (fun stx acc => do
      let ins <- mkInstruction E rf' co' po' ctx stx acc
      match ins with
      | some i => return i
      | none => return acc
    ) baseExpr

  | _ =>
    throwUnsupportedSyntax

elab ">>" p:model "<<" : term => mkModelTest p

#check >> include "" let a' = rf let b = rf acyclic rf let a = rf acyclic W * W <<

end test

#check withLocalDeclsDND

def mkModel : Syntax -> MetaM Expr
  | `(model| $ins:inst* ) => do
    withLocalDeclsDND #[(`E', (.const `E [])), (`rf', (.const `Rty [])), (`co', (.const `Rty [])), (`po', (.const `Rty []))] ( λ params ↦ do
      -- Create the base case (likely True or unit)
      let baseExpr : Expr := .const ``True []
      let ctx := collectLetBindings ins.raw

      let body := ins.foldrM (fun stx acc => do
        let ctx := match stx with
        | `(inst | let $_:ident = $_:expr) => ctx.drop 1
        | _ => ctx

        let ins <- mkInstruction params[0]! params[1]! params[2]! params[3]! ctx stx acc

        match ins with
        | some i => return i
        | none => return acc
      ) baseExpr

      mkLambdaFVars params (<-body)
    )
  | _ =>
    throwUnsupportedSyntax

elab p:model : term => mkModel p

#check
  include "cos.cat"

  (* Communication relations that order events*)
  let com = rf | co | fr
  (* Program order that orders events *)
  let ppo = po & (W*W | R*M)

  let ghb = ppo | com
  acyclic ghb

end CatParser
