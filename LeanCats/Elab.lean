import Mathlib.Data.Rel
import LeanCats.Data
import LeanCats.CatPreprocessor
import LeanCats.Relations
import LeanCats.Syntax
import Lean


section CatParser
open Lean.Meta Lean Lean.Expr Elab


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
  | `(expr | $e₁:expr ; $e₂:expr) => do
    let lhs <- mkExpr E rf' co' po' ctx e₁
    let rhs <- mkExpr E rf' co' po' ctx e₂
    mkAppM ``Sequence #[lhs, rhs]

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
  (instructions.filterMap λ stx ↦
    match stx with
    | `(inst | let $i:ident = $_:expr) => some i.getId
    | _ => none).reverse

section test

def test : Rty := λ _ _ ↦ true
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

    ins.foldrM (λ stx acc ↦ do
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

def mkModel : Syntax -> MetaM Expr
  | `(model| $ins:inst* ) => do
    withLocalDeclsDND #[(`E', (.const `E [])), (`rf', (.const `Rty [])), (`co', (.const `Rty [])), (`po', (.const `Rty []))] ( λ params ↦ do
      -- Create the base case (likely True or unit)
      let baseExpr : Expr := .const ``True []
      let ctx := collectLetBindings ins.raw

      let body := ins.foldrM (λ stx acc ↦ do
        -- Because it's foldr, the iteration works from right to left so we drop the closest binder when we meet one.
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

elab "[cat|" p:model "]" : term => mkModel p

-- parser hack
def parseModel (file : String) : Lean.MetaM Lean.Expr := do
  let raw <- IO.FS.readFile file
  let s := removeComments raw
  let env: Lean.Environment <- Lean.getEnv
  let stx?: Except String Lean.Syntax := Lean.Parser.runParserCategory env `model s
  let stx : Lean.Syntax <- Lean.ofExcept stx?
  mkModel stx


#check [cat|
  include "cos.cat"

  (* Communication relations that order events*)
  let com = rf | co | fr
  (* Program order that orders events *)
  let ppo = po & (W*W | R*M)

  let ghb = ppo | com
  acyclic ghb
  ]

end CatParser
