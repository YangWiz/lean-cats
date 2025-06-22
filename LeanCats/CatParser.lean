import Mathlib.Data.Rel
import LeanCats.Data
import Lean

open Lean.Meta Lean Lean.Expr Elab

abbrev R := Rel Event Event

-- Create fvar for keyword (Abstract interface)
declare_syntax_cat keyword
declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat binOp
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model

syntax "co" : keyword
syntax "rf" : keyword
syntax "fr" : keyword
syntax "po" : keyword
syntax "emptyset" : keyword

syntax "(*" ident* "*)" : comment

syntax keyword : dsl_term
syntax num : dsl_term
syntax ident : dsl_term
syntax "(" expr ")" : dsl_term

syntax dsl_term : expr
syntax binOp : expr

syntax dsl_term "|" expr: binOp
syntax dsl_term "&" expr: binOp
syntax dsl_term "^" dsl_term: binOp
syntax dsl_term "+" dsl_term: binOp
syntax dsl_term "-" dsl_term: binOp

syntax "let" ident "=" expr : inst
syntax "acyclic" expr : inst
syntax "irreflexive" expr : inst
syntax "empty" expr : inst

syntax inst* : model

instance : Union (Rel Event Event) where
  union (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∨ r₂ x y

instance : Inter (Rel Event Event) where
  inter (r₁ r₂ : Rel Event Event) := λ x y ↦ r₁ x y ∧ r₂ x y

def fr' (rf' : R) (co' : R) (e₁ e₂ : Event) : Prop :=
  ∃w, w.a.action = write ∧ rf' w e₁ ∧ co' w e₂

def Acyclic (r : Rel Event Event) : Prop
  := Irreflexive (Relation.TransGen r)

def mkAcyclicExpr (rel : Expr) : MetaM Expr := do
  mkAppM ``Acyclic #[rel]

def mkIrreflexive (rel : Expr) : MetaM Expr := do
  mkAppM ``Irreflexive #[rel]

def mkkeyword (rf' co' po' : Expr) : Syntax -> MetaM Expr
  | `(keyword | emptyset) => return const ``List []
  | `(keyword | rf) => return rf'
  | `(keyword | co) => return co'
  | `(keyword | po) => return po'
  | `(keyword | fr) => mkAppM `rf #[rf', co']
  | _ => throwUnsupportedSyntax

@[reducible, simp] def I (x : R) : R := x

mutual
partial def mkTerm (rf' co' po' : Expr) (ctx : Array Name) : Syntax -> MetaM Lean.Expr
  | `(dsl_term | $lit:ident ) => do
    -- Look up the identifier in the context
    match ctx.findIdx? (· == lit.getId) with
    | some idx =>
      let ret := .app (.const ``I []) (.bvar idx)
      return ret
    | none => throwError s!"Unknown identifier: {lit.getId}"
  | `(dsl_term | $lit:keyword ) => do
    mkkeyword rf' co' po' lit
  | _ => do
    println! "Failed to parse term"
    throwUnsupportedSyntax

partial def mkExpr (rf' co' po' : Expr) (ctx : Array Name) : Syntax -> MetaM Lean.Expr
  | `(expr| $e:binOp ) => do
    mkBinOp rf' co' po' ctx e
  | `(expr| $t:dsl_term ) => do
    -- mkTerm rf' co' po' t
    mkTerm rf' co' po' ctx t
  | _ => do
    println! "Failed to parse expr"
    throwUnsupportedSyntax

partial def mkBinOp (rf' co' po' : Expr) (ctx : Array Name) : Syntax -> MetaM Lean.Expr
  | `(binOp | $t:dsl_term | $e:expr) => do
    let lhs <- mkTerm rf' co' po' ctx t
    let rhs <- mkExpr rf' co' po' ctx e
    mkAppM ``Union.union #[lhs, rhs]
  | `(binOp | $t:dsl_term & $e:expr) => do
    let lhs <- mkTerm rf' co' po' ctx t
    let rhs <- mkExpr rf' co' po' ctx e
    mkAppM ``Inter.inter #[lhs, rhs]
  | _ => do
    println! "Failed to parse binOp"
    throwUnsupportedSyntax
end

-- We need to create a body using recursion (we need to process the left, then this one), so we need a foldr.
-- We use a nameMap to store store the binding.
def mkInstruction (rf' co' po' : Expr) (ctx : Array Name) (stx : Syntax) (restIns : Expr) : MetaM Expr :=
  match stx with
  | `(inst | let $i:ident = $e:expr) => do
    logInfo restIns
    let ret := letE i.getId (.const `R []) (<-mkExpr rf' co' po' ctx e) restIns true
    logInfo ret
    return ret
  | `(inst | acyclic $e:expr) => do
    let acyc <- mkAppM ``Acyclic #[<-mkExpr rf' co' po' ctx e]
    mkAppM ``And #[acyc, restIns]
  | `(inst | irreflexive $e:expr) => do
    let irfx <- mkAppM ``Irreflexive #[<-mkExpr rf' co' po' ctx e]
    mkAppM ``And #[irfx, restIns]
  | _ => throwUnsupportedSyntax

-- This is used to collect all the binders.
-- We don't support variable shadowing.
def collectLetBindings (instructions : Array Syntax) : Array Name :=
  (instructions.filterMap fun stx =>
    match stx with
    | `(inst | let $i:ident = $_:expr) => some i.getId
    | _ => none).reverse

section test

def test : R := fun _ _ ↦ true

def mkModelTest : Syntax -> MetaM Expr
  | `(model| $ins:inst* ) => do
    let rf' : Expr := .const ``test []
    let co' : Expr := .const ``test []
    let po' : Expr := .const ``test []

    -- Create the base case (likely True or unit)
    let baseExpr : Expr := .const ``True []
    let ctx := collectLetBindings ins.raw

    ins.foldrM (fun stx acc => do
      let ins := mkInstruction rf' co' po' ctx stx acc
      ins
    ) baseExpr

  | _ =>
    throwUnsupportedSyntax

elab ">>" p:model "<<" : term => mkModelTest p
#reduce >> let a' = rf let b = rf acyclic rf let a = rf acyclic a' <<

end test

#check withLocalDeclsDND

def mkModel : Syntax -> MetaM Expr
  | `(model| $ins:inst* ) => do
    withLocalDeclsDND #[(`rf', (.const `R [])), (`co', (.const `R [])), (`po', (.const `R []))] ( λ params ↦ do
      -- Create the base case (likely True or unit)
      let baseExpr : Expr := .const ``True []
      let ctx := collectLetBindings ins.raw

      let body := ins.foldrM (fun stx acc => do
        let ins := mkInstruction params[0]! params[1]! params[2]! ctx stx acc
        ins
      ) baseExpr

      mkLambdaFVars params (<-body)
    )
  | _ =>
    throwUnsupportedSyntax

elab p:model : term => mkModel p
#reduce let a' = rf let b = rf acyclic co let a = rf acyclic a'
