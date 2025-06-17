import Mathlib.Data.Rel
import LeanCats.Data
import Lean

open Lean.Meta Lean Lean.Expr Elab

abbrev R := Rel Event Event

#check NameMap

-- Create fvar for keyword (Abstract interface)
declare_syntax_cat keyword
declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat binOp
declare_syntax_cat instruction

syntax "co" : keyword
syntax "rf" : keyword
syntax "fr" : keyword
syntax "po" : keyword
syntax "emptyset" : keyword

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

syntax "let" ident "=" dsl_term : instruction

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

#check []

def mkkeyword : Syntax -> MetaM Expr
  | `(keyword | emptyset) => return const ``List []
  | `(keyword | rf) => return lam `rf (.const ``R []) (.bvar 0) default
  | `(keyword | co) => return lam `co (.const ``R []) (.bvar 0) default
  | `(keyword | po) => return lam `po (.const ``R []) (.bvar 0) default
  | `(keyword | fr) => return lam `rf (.const ``R []) (lam `co (.const ``R []) (<-mkAppM `fr #[(.bvar 0), (.bvar 1)]) default) default
  | _ => throwUnsupportedSyntax

elab k:keyword : term => do mkkeyword k

#check Lean.Meta.mkFreshExprMVarAt

#check withLocalDecls
#check withLocalDecl

def mkTerm : Syntax -> MetaM Expr
  | _ => throwUnsupportedSyntax

#check addDecl
#check Declaration
#check LocalContext.mkLocalDecl
#check mkFreshFVarId

#check λ x ↦
  let a := 3
  3

-- We use a nameMap to store store the binding.
def mkInstruction : Syntax -> MetaM Expr
  | `(instruction | let $i:ident = $t:dsl_term) => do
    withLocalDeclD `rf (.const `R []) (λ rf' ↦ withLocalDeclD `co (.const `R []) (
      λ e ↦ return .const `R
    ))
    _
  | _ => throwUnsupportedSyntax

-- It's right associative now.
partial def mkBinOp : Syntax -> MetaM Lean.Expr
  | `(binOp | $t:dsl_term | $e:expr) => do
    let ctx <- getLCtx
    let lhs <- mkTerm t
    let rhs <- mkExpr e
    mkAppM ``BinOp.union #[lhs, rhs]
  | `(binOp | $t:dsl_term & $e:expr) => do
    let lhs <- mkTerm t
    let rhs <- mkExpr e
    mkAppM ``BinOp.inter #[lhs, rhs]
  | _ => do
    println! "Failed to parse binOp"
    throwUnsupportedSyntax

#check Eq.trans

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
