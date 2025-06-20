import LeanCats.AST
import Mathlib.Data.Set.Basic
import Init.Data.List.Basic
import Init.System.IO

/-
  The cat language is much inspired by OCaml, featuring immutable bindings, first-class functions, pattern matching, etc.
  However, cat is a domain specific language, with important differences from OCaml.

  Base values are specialised, they are sets of events and relations over events.
  There are also tags, akin to C enumerations or OCaml “constant” constructors and first class functions. Moreover, events can be extracted from sets and pair of events (element of relations) from relations.

  There are two structured values: tuples of values and sets of values. One should notice that primitive set of events and structured set of events are not the same thing.
  In fact, the language prevents the construction of structured set of events. Similarily, there are no structured sets of elements of relations, there are only relations.
  There is a distinction between expressions that evaluate to some value, and instructions that are executed for their effect.

  A model, or cat program is a sequence of instructions. At startup, pre-defined identifiers are bound to event sets and relations over events.
  Those pre-defined identifiers describe a candidate execution (in the sense of the memory model). Executing the model means allowing or forbidding that candidate execution.

  -- Identifiers.
  -- Expressions.
  -- Instructions.
-/

namespace Cats
open CatsAST
open Lean Elab Meta

def empty_set : List Event := []

def mkLit : Syntax -> MetaM Lean.Expr
  | lit => mkAppM ``CatsAST.liter #[mkStrLit lit.getId.toString]

declare_syntax_cat binOp
declare_syntax_cat instruction
declare_syntax_cat expr
declare_syntax_cat binding
declare_syntax_cat const
declare_syntax_cat acyclic
declare_syntax_cat dsl_term
declare_syntax_cat comment
declare_syntax_cat model

syntax binding : instruction
syntax acyclic : instruction

syntax num : dsl_term
syntax ident : dsl_term
syntax "(" expr ")" : dsl_term

syntax "acyclic" expr ("as" expr)? : acyclic
syntax "let" expr "=" expr : binding

syntax dsl_term : expr
syntax binOp : expr

syntax num : const
syntax str : const

syntax dsl_term "|" expr: binOp
syntax dsl_term "&" expr: binOp
syntax dsl_term "^" dsl_term: binOp
syntax dsl_term "+" dsl_term: binOp
syntax dsl_term "-" dsl_term: binOp

-- syntax (comment+) : model
syntax instruction* : model

mutual -- mutual recursion.

-- It's right associative now.
partial def mkBinOp : Syntax -> MetaM Lean.Expr
  | `(binOp | $t:dsl_term | $e:expr) => do
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

partial def mkExpr : Syntax -> MetaM Lean.Expr
  | `(expr| $e:binOp ) => do
    let binop <- mkBinOp e
    mkAppM ``Expr.binop #[binop]
  | `(expr| $t:dsl_term ) => do
    let t <- mkTerm t
    mkAppM ``Expr.term #[t]
  | _ => do
    println! "Failed to parse expr"
    throwUnsupportedSyntax

partial def mkTerm : Syntax -> MetaM Lean.Expr
  -- | `(dsl_term | ( $e:expr ) ) => CatsAST.Term.expr <$> (mkExpr e)
  | `(dsl_term | $lit:ident ) => do
    mkAppM ``CatsAST.Term.liter #[mkStrLit lit.getId.toString]
  | _ => do
    println! "Failed to parse term"
    throwUnsupportedSyntax

end

def mkBinding : Syntax -> MetaM Lean.Expr
  | `(binding| let $n = $e ) => do
    let n <- mkExpr n
    let e <- mkExpr e
    mkAppM ``Binding.varbinding #[n, e]
  -- TODO(Zhiyang) will implement pat binding (function binding) later.
  | _ => throwUnsupportedSyntax

def mkAcyclic : Syntax -> MetaM Lean.Expr
  | `(acyclic| acyclic $e ) => do
    let e <- mkExpr e
    mkAppM ``Acyclic.expr #[e]
  | `(acyclic| acyclic $e as $n ) => do
    let e <- mkExpr e
    let n <- mkExpr n
    mkAppM ``AcyclicAs.expr #[n, e]
  | _ => throwUnsupportedSyntax
--
-- def mkInstruction : Syntax -> Except String Instruction
--   -- | `(instruction| $b:binding) => Instruction.binding <$> (mkBinding b)
--   | `(instruction| $e:expr ) => Instruction.expr <$> (mkExpr e)
--   | `(instruction| $a:acyclic ) => Instruction.acyclic <$> (mkAcyclic a)
--   | _ => throw "Failed to parse statement"
--
def mkInstruction : Syntax -> MetaM Lean.Expr
  | `(instruction| $b:binding) => do
    let binding <- mkBinding b
    mkAppM ``Instruction.binding #[binding]
  -- | `(instruction| $e:expr ) => Instruction.expr <$> (mkExpr e)
  | `(instruction| $a:acyclic ) => do
    let acyc <- (mkAcyclic a)
    mkAppM ``Instruction.acyclic #[acyc]
  | _ => do
    println! "Failed to parse instruction"
    throwUnsupportedSyntax


#check foldlM
#check List.map

-- elab m:model : term => do
--   match m with
--   | `(model| $ins:instruction*) => do
--     let ins_list <- liftMetaM $ Array.mapM mkInstruction ins.raw
--
--     let instructions <- mkListLit (.const ``Instruction []) ins_list.toList
--     mkAppM ``CatsAST.Model.instructions #[instructions]
--   | _ =>
--     println! "Failed to parse model."
--     throwUnsupportedSyntax

elab m:model : term => do
  match m with
  | `(model| $ins:instruction*) => do
    let ins_list <- liftMetaM $ Array.mapM mkInstruction ins.raw

    let instructions <- mkListLit (.const ``Instruction []) ins_list.toList
    mkAppM ``CatsAST.Model.instructions #[instructions]
  | _ =>
    throwUnsupportedSyntax

--
-- #check
--   let a = amo
--
-- abbrev output := IO
--
def test :=
  let a := 1
  let a := 2

def prog :=
  let a = rf | fr
  acyclic a
--
-- #reduce prog
-- def mkAssignment : Syntax -> Except String Assignment
--   | `(Assignment| let $n:name = $e:Expr ) => return (Stmt.assignment (mkExpr e.) (mkExpr e))
--   | _ => throw "Failed to parse assignement statement."

-- elab v:num : const => mkConst v

def prop_test (a : Bool) : Prop := ¬ a

def t₁ (a : Prop) := [¬a]

-- We get a list of Prop, the Prop is what we need to prove.


#reduce prog

#check t₁

end Cats

#check IO String
