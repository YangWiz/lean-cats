-- AST
namespace CatsAST

abbrev Ident := String
abbrev liter := Ident -> Ident

def e.w : Ident := "write"
def e.r : Ident := "read"
def e.m : Ident := "memory"
def e.iw : Ident := "initial_write"
def e.fw : Ident := "final_write"
def e.b : Ident := "branch"
def e.rmw : Ident := "read_modify_write"
def e.f : Ident := "fence"

def r.po : Ident := "program_order"
def r.addr : Ident := "address_dependency"
def r.data : Ident := "data_dependency"
def r.ctrl : Ident := "control_dependency"
def r.rmw : Ident := "read_modify_write_pair"
def r.amo : Ident := "atomic_modify"
def r.rf : Ident := "read_from"
def r.fr : Ident := "from_read"
def r.co : Ident := "coherence_order"

mutual
inductive BinOp
  | union : Term -> Expr -> BinOp
  | inter : Term -> Expr -> BinOp
  | diff : Term -> Expr -> BinOp

inductive Term where
  | name : Expr -> Term
  | negation : Term -> Term
  -- Expr itself is also a Term.
  | keyword : String -> Term
  | expr: Expr -> Term
  | liter: String -> Term

inductive Expr where
  | id : Nat -> Expr
  | term : Term -> Expr
  | binop : BinOp -> Expr

end

mutual
  partial def toStringAuxBinOp : BinOp → String
    | .union t e => s!"({toStringAuxTerm t} union {toStringAuxExpr e})"
    | .inter t e => s!"({toStringAuxTerm t} inter {toStringAuxExpr e})"
    | .diff t e => s!"({toStringAuxTerm t} diff {toStringAuxExpr e})"

  partial def toStringAuxTerm : Term → String
    | .name e => s!"name({toStringAuxExpr e})"
    | .negation t => s!"¬{toStringAuxTerm t}"
    | .keyword s => s!"keyword({s})"
    | .expr e => toStringAuxExpr e
    | .liter s => s!"{s}"

  partial def toStringAuxExpr : Expr → String
    | .id n => s!"id({n})"
    | .term t => toStringAuxTerm t
    | .binop b => toStringAuxBinOp b

  partial instance : ToString BinOp where
    toString b := toStringAuxBinOp b

  partial instance : ToString Term where
    toString t := toStringAuxTerm t

  partial instance : ToString Expr where
    toString e := toStringAuxExpr e
end


inductive Stmt
  | expr : Expr -> Stmt
  | comment : String -> Stmt
  | assignment : Expr -> Expr -> Stmt

inductive Binding
  -- valbinding ::=	id -> expr
  | varbinding : Expr -> Expr -> Binding
  -- funbinding := id -> pad -> expr
  | funbinding : Expr -> Expr -> Expr -> Binding

inductive Acyclic
  | expr : Expr -> Acyclic

inductive AcyclicAs
  | expr : Expr -> Expr -> AcyclicAs

inductive Instruction
  | binding : Binding -> Instruction
  | expr : Expr -> Instruction
  | check : String -> Expr -> Instruction
  | acyclic : Acyclic -> Instruction

inductive Model
  | instructions : List Instruction -> Model

partial def toStringStmt : Stmt -> String
  | .expr e => toString e
  | .comment c => s!"comment(\"{c}\")"
  | .assignment e₁ e₂ => s!"{toString e₁} := {toString e₂}"

instance : ToString Stmt where
  toString s := toStringStmt s

partial def toStringBinding : Binding -> String
  | .varbinding e₁ e₂ => s!"{toString e₁} -> {toString e₂}"
  | .funbinding e₁ e₂ e₃ => s!"{toString e₁} -> {toString e₂} -> {toString e₃}"

instance : ToString Binding where
  toString b := toStringBinding b

partial def toStringAcyclic : Acyclic -> String
  | .expr e => s!"{toString e}"

instance : ToString Acyclic where
  toString a := toStringAcyclic a

partial def toStringAcyclicAs : AcyclicAs -> String
  | .expr e₁ e₂ => s!"acyclic({toString e₁}) as {toString e₂}"

instance : ToString AcyclicAs where
  toString a := toStringAcyclicAs a

partial def toStringInstruction : Instruction -> String
  | .binding b => s!"binding ({toString b})"
  | .expr e => s!"expr ({toString e})"
  | .check s e => s!"check \"{s}\" {toString e}"
  | .acyclic a => s!"acyclic ({toString a})"

instance : ToString Instruction where
  toString i := toStringInstruction i ++ "; "

#check String.intercalate

partial def toStringModel : Model -> String
  | .instructions is =>
    let instrStrings := is.map toString
    "model:" ++ String.intercalate "" instrStrings ++ "}"

instance : ToString Model where
  toString m := toStringModel m

end CatsAST
