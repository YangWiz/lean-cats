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

  -- | `(ident|emptyset) => return .const ``Primitives.Events.empty []
  -- | `(ident|W) => return .const ``Primitives.Events.write []
  -- | `(ident|R) => return .const ``Primitives.Events.read []
  -- | `(ident|M) => return .const ``Primitives.Events.memory []
  -- | `(ident|IW) => return .const ``Primitives.Events.initial_writes []
  -- | `(ident|FW) => return .const ``Primitives.Events.final_writes []
  -- | `(ident|B) => return .const ``Primitives.Events.branch []
  -- | `(ident|RMW) => return .const ``Primitives.Events.read_modify_write []
  -- | `(ident|F) => return .const ``Primitives.Events.fence []
  -- | `(ident|po) => return .const ``Primitives.Relation.po []
  -- | `(ident|addr) => mkConst ``AddressDependency
  -- | `(ident|data) => mkConst ``DataDependency
  -- | `(ident|ctrl) => mkConst ``ControlDependency
  -- | `(ident|rmw) => mkConst ``ReadModifyWritePair
  -- | `(ident|amo) => mkConst ``AtomicModify

inductive Const
  | num_lit : Nat -> Const
  | str_lit : Expr -> Const
deriving Inhabited

mutual

inductive BinOp
  | union : Term -> Expr -> BinOp
  | inter : Term -> Expr -> BinOp
  | diff : Term -> Expr -> BinOp

inductive Term
  | name : Expr -> Term
  | negation : Term -> Term
  -- Expr itself is also a Term.
  | keyword : String -> Term
  | expr: Expr -> Term
  | liter: String -> Term

inductive Expr
  | id : Nat -> Expr
  | term : Term -> Expr
  | binop : BinOp -> Expr

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

end
end CatsAST
