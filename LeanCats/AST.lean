-- AST
namespace CatsAST
inductive Instruction

abbrev Ident := String

inductive QualifiedName
  | name: String -> QualifiedName

inductive Const
  | num_lit : Nat -> Const
  | str_lit : QualifiedName -> Const
deriving Inhabited

mutual

inductive Term
  | name : QualifiedName -> Term
  | negation : Term -> Term
  -- Expr itself is also a Term.
  | expr: Expr -> Term

inductive Expr
  | id : Nat -> Expr
  | bin_or : Term -> Term -> Expr

inductive Stmt
  | expr : Expr -> Stmt
  | comment : String -> Stmt
  | assignment : Expr -> Expr -> Stmt

inductive Binding
  -- valbinding ::=	id -> expr
  | varbinding : QualifiedName -> Expr -> Binding
  -- funbinding := id -> pad -> expr
  | funbinding : Expr -> Expr -> Expr -> Binding

inductive Statement
  | expr : Expr -> Statement

end
end CatsAST
