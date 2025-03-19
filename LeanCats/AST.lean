-- AST
inductive Instruction

inductive Const
  | num_lit : Nat -> Const
  | str_lit : String -> Const

inductive Expr
  | id : Nat -> Expr

inductive Stmt
  | expr : Expr -> Stmt
  | comment : String -> Stmt
  | assignment : Expr -> Expr -> Stmt

inductive Binding
  -- valbinding ::=	id -> expr
  | varbinding : Expr -> Expr -> Binding
  -- funbinding := id -> pad -> expr
  | funbinding : Expr -> Expr -> Expr -> Binding
