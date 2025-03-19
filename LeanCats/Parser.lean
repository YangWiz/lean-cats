import LeanCats.AST

open CatsAST
open Lean Elab Meta

namespace Cats

section
declare_syntax_cat binOp
declare_syntax_cat statement
declare_syntax_cat expr
declare_syntax_cat ident
declare_syntax_cat binding
declare_syntax_cat const
declare_syntax_cat acyclic
declare_syntax_cat qualified_name
declare_syntax_cat dsl_term

syntax binding : statement
syntax expr : statement

syntax ident : qualified_name -- qualifed_name is just a identifier.

syntax "let" qualified_name "=" expr : binding
syntax qualified_name : dsl_term

syntax expr : dsl_term
syntax "(" dsl_term ")" : expr

syntax num : const
syntax str : const

syntax dsl_term "|" dsl_term: binOp

-- Embed the dsl into Lean
syntax "[assignment|" binding "]" : term
syntax "[const|" const "]" : term
syntax "[qualified_name|" qualified_name "]" : term
syntax "[bin_or|" dsl_term "|" dsl_term : term

def mkName : Syntax -> Except String QualifiedName
  | `(qualified_name | $x:ident) => return QualifiedName.name x.getId.toString
  | _ => throw "Failed to parse QualifedName"

def mkExpr : Syntax -> Except String Expr
  | _ => throw "Failed to parse expr."

def mkTerm : Syntax -> Except String CatsAST.Term
  | `(dsl_term | $e:expr ) => CatsAST.Term.expr <$> (mkExpr e)
  | `(dsl_term | $n:qualified_name ) => CatsAST.Term.name <$> (mkName n)
  | _ => throw "Failed to parse Term"

def mkBinding : Syntax -> Except String Binding
  | `(binding| let $n:qualified_name = $e:expr ) => Binding.varbinding <$> (mkName n) <*> (mkExpr e)
  -- TODO(Zhiyang) will implement pat binding (function binding) later.
  | _ => throw "Failed to parse assignment."

def mkStatement : Syntax -> Except String Statement
  | _ => throw "Failed to parse statement"

def mkConst : Syntax -> Except String Const
  | `(const| $x:num ) => return Const.num_lit x.getNat
  | `(const| $x:str ) => Const.str_lit <$> (mkName x)
  | _ => throw "Failed to parse const"

-- def mkAssignment : Syntax -> Except String Assignment
--   | `(Assignment| let $n:name = $e:Expr ) => return (Stmt.assignment (mkExpr e.) (mkExpr e))
--   | _ => throw "Failed to parse assignement statement."

-- elab v:num : const => mkConst v

end
