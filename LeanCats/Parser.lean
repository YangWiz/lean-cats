import LeanCats.AST

open Lean Elab Meta

namespace Cats

section
declare_syntax_cat binOp
declare_syntax_cat stmt
declare_syntax_cat expr
declare_syntax_cat ident
declare_syntax_cat assignment
declare_syntax_cat const

syntax name : ident
syntax "let" name "=" expr : assignment

syntax ident : expr
syntax num : const
syntax str : const

syntax expr "|" expr : binOp

-- Embed the dsl into Lean
syntax "[assignment|" assignment "]" : term
syntax "[const|" const "]" : term

def mkExpr : Syntax -> Except String Expr
  | _ => throw "Failed to parse expr."

def mkConst : Syntax -> Except String Const
  | `(const| $x:num ) => return Const.num_lit x.getNat
  | `(const| $x:str ) => return Const.str_lit x.getString
  | _ => throw "Failed to parse const"


-- def mkAssignment : Syntax -> Except String Assignment
--   | `(Assignment| let $n:name = $e:Expr ) => return (Stmt.assignment (mkExpr e.) (mkExpr e))
--   | _ => throw "Failed to parse assignement statement."

-- def constTest : term := [const|  ]

end
