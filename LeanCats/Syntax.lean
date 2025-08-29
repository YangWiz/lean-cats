namespace Cat

declare_syntax_cat keyword
declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model

syntax "co" : keyword
syntax "rf" : keyword
syntax "fr" : keyword
syntax "po" : keyword
syntax "W" : keyword
syntax "R" : keyword
syntax "M" : keyword
syntax "emptyset" : keyword

syntax keyword : dsl_term
syntax num : dsl_term
syntax ident : dsl_term
syntax "(" expr ")" : dsl_term

syntax dsl_term : expr

syntax:50 expr:50 "|" expr:51 : expr
syntax expr "&" expr : expr
syntax expr ";" expr : expr
syntax:60 expr:60 "*" expr:61 : expr
syntax expr "^" expr : expr
syntax expr "+" expr : expr
syntax expr "-" expr : expr

syntax "let" ident "=" expr : inst
syntax "acyclic" expr : inst
syntax "irreflexive" expr : inst
syntax "empty" expr : inst
syntax "(*" ident* "*)" : inst
syntax "include" str : inst

syntax inst* : model

end Cat
