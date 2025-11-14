namespace CatGrammar

declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model
declare_syntax_cat assertion
declare_syntax_cat reserved
declare_syntax_cat keyword
declare_syntax_cat primitive
declare_syntax_cat name
declare_syntax_cat statement
declare_syntax_cat definition
declare_syntax_cat constraint
declare_syntax_cat annotable_events
declare_syntax_cat predefined_events
declare_syntax_cat predefined_relations

scoped syntax reserved : expr
scoped syntax primitive : reserved
scoped syntax keyword : reserved
scoped syntax name : reserved
scoped syntax predefined_events : reserved
scoped syntax predefined_relations : reserved

scoped syntax "and" : keyword
scoped syntax "as" : keyword
scoped syntax "begin" : keyword
scoped syntax "call" : keyword
scoped syntax "do" : keyword
scoped syntax "end" : keyword
scoped syntax "enum" : keyword
scoped syntax "flag" : keyword
scoped syntax "forall" : keyword
scoped syntax "from" : keyword
scoped syntax "fun" : keyword
scoped syntax "in" : keyword
scoped syntax "instructions" : keyword
scoped syntax "let" : keyword
scoped syntax "match" : keyword
scoped syntax "procedure" : keyword
scoped syntax "rec" : keyword
scoped syntax "scopes" : keyword
scoped syntax "with" : keyword

scoped syntax "classes" : primitive
scoped syntax "linearizations" : primitive
scoped syntax "tag2events" : primitive
scoped syntax "tag2scopes" : primitive

scoped syntax assertion : keyword
scoped syntax "irreflexive" : assertion
scoped syntax "empty" : assertion
scoped syntax "acyclic" : assertion

scoped syntax "_" : name
scoped syntax "O" : name
scoped syntax "ext" : name
scoped syntax "FW" : name
scoped syntax "id" : name
scoped syntax "loc" : name
scoped syntax "narrower" : name
scoped syntax "wider" : name

-- annotable events.
scoped syntax "W" : annotable_events -- write events
scoped syntax "R" : annotable_events -- read events
scoped syntax "B" : annotable_events -- branch events
scoped syntax "F" : annotable_events -- fence events

scoped syntax "___" : predefined_events -- all events
scoped syntax "IW" : predefined_events -- initial writes
scoped syntax "M" : predefined_events -- memory events, M = W ∪ R
scoped syntax annotable_events : predefined_events

/-- predefined_relations: -/
scoped syntax "O" : predefined_relations -- empty relation
scoped syntax "rf" : predefined_relations -- read from
scoped syntax "fr" : predefined_relations -- from read
scoped syntax "id" : predefined_relations -- identity
scoped syntax "loc" : predefined_relations -- same location
scoped syntax "ext" : predefined_relations -- external (different pids)
scoped syntax "po" : predefined_relations -- program order
scoped syntax "rmw" : predefined_relations -- read-modify-write

scoped syntax keyword : dsl_term
scoped syntax num : dsl_term
scoped syntax ident : dsl_term
scoped syntax "(" expr ")" : dsl_term

scoped syntax dsl_term : expr

scoped syntax:50 expr:50 "|" expr:51 : expr
scoped syntax expr "&" expr : expr
scoped syntax expr ";" expr : expr
scoped syntax:60 expr:60 "*" expr:61 : expr
scoped syntax expr "^" expr : expr
scoped syntax expr "+" expr : expr
scoped syntax expr "-" expr : expr
scoped syntax:71 expr "^-1" : expr

scoped syntax assertion expr ("as" ident)? : inst
scoped syntax "let" ident "=" expr : inst

scoped syntax "(*" ident* "*)" : inst
scoped syntax "include" str : inst

end CatGrammar
