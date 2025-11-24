import LeanCats.Macro

-- include "cos.cat"
[model| sc
  let com = rf | co | fr
  let poo = po & (W*W | R*M)

  let ghb = po | com
  acyclic ghb as new
]

[model| tso
  let com_tso = rf | co | fr
  let po_tso = po & (W*W | R*M)
  let ghb = po_tso | com_tso
  acyclic ghb as new
]

#check sc.new
#check tso.new
