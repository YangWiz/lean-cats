inductive Vec (α : Type μ) : Nat -> Type μ
| nil : Vec α 0
| cons : α -> Vec α n -> Vec α (n+1)

infix:67 " :: " => Vec.cons

inductive Ty where
| int
| bool
| fn (a r : Ty)

@[reducible] def Ty.interp : Ty -> Type
| int => Int
| bool => Bool
| fn a r => a.interp -> r.interp
