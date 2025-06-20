import LeanCats.HerdingCats

@[simp] def e₁ := Event.mk "1" 1 (Thread.mk 1) 1 (Action.mk write "x" (some 1) true false)
@[simp] def e₂ := Event.mk "2" 1 (Thread.mk 1) 2 (Action.mk read "x" (some 1) false false)
@[simp] def e₃ := Event.mk "3" 2 (Thread.mk 2) 1 (Action.mk write "y" (some 1) false false)
@[simp] def e₄ := Event.mk "4" 2 (Thread.mk 2) 2 (Action.mk read "y" (some 1) false false)
@[simp] def e₅ := Event.mk "5" 2 (Thread.mk 2) 3 (Action.mk write "x" (some 1) false false)

#eval e₁ = e₁

def input := [e₁, e₂, e₃, e₄, e₅]

#eval Primitives.allCo input
#eval Primitives.candadites input
#eval Primitives.candadites input |>.filter (λ p ↦ Primitives.loc.rel p.1 p.2)
#eval input.filter (λ p ↦ Primitives.IW.rel p)
#eval input.filter (λ p ↦ Primitives.FW.rel p)
def W := input.filter (λ p ↦ Primitives.W.rel p)

#eval Primitives.Wx input
def perm := (Primitives.Wx input).head!.permutations
#eval perm
#eval Primitives.allCox input |>.length
#eval (Primitives.allCox input).head!.length

#eval (Primitives.allCo input)

#eval Primitives.validate input
#eval (Primitives.rf.Es input)[0]
#eval Primitives.rf_well_formed (Primitives.rf.Es input)[0] Primitives.rf
