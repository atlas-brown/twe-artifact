module

public import Accordion.TWE.Bounded.ToLinear
public import Accordion.TWE.Linear.ToWE

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

variable {Γ : Type} {V : TWE.Vars} [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

namespace Formula

/-- The reduction of bounded TWE to WE (§6.2). -/
@[grind]
def toWE (k : Nat) (φ : TWE.Formula Γ V) : Guess (WE.Formula Γ (Linear.ToWE.Vars V)) := do
  let ψ ← toLinear k φ
  Linear.Formula.toWE ψ

@[grind =_]
theorem toWE_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [Infinite Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ toWE k φ, WE.Formula.SAT ψ) ↔ SAT k φ := by
  grind only [toWE, =_ toLinear_equisat, =_ Linear.Formula.toWE_equisat,
    Guess.mem_bind]

end Formula

end Bounded

end TWE

end Accordion

end
