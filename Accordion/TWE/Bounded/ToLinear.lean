module

public import Accordion.TWE.Bounded.ToLinear.Properties.Decompositions

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

open ToLinear

variable {Γ : Type} {V : TWE.Vars} [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

namespace Formula

/-- The reduction of bounded TWE to linear TWE (§6.2). -/
def toLinear (k : Nat) (φ : TWE.Formula Γ V) : Guess (TWE.Formula Γ V) := do
  let δ ← boundedDecompositions k φ
  return linearTranslation δ φ

@[grind =_]
theorem toLinear_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [Nonempty Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ toLinear k φ, Linear.Formula.SAT ψ) ↔ SAT k φ :=
  guess_linearTranslation_equisat k φ

end Formula

end Bounded

end TWE

end Accordion

end
