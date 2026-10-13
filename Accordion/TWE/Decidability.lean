module

public import Accordion.TWE.Linear.ToWE
public import Accordion.TWE.Bounded.ToLinear
public import Accordion.TWE.Bounded.ToWE
public import Accordion.WE.Decidability

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : Vars} [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
  [Vars.Comparable V] [Vars.Fresh V]

namespace Linear

/-- Linear TWE reduces to WE (§6.1, Theorem 4). -/
theorem toWE_equisat [Infinite Γ] (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toWE φ, WE.Formula.SAT ψ) ↔ Formula.SAT φ :=
  Formula.toWE_equisat φ

/-- A decision procedure for linear TWE (§6.1). -/
def Formula.sat? [Fresh Γ] (φ : TWE.Formula Γ V) : Bool :=
  (Formula.toWE φ).any WE.Formula.sat?

/-- The decision procedure for linear TWE is correct (§6.1, Corollary 1). -/
theorem sat?_iff [Fresh Γ] (φ : TWE.Formula Γ V) : Formula.sat? φ = true ↔ Formula.SAT φ := by
  rw [← toWE_equisat, Formula.sat?, Guess.any_eq_true]
  simp only [WE.Formula.sat?_iff]

/-- Linear TWE is decidable (§6.1, Corollary 1). -/
instance [Fresh Γ] : DecidablePred (Formula.SAT (Γ := Γ) (V := V)) :=
  fun φ ↦ decidable_of_iff _ (sat?_iff φ)

end Linear

namespace Bounded

/-- Bounded TWE reduces to linear TWE (§6.2, Theorem 5). -/
theorem toLinear_equisat [Nonempty Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toLinear k φ, Linear.Formula.SAT ψ) ↔ Formula.SAT k φ :=
  Formula.toLinear_equisat k φ

/-- Bounded TWE reduces to WE (§6.2, Theorem 5). -/
theorem toWE_equisat [Infinite Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toWE k φ, WE.Formula.SAT ψ) ↔ Formula.SAT k φ :=
  Formula.toWE_equisat k φ

/-- A decision procedure for bounded TWE (§6.2). -/
def Formula.sat? [Fresh Γ] (k : Nat) (φ : TWE.Formula Γ V) : Bool :=
  (Formula.toWE k φ).any WE.Formula.sat?

/-- The decision procedure for bounded TWE is correct (§6.2, Corollary 2). -/
theorem sat?_iff [Fresh Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    Formula.sat? k φ = true ↔ Formula.SAT k φ := by
  rw [← toWE_equisat, Formula.sat?, Guess.any_eq_true]
  simp only [WE.Formula.sat?_iff]

/-- Bounded TWE is decidable (§6.2, Corollary 2). -/
instance [Fresh Γ] (k : Nat) : DecidablePred (Formula.SAT (Γ := Γ) (V := V) k) :=
  fun φ ↦ decidable_of_iff _ (sat?_iff k φ)

end Bounded

end TWE

end Accordion

end
