module

public import Accordion.WE.Decidability.Properties.Steps

@[expose] public section

namespace Accordion.WE

variable {Γ : Type} {V : Vars} [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Letter]
  [DecidableEq V.Word] [Fresh V.Word]

/-- A decision procedure for WE (cited in §6.1). -/
def Formula.sat? (φ : Formula Γ V) : Bool :=
  (Decidability.wordEquations φ).any Decidability.eqnSat?

/-- The decision procedure for WE is correct (cited in §6.1). -/
theorem Formula.sat?_iff (φ : Formula Γ V) : φ.sat? = true ↔ φ.SAT := by
  rw [Formula.sat?, Guess.any_eq_true, ← Decidability.wordEquations_equisat]
  simp only [Decidability.eqnSat?_iff]

/-- WE is decidable (cited in §6.1). -/
instance : DecidablePred (Formula.SAT (Γ := Γ) (V := V)) :=
  fun φ ↦ decidable_of_iff _ φ.sat?_iff

end Accordion.WE

end
