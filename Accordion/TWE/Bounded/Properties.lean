module

public import Accordion.TWE.Bounded
public import Accordion.Path.Properties

@[expose] public section

namespace Accordion

variable {Γ : Type}

namespace Path

theorem nonlinearCount_join (p q : Path Γ) :
    nonlinearCount (p ++ q) = nonlinearCount p + nonlinearCount q := by
  induction q with
  | nil => rfl
  | app q c ih =>
      simp only [append_eq] at ih ⊢
      cases c <;> simp [join, nonlinearCount, ih] <;> omega

theorem linear_iff_nonlinearCount_eq_zero (p : Path Γ) : p.Linear ↔ nonlinearCount p = 0 := by
  induction p with
  | nil => simp [Linear, nonlinearCount]
  | app p c ih => cases c <;> simp [Linear, nonlinearCount, ih]

theorem nonlinearCount_descend (w : List Γ) : (descend w).nonlinearCount = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [descend, nonlinearCount_join, ih]
      rfl

end Path

end Accordion

end
