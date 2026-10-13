module

public import Accordion.WhileFS.Symbolic.Completeness

@[expose] public section

namespace Accordion.WhileFS.Symbolic

variable {Γ X : Type} {V : TWE.Vars} [Ord Γ] [DecidableEq Γ] [DecidableEq X]
  [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
  {c c' : Command Γ X} {ς ς' : State Γ X} {sς sς' : SState Γ X V}
  {m : TWE.Model Γ V}

/-- Soundness of the symbolic semantics (§4.2, Theorem 1). -/
theorem soundness :
    ((c, sς) ⇝* (c', sς')) → m.WF → (m ⊫ sς) → (m ⊨ sς'.π) →
      ⟦sς⟧  m = some ς  →
      ⟦sς'⟧ m = some ς' →
      ((c, ς) ⟶* (c', ς')) :=
  smultistep_sound

/-- Completeness of the symbolic semantics (§4.2, Theorem 1). -/
theorem completeness [TWE.Vars.Comparable V] [TWE.Vars.Unbounded V] :
    m.WF → (m ⊫ sς) → ⟦sς⟧ m = some ς → ((c, ς) ⟶* (c', ς')) →
      ∃ sς', ((c, sς) ⇝* (c', sς')) ∧
        ∃ m' : TWE.Model Γ V, m'.WF ∧ (m' ⊫ sς') ∧
          ⟦sς⟧  m' = some ς  ∧
          ⟦sς'⟧ m' = some ς' :=
  smultistep_complete

end Accordion.WhileFS.Symbolic

end
