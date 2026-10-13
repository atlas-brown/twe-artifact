module

public import Accordion.TWE.Properties
public import Accordion.WE.Norm.ToTWE.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace Norm

variable {Γ X : Type}

theorem evalPath_toTWE (m : TWE.Model Γ (ToTWE.Vars X)) (p : Path Γ X) :
    m.evalPath p.toTWE = Model.evalPath ⟨m.σPath⟩ p := by
  induction p with
  | concat p q ihp ihq =>
      simp [Path.toTWE, TWE.Path.append_eq, TWE.Model.evalPath, Model.evalPath, ihp, ihq]
  | norm p ih => simp [Path.toTWE, TWE.Model.evalPath, Model.evalPath, ih]
  | _ => rfl

variable [Ord Γ] [DecidableEq Γ]

theorem sat_toTWE (m : TWE.Model Γ (ToTWE.Vars X)) (φ : Formula Γ X) :
    m ⊨ φ.bind Atom.toTWE ↔ (⟨m.σPath⟩ : Model Γ X) ⊨ φ :=
  Accordion.Formula.sat_bind _ m Atom.toTWE φ fun A _ => by
    cases A
    simp only [Atom.toTWE, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom,
      evalPath_toTWE]
    exact Iff.rfl

theorem Formula.bind_toTWE_equisat (φ : Formula Γ X) :
    TWE.Formula.SAT (φ.bind Atom.toTWE) ↔ Formula.SAT φ :=
  ⟨fun ⟨m, _, h⟩ => ⟨⟨m.σPath⟩, (sat_toTWE m φ).1 h⟩,
    fun ⟨m, h⟩ => ⟨⟨Empty.elim, Empty.elim, m.σPath, Empty.elim, Empty.elim, Empty.elim⟩,
      ⟨fun l => Empty.elim l, fun x => Empty.elim x⟩, (sat_toTWE _ φ).2 h⟩⟩

end Norm

end WE

end Accordion

end
