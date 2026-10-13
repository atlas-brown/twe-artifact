module

public import Accordion.TWE.Properties
public import Accordion.WE.Walk.ToTWE.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace Walk

variable {Γ : Type} {V : Vars}

theorem evalPath_toTWE (m : TWE.Model Γ (ToTWE.Vars V)) (p : Path Γ V) :
    m.evalPath p.toTWE = Model.evalPath ⟨m.σPath, m.σLoc, m.θ⟩ p := by
  induction p with
  | concat p q ihp ihq =>
      simp [Path.toTWE, TWE.Path.append_eq, TWE.Model.evalPath, Model.evalPath, ihp, ihq]
  | _ => rfl

variable [Ord Γ] [DecidableEq Γ]

theorem sat_toTWE (m : TWE.Model Γ (ToTWE.Vars V)) (φ : Formula Γ V) :
    m ⊨ φ.bind Atom.toTWE ↔ (⟨m.σPath, m.σLoc, m.θ⟩ : Model Γ V) ⊨ φ :=
  Accordion.Formula.sat_bind _ m Atom.toTWE φ fun A _ => by
    cases A with
    | pathEq p q =>
        simp only [Atom.toTWE, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom,
          TWE.Model.satAtom, evalPath_toTWE]
        exact Iff.rfl
    | treeWalk p τ l =>
        simp only [Atom.toTWE, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom,
          TWE.Model.satAtom, TWE.Model.evalTree, evalPath_toTWE]
        change _ ↔ Model.satAtom _ (.treeWalk p τ l)
        simp only [Model.satAtom]
        cases m.θ τ <;> exact Iff.rfl

theorem Formula.bind_toTWE_equisat (φ : Formula Γ V) :
    TWE.Formula.SAT (φ.bind Atom.toTWE) ↔ Formula.SAT φ :=
  ⟨fun ⟨m, hwf, h⟩ => ⟨⟨m.σPath, m.σLoc, m.θ⟩, hwf, (sat_toTWE m φ).1 h⟩,
    fun ⟨m, hwf, h⟩ => ⟨⟨Empty.elim, Empty.elim, m.σPath, m.σLoc, Empty.elim, m.θ⟩, hwf,
      (sat_toTWE _ φ).2 h⟩⟩

end Walk

end WE

end Accordion

end
