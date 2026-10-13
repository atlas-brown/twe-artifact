module

public import Accordion.Formula.Properties
public import Accordion.TWE

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : Vars}

-- Lets `simp` see through the `++`/`∅` wrappers.
@[simp] theorem Path.append_eq (p q : Path Γ V) : p ++ q = .join p q := rfl
@[simp] theorem Set.empty_eq : (∅ : Set Γ V) = .empty := rfl

namespace Model

section
variable (m : Model Γ V)

@[simp] theorem σName_setName [DecidableEq V.Name] (x y : V.Name) (a : Γ) :
    (m[x ↦ a]).σName y = if y = x then a else m.σName y := rfl
@[simp] theorem σComp_setComp [DecidableEq V.Comp] (x y : V.Comp) (c : Accordion.Component Γ) :
    (m[x ↦ c]).σComp y = if y = x then c else m.σComp y := rfl
@[simp] theorem σPath_setPath [DecidableEq V.Path] (x y : V.Path) (p : Accordion.Path Γ) :
    (m[x ↦ p]).σPath y = if y = x then p else m.σPath y := rfl
@[simp] theorem σLoc_setLoc [DecidableEq V.Loc] (x y : V.Loc) (p : Accordion.Path Γ) :
    (m[x ↦ p]).σLoc y = if y = x then p else m.σLoc y := rfl
@[simp] theorem σSet_setSet [DecidableEq V.Set] (x y : V.Set) (s : Finset Γ) :
    (m[x ↦ s]).σSet y = if y = x then s else m.σSet y := rfl

@[simp] theorem setName_frame [DecidableEq V.Name] (x : V.Name) (a : Γ) :
    (m[x ↦ a]).σComp = m.σComp ∧ (m[x ↦ a]).σPath = m.σPath ∧ (m[x ↦ a]).σLoc = m.σLoc ∧
      (m[x ↦ a]).σSet = m.σSet ∧ (m[x ↦ a]).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setComp_frame [DecidableEq V.Comp] (x : V.Comp) (c : Accordion.Component Γ) :
    (m[x ↦ c]).σName = m.σName ∧ (m[x ↦ c]).σPath = m.σPath ∧ (m[x ↦ c]).σLoc = m.σLoc ∧
      (m[x ↦ c]).σSet = m.σSet ∧ (m[x ↦ c]).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setPath_frame [DecidableEq V.Path] (x : V.Path) (p : Accordion.Path Γ) :
    (m[x ↦ p]).σName = m.σName ∧ (m[x ↦ p]).σComp = m.σComp ∧ (m[x ↦ p]).σLoc = m.σLoc ∧
      (m[x ↦ p]).σSet = m.σSet ∧ (m[x ↦ p]).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setLoc_frame [DecidableEq V.Loc] (x : V.Loc) (p : Accordion.Path Γ) :
    (m[x ↦ p]).σName = m.σName ∧ (m[x ↦ p]).σComp = m.σComp ∧ (m[x ↦ p]).σPath = m.σPath ∧
      (m[x ↦ p]).σSet = m.σSet ∧ (m[x ↦ p]).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setSet_frame [DecidableEq V.Set] (x : V.Set) (s : Finset Γ) :
    (m[x ↦ s]).σName = m.σName ∧ (m[x ↦ s]).σComp = m.σComp ∧ (m[x ↦ s]).σPath = m.σPath ∧
      (m[x ↦ s]).σLoc = m.σLoc ∧ (m[x ↦ s]).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩

end

variable [Ord Γ] [DecidableEq Γ]

@[simp] theorem sat_iff_satAtom (m : Model Γ V) (a : Atom Γ V) :
    Sat.sat m a ↔ m.satAtom a := Iff.rfl

instance (m : Model Γ V) (a : Atom Γ V) : Decidable (Sat.sat m a) := by
  change Decidable (m.satAtom a)
  cases a <;> unfold Model.satAtom <;> (repeat' split) <;> infer_instance

end Model

end TWE

end Accordion

end
