module

public import Accordion.Path.Measures
public import Accordion.WE

@[expose] public section

namespace Accordion

namespace WE

namespace Norm

inductive Path (Γ : Type) (X : Type) where
  | nil
  | letter (a : Γ)
  | var (x : X)
  | concat (p q : Path Γ X)
  | norm (p : Path Γ X)
  deriving Repr

instance {Γ X : Type} : Append (Path Γ X) := ⟨Path.concat⟩

scoped notation "ε" => Path.nil

inductive Atom (Γ : Type) (X : Type) where
  | pathEq (p q : Path Γ X)
  deriving Repr

/-- A formula of word equations with path normalisation (§5.1). -/
abbrev Formula (Γ : Type) (X : Type) := Accordion.Formula (Atom Γ X)

scoped notation:60 p:61 " ≐ " q:61 => Accordion.Formula.atom (Atom.pathEq p q)

namespace Formula

open scoped Accordion.Formula in
def pathBalanced [Inhabited Γ] (p : Path Γ X) : Formula Γ X :=
  (.norm p ≐ ε) ⋏ ∼(.norm (.letter default ++ p) ≐ ε)

end Formula

structure Model (Γ : Type) (X : Type) where
  σPath : WE.Subst X (Accordion.Path Γ)

variable {Γ X : Type}

namespace Model

def evalPath (m : Model Γ X) : Path Γ X → Accordion.Path Γ
  | .nil => ε
  | .letter a => (a : Accordion.Path Γ)
  | .var x => m.σPath x
  | .concat p q => m.evalPath p ++ m.evalPath q
  | .norm p => (m.evalPath p).norm

def satAtom (m : Model Γ X) : Atom Γ X → Prop
  | .pathEq p q => m.evalPath p = m.evalPath q

instance : Sat (Model Γ X) (Atom Γ X) where
  sat := satAtom

theorem sat_pathBalanced [Inhabited Γ] (m : Model Γ X) (p : Path Γ X) :
    m ⊨ Formula.pathBalanced p ↔ (m.evalPath p).IsBalanced :=
  (Accordion.Path.isBalanced_iff_norm_eq_nil default (m.evalPath p)).symm

end Model

namespace Formula

def SAT (φ : Formula Γ X) : Prop :=
  ∃ m : Model Γ X, m ⊨ φ

end Formula

end Norm

end WE

end Accordion

end
