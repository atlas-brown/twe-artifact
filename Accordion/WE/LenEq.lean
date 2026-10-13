module

public import Accordion.WE

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

inductive Atom (Γ : Type) (V : Vars) where
  | wordEq (u v : WE.Word Γ V)
  | lenEq (u v : WE.Word Γ V)

abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

abbrev Model (Γ : Type) (V : Vars) := WE.Model Γ V

variable {Γ : Type} {V : Vars}

namespace Atom

def vars : Atom Γ V → List V.Word
  | .wordEq u v => u.vars ++ v.vars
  | .lenEq u v => u.vars ++ v.vars

end Atom

namespace Model

def satAtom (m : Model Γ V) : Atom Γ V → Prop
  | .wordEq u v => m.evalWord u = m.evalWord v
  | .lenEq u v => GroundWord.length (m.evalWord u) = GroundWord.length (m.evalWord v)

instance : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

end Model

namespace Formula

def vars (φ : Formula Γ V) : List V.Word :=
  φ.atoms.flatMap Atom.vars

def SAT (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m ⊨ φ

end Formula

end LenEq

end WE

end Accordion

end
