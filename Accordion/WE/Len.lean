module

public import Accordion.WE

@[expose] public section

namespace Accordion

namespace WE

namespace Len

open scoped Accordion.Formula

structure LenTerm (X : Type) where
  c : Int
  x : X
  deriving Repr

structure LenConstraint (X : Type) where
  c₀ : Int
  terms : List (LenTerm X)
  deriving Repr

inductive Atom (Γ : Type) (V : Vars) where
  | wordEq (u v : WE.Word Γ V)
  | wordLength (c : LenConstraint V.Word)

/-- A formula of word equations with length constraints (§5). -/
abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

scoped notation:60 u:61 " ≐ " v:61 => Accordion.Formula.atom (Atom.wordEq u v)

abbrev Model (Γ : Type) (V : Vars) := WE.Model Γ V

variable {Γ : Type} {V : Vars}

namespace Atom

def letterVars : Atom Γ V → List V.Letter
  | .wordEq u v => u.letterVars ++ v.letterVars
  | .wordLength _ => []

end Atom

namespace Model

def evalConstraint (m : Model Γ V) (c : LenConstraint V.Word) : Int :=
  c.c₀ + (c.terms.map fun t => t.c * (GroundWord.length (m.σWord t.x) : Int)).sum

def satAtom (m : Model Γ V) : Atom Γ V → Prop
  | .wordEq u v => m.evalWord u = m.evalWord v
  | .wordLength c => m.evalConstraint c = 0

instance : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

end Model

namespace Formula

def letterVars (φ : Formula Γ V) : List V.Letter :=
  φ.atoms.flatMap Atom.letterVars

def SAT (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m ⊨ φ

end Formula

end Len

end WE

end Accordion

end
