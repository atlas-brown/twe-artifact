module

public import Accordion.TWE
public import Accordion.WE

@[expose] public section

namespace Accordion

namespace WE

namespace ShapeReg

structure Vars where
  Path : Type
  Tree : Type

inductive Path (Γ : Type) (V : Vars) where
  | nil
  | letter (a : Γ)
  | var (x : V.Path)
  | concat (p q : Path Γ V)

instance {Γ : Type} {V : Vars} : Append (Path Γ V) := ⟨Path.concat⟩

scoped notation "ε" => Path.nil

inductive Regex (Γ : Type) where
  | empty
  | nil
  | name (a : Γ)
  | nameNotIn (s : Finset Γ)
  | parent
  | union (r s : Regex Γ)
  | concat (r s : Regex Γ)
  | star (r : Regex Γ)

namespace Regex

def Matches {Γ : Type} : Regex Γ → List (Component Γ) → Prop
  | .empty, _ => False
  | .nil, w => w = []
  | .name a, w => w = [.name a]
  | .nameNotIn s, w => ∃ a, a ∉ s ∧ w = [.name a]
  | .parent, w => w = [‥]
  | .union r s, w => r.Matches w ∨ s.Matches w
  | .concat r s, w => ∃ u v, w = u ++ v ∧ r.Matches u ∧ s.Matches v
  | .star r, w => ∃ ws : List (List (Component Γ)), w = ws.flatten ∧ ∀ u ∈ ws, r.Matches u

end Regex

inductive Atom (Γ : Type) (V : Vars) where
  | pathEq (p q : Path Γ V)
  | treeWalkShape (p : Path Γ V) (τ : V.Tree) (h : TWE.Shape)
  | pathMem (p : Path Γ V) (r : Regex Γ)

/-- A formula of word equations with shapes and regular constraints (§5.2). -/
abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

scoped notation:60 p:61 " ≐ " q:61 => Accordion.Formula.atom (Atom.pathEq p q)
scoped notation:60 τ:61 " ⊢ " p " ⇝ " h:61 => Accordion.Formula.atom (Atom.treeWalkShape p τ h)
scoped notation:60 p:61 " ∈̇ " r:61 => Accordion.Formula.atom (Atom.pathMem p r)

structure Model (Γ : Type) (V : Vars) where
  σPath : WE.Subst V.Path (Accordion.Path Γ)
  θ : WE.Subst V.Tree (FileTree.Focus Γ)

variable {Γ : Type} {V : Vars}

namespace Model

def evalPath (m : Model Γ V) : Path Γ V → Accordion.Path Γ
  | .nil => ε
  | .letter a => (a : Accordion.Path Γ)
  | .var x => m.σPath x
  | .concat p q => m.evalPath p ++ m.evalPath q

variable [Ord Γ]

def WF (m : Model Γ V) : Prop :=
  ∀ x, (m.θ x).Canonical

def satAtom (m : Model Γ V) : Atom Γ V → Prop
  | .pathEq p q => m.evalPath p = m.evalPath q
  | .treeWalkShape p τ h =>
      match m.θ τ with
      | .tree τ' =>
          match FileTree.resolve (m.evalPath p) τ' with
          | some (_, f) => f.shape = h
          | none => False
      | .abst => False
  | .pathMem p r => r.Matches (m.evalPath p).components

instance : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

end Model

namespace Formula

def SAT [Ord Γ] (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m.WF ∧ m ⊨ φ

end Formula

end ShapeReg

end WE

end Accordion

end
