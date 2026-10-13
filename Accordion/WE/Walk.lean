module

public import Accordion.FileTree.Zipper
public import Accordion.WE

@[expose] public section

namespace Accordion

namespace WE

namespace Walk

structure Vars where
  Path : Type
  Loc : Type
  Tree : Type

inductive Path (Γ : Type) (V : Vars) where
  | nil
  | letter (a : Γ)
  | var (x : V.Path)
  | loc (l : V.Loc)
  | concat (p q : Path Γ V)

instance {Γ : Type} {V : Vars} : Append (Path Γ V) := ⟨Path.concat⟩

scoped notation "ε" => Path.nil

inductive Atom (Γ : Type) (V : Vars) where
  | pathEq (p q : Path Γ V)
  | treeWalk (p : Path Γ V) (τ : V.Tree) (l : V.Loc)

/-- A formula of word equations with tree walks (§5.1). -/
abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

scoped notation:60 p:61 " ≐ " q:61 => Accordion.Formula.atom (Atom.pathEq p q)
scoped notation:60 τ:61 " ⊢ " p " ⇝ " l:61 => Accordion.Formula.atom (Atom.treeWalk p τ l)

structure Model (Γ : Type) (V : Vars) where
  σPath : WE.Subst V.Path (Accordion.Path Γ)
  σLoc : WE.Subst V.Loc (Accordion.Path Γ)
  θ : WE.Subst V.Tree (FileTree.Focus Γ)

variable {Γ : Type} {V : Vars}

namespace Model

def evalPath (m : Model Γ V) : Path Γ V → Accordion.Path Γ
  | .nil => ε
  | .letter a => (a : Accordion.Path Γ)
  | .var x => m.σPath x
  | .loc l => m.σLoc l
  | .concat p q => m.evalPath p ++ m.evalPath q

variable [Ord Γ]

def WF (m : Model Γ V) : Prop :=
  (∀ l, (m.σLoc l).Linear) ∧ (∀ x, (m.θ x).Canonical)

def satAtom (m : Model Γ V) : Atom Γ V → Prop
  | .pathEq p q => m.evalPath p = m.evalPath q
  | .treeWalk p τ l =>
      match m.θ τ with
      | .tree τ' =>
          match FileTree.resolve (m.evalPath p) τ' with
          | some (C, _) => C.path = m.σLoc l
          | none => False
      | .abst => False

instance : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

end Model

namespace Formula

def SAT [Ord Γ] (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m.WF ∧ m ⊨ φ

end Formula

end Walk

end WE

end Accordion

end
