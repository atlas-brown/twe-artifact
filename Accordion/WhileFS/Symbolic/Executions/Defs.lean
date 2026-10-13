module

public import Accordion.WhileFS.Symbolic

@[expose] public section

namespace Accordion

open scoped Accordion.Formula

/-- The model in which every tree variable denotes `τ` and a location is given by its names. -/
def TWE.Model.ofTree {Γ : Type} {V : TWE.Vars} [Inhabited Γ] (τ : FileTree Γ)
    (loc : V.Loc → List Γ) : TWE.Model Γ V where
  σName _ := default
  σComp _ := .empty
  σPath _ := .nil
  σLoc l := Path.descend (loc l)
  σSet _ := ∅
  θ _ := .tree τ

/-- The symbolic state of a program started in the tree `T`, with nothing assumed. -/
def SState.init {Γ X : Type} {V : TWE.Vars} [DecidableEq X] (T : TWE.Tree V) : SState Γ X V :=
  ⟨∅, T, ⊤⟩

end Accordion

end
