module

public import Accordion.Path
public import Accordion.FileTree.Entries
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Accordion

/-- A file tree: a file, or a directory of named subtrees (Fig. 3). -/
inductive FileTree (Γ : Type) where
  | file
  | dirc (δ : FileTree.Entries Γ (FileTree Γ))
  deriving Repr

namespace FileTree

/-- A file tree is canonical when every entries map under it is. -/
inductive Canonical {Γ : Type} [Ord Γ] : FileTree Γ → Prop
  | file : Canonical .file
  | dirc {δ : Entries Γ (FileTree Γ)} (hδ : δ.Canonical)
      (hsub : ∀ p ∈ δ.map, Canonical p.2) : Canonical (.dirc δ)

/-- A focus: a file tree, or an absent node (Fig. 3). -/
inductive Focus (Γ : Type) where
  | tree (τ : FileTree Γ)
  | abst

def Focus.Canonical {Γ : Type} [Ord Γ] : Focus Γ → Prop
  | .tree τ => τ.Canonical
  | .abst => True

/-- A one-holed file tree context (Fig. 3). -/
inductive Ctx (Γ : Type) where
  | hole
  | node (δ : Entries Γ (FileTree Γ)) (a : Γ) (C : Ctx Γ)

def Ctx.Canonical {Γ : Type} [Ord Γ] : Ctx Γ → Prop
  | .hole => True
  | .node δ _ C => FileTree.Canonical (.dirc δ) ∧ C.Canonical

variable {Γ : Type} [Ord Γ]

def Entries.dom {β : Type} [DecidableEq Γ] (δ : Entries Γ β) : Finset Γ :=
  (δ.map.map Prod.fst).toFinset

namespace Ctx

/-- The file tree obtained by filling the hole of a context with a focus (Fig. 3). -/
def fill : Ctx Γ → Focus Γ → Option (FileTree Γ)
  | .hole, .tree τ => some τ
  | .hole, .abst => none
  | .node δ a C, f =>
      match C.fill f with
      | some τ => some (.dirc (δ.insert a τ))
      | none => some (.dirc δ)

def compose : Ctx Γ → Ctx Γ → Ctx Γ
  | .hole, C' => C'
  | .node δ a C, C' => .node δ a (C.compose C')

/-- The path from the root to the hole of a context (Fig. 4). -/
def path : Ctx Γ → Path Γ
  | .hole => .nil
  | .node _ a C => (a : Path Γ) ++ C.path

end Ctx

end FileTree

end Accordion

end
