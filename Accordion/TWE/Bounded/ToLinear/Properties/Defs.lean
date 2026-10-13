module

public import Accordion.TWE.Bounded.ToLinear.Rewrites
public import Accordion.TWE.Linear.ToWE.Properties.Defs

@[expose] public section

namespace Accordion

def Component.kind {Γ : Type} : Component Γ → TWE.Bounded.ToLinear.ComponentKind
  | .name _ => .name
  | .empty => .empty
  | .self => .self
  | .parent => .parent

namespace TWE

namespace Bounded

namespace ToLinear

open Linear.ToWE (WordModel)
open scoped Accordion.Formula Linear.ToWE.WordModel

variable {Γ : Type} {V : TWE.Vars}

def Step.toComponent : Step → Accordion.Component Γ
  | .empty => .empty
  | .self => .self
  | .parent => .parent

def Step.apply : Step → List Γ → List Γ
  | .parent, w => w.dropLast
  | _, w => w

/-- The path `B₁ C₁ B₂ ⋯ Cₘ Bₘ₊₁`, for the word `B₁` and the pairs `(Cᵢ, Bᵢ₊₁)`. -/
def blocksPath (w : List Γ) : List (Step × List Γ) → Accordion.Path Γ
  | [] => Path.descend w
  | (C, w') :: r => Path.descend w ++ .init C.toComponent ++ blocksPath w' r

def Decomposition.restWords [Ord Γ] (M : WordModel Γ V) (d : Decomposition Γ V) :
    List (Step × List Γ) :=
  d.rest.map fun p ↦ (p.1, M.evalPath p.2)

def Decomposition.eval [Ord Γ] (M : WordModel Γ V) (d : Decomposition Γ V) : Accordion.Path Γ :=
  blocksPath (M.evalPath d.first) (d.restWords M)

def Decomposition.HasLinearConstants (d : Decomposition Γ V) : Prop :=
  d.first.hasLinearConstants ∧ ∀ p ∈ d.rest, p.2.hasLinearConstants

/-- The source model of `M` under `δ`: a path variable `X` denotes `X₀ C₁ X₁ ⋯ Cₘ Xₘ` for the
blocks that `δ` gives it. -/
def sourceModel [Ord Γ] [TWE.Vars.Comparable V] (δ : VariableDecomposition V)
    (M : WordModel Γ V) : TWE.Model Γ V where
  σName := M.σName
  σComp x := match δ.component x with
    | .name => .name (M.σComp x)
    | .empty => .empty
    | .self => .self
    | .parent => .parent
  σPath X := blocksPath (M.σPath (δ.path X).1) ((δ.path X).2.map fun p ↦ (p.1, M.σPath p.2))
  σLoc ℓ := (M.σLoc ℓ : Accordion.Path Γ)
  σSet := M.σSet
  θ T := (M.θ T).1

def splitComponents : List (Accordion.Component Γ) → List Γ × List (Step × List Γ)
  | [] => ([], [])
  | .name a :: cs => (a :: (splitComponents cs).1, (splitComponents cs).2)
  | .empty :: cs => ([], (.empty, (splitComponents cs).1) :: (splitComponents cs).2)
  | .self :: cs => ([], (.self, (splitComponents cs).1) :: (splitComponents cs).2)
  | .parent :: cs => ([], (.parent, (splitComponents cs).1) :: (splitComponents cs).2)

def splitPath (p : Accordion.Path Γ) : List Γ × List (Step × List Γ) :=
  splitComponents p.components

def normalWord (w : List Γ) : List (Step × List Γ) → List Γ
  | [] => w
  | (C, w') :: r => normalWord (C.apply w ++ w') r

def prefixWords (w : List Γ) : List (Step × List Γ) → List (List Γ)
  | [] => []
  | (C, w') :: r => w :: prefixWords (C.apply w ++ w') r

def IsDir [Ord Γ] (base : FileTree Γ) (w : List Γ) : Prop :=
  (FileTree.Zipper.traverse (Path.descend w) (FileTree.Zipper.zip base)).map
    (·.focus.shape) = some .dirc

instance [Ord Γ] (base : FileTree Γ) (w : List Γ) : Decidable (IsDir base w) :=
  inferInstanceAs (Decidable (_ = _))

def ReadsOn {α : Sort _} [Ord Γ] (U : TWE.Free V) (g : WordModel Γ V → α) : Prop :=
  ∀ M M', M ≡[U] M' → g M = g M'

section

variable [Ord Γ] [DecidableEq Γ]

def FreshState.Holds (M : WordModel Γ V) (s : FreshState Γ V) : Prop :=
  ∀ F ∈ s.definitions, M.toTWE ⊨ F

def FreshState.Valid (s : FreshState Γ V) : Prop :=
  ∀ F ∈ s.definitions, ReadsOn s.used (·.toTWE ⊨ F)

/-- A run of the rules from `s` to `s'`: it keeps the equations of `s`, and its own equations hold
after changing only variables that are not in use in `s`. -/
structure FreshState.Extends (s s' : FreshState Γ V) : Prop where
  used_subset : s.used ⊆ s'.used
  subset : s.definitions ⊆ s'.definitions
  valid : s.Valid → s'.Valid
  complete : s.Valid → ∀ M : WordModel Γ V, s.Holds M → ∃ M', M ≡[s.used] M' ∧ s'.Holds M'

end

def FreshState.HasLinearConstants (s : FreshState Γ V) : Prop :=
  ∀ F ∈ s.definitions, F.hasLinearConstants

/-- The decomposition of the variables of `φ` that `m` induces: a path variable has the non-linear
components of its value, between fresh blocks. -/
def modelDecomposition [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (m : TWE.Model Γ V)
    (φ : TWE.Formula Γ V) : VariableDecomposition V where
  components := φ.compVars.map fun x ↦ (x, (m.σComp x).kind)
  paths := ((freshDecompositions (φ.pathVars.map fun X ↦
    (X, (splitPath (m.σPath X)).2.map Prod.fst))).run φ.free).1

end ToLinear

end Bounded

end TWE

end Accordion

end
