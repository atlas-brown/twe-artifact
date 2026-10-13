module

public import Accordion.TWE.Bounded

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

variable {Γ : Type} {V : TWE.Vars}

/-- The empty component is a non-linear component, treated like `.`, so that its directory check is
kept. -/
inductive Step where
  | empty
  | self
  | parent
  deriving DecidableEq

inductive ComponentKind where
  | name
  | empty
  | self
  | parent
  deriving DecidableEq

/-- For each component variable its kind, and for each path variable `X` its decomposition
`X = X₀ C₁ X₁ ⋯ Cₘ Xₘ`, as the block `X₀` and the pairs `(Cᵢ, Xᵢ)`. -/
structure VariableDecomposition (V : TWE.Vars) where
  components : List (V.Comp × ComponentKind)
  paths : List (V.Path × V.Path × List (Step × V.Path))

/-- `B₁ C₁ B₂ ⋯ Cₘ Bₘ₊₁`: the first block `B₁` and the pairs `(Cᵢ, Bᵢ₊₁)`. -/
structure Decomposition (Γ : Type) (V : TWE.Vars) where
  first : TWE.Path Γ V
  rest : List (Step × TWE.Path Γ V)

/-- The normal prefixes of `B₁ C₁ B₂ ⋯ Cₘ Bₘ₊₁`: the locations `Y₁, …, Yₘ` before the
non-linear components, and the location `Yₘ₊₁` of the whole path. -/
structure NormalPrefixes (V : TWE.Vars) where
  prefixes : List V.Loc
  last : V.Loc

end ToLinear

end Bounded

end TWE

end Accordion

end
