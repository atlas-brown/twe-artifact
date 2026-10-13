module

public import Accordion.TWE.Linear

@[expose] public section

namespace Accordion

variable {Γ : Type} {V : TWE.Vars}

def Path.nonlinearCount : Path Γ → Nat
  | .nil => 0
  | .app p (.name _) => nonlinearCount p
  | .app p .empty => nonlinearCount p + 1
  | .app p .self => nonlinearCount p + 1
  | .app p .parent => nonlinearCount p + 1

namespace TWE

def Model.BoundedAt [Ord Γ] (k : Nat) (m : TWE.Model Γ V) (φ : TWE.Formula Γ V) : Prop :=
  ∀ p ∈ φ.paths, (m.evalPath p).nonlinearCount ≤ k

namespace Bounded

/-- A model of `k`-bounded TWE: a well-formed model in which every path of the formula has at most
`k` non-linear components (§6.2). -/
def Model [Ord Γ] (k : Nat) (φ : TWE.Formula Γ V) : Type :=
  {m : TWE.Model Γ V // m.WF ∧ m.BoundedAt k φ}

namespace Formula

/-- Satisfiability in `k`-bounded TWE (§6.2). -/
def SAT [Ord Γ] [DecidableEq Γ] (k : Nat) (φ : TWE.Formula Γ V) : Prop :=
  ∃ m : Bounded.Model k φ, m.1 ⊨ φ

end Formula

end Bounded

end TWE

end Accordion

end
