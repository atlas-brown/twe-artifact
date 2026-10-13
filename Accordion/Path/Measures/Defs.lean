module

public import Accordion.Path

@[expose] public section

namespace Accordion

namespace Component

variable {Γ : Type}

def depth : Component Γ → Int
  | .name _ => 1
  | .empty => 0
  | .self => 0
  | .parent => -1

end Component

namespace Path

variable {Γ : Type}

def depth : Path Γ → Int
  | .nil => 0
  | .app p q => p.depth + q.depth

def length : Path Γ → Nat
  | .nil => 0
  | .app p _ => p.length + 1

def IsPrefix (p q : Path Γ) : Prop :=
  ∃ r, q = p ++ r

/-- A path is anchored when no prefix of it has negative depth (§5.1). -/
def IsAnchored (p : Path Γ) : Prop :=
  ∀ q : Path Γ, IsPrefix q p → 0 ≤ depth q

/-- A path is balanced when it is anchored and has depth zero (§5.1). -/
def IsBalanced (p : Path Γ) : Prop :=
  p.IsAnchored ∧ p.depth = 0

end Path

end Accordion

end
