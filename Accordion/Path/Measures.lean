module

public import Accordion.Path.Measures.Properties

@[expose] public section

namespace Accordion

namespace Path

variable {Γ : Type}

theorem IsAnchored.depth_eq_length_norm {p : Path Γ} (hp : p.IsAnchored) :
    p.depth = (p.norm.length : Int) :=
  depth_eq_length_norm_of_isAnchored hp

theorem isAnchored_iff_norm_ne (a : Γ) (p : Path Γ) :
    p.IsAnchored ↔ p.norm ≠ ((a : Path Γ) ++ p).norm :=
  isAnchored_iff_norm_ne_norm_join a p

theorem isBalanced_iff_norm_eq_nil (a : Γ) (p : Path Γ) :
    p.IsBalanced ↔ p.norm = ε ∧ ((a : Path Γ) ++ p).norm ≠ ε :=
  isBalanced_iff_norm_eq_nil_and_norm_join_ne_nil a p

end Path

end Accordion

end
