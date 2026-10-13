module

public import Accordion.TWE

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : Vars}

namespace Path

def subterms : TWE.Path Γ V → List (TWE.Path Γ V)
  | p@.nil => [p]
  | p@(.init _) => [p]
  | p@(.join q r) => p :: subterms q ++ subterms r
  | p@(.loc _) => [p]
  | p@(.var _) => [p]
  | p@(.norm q) => p :: subterms q

end Path

namespace Formula

def paths : TWE.Formula Γ V → List (TWE.Path Γ V)
  | .top | .bot => []
  | .conj φ ψ | .disj φ ψ => paths φ ++ paths ψ
  | .neg φ => paths φ
  | .atom (.pathEq p q) => p.subterms ++ q.subterms
  | .atom (.pathIsLin p) => p.subterms
  | .atom (.treeWalk p _ _) => p.subterms
  | .atom (.treeShape _ _) | .atom (.setEq _ _) | .atom (.setMem _ _) => []

end Formula

def Model.LinearAt [Ord Γ] (m : TWE.Model Γ V) (φ : TWE.Formula Γ V) : Prop :=
  ∀ p ∈ φ.paths, (m.evalPath p).Linear

namespace Linear

/-- A model of linear TWE: a well-formed model in which every path of the formula is linear
(§6.1). -/
def Model [Ord Γ] (φ : TWE.Formula Γ V) : Type :=
  {m : TWE.Model Γ V // m.WF ∧ m.LinearAt φ}

namespace Formula

/-- Satisfiability in linear TWE (§6.1). -/
def SAT [Ord Γ] [DecidableEq Γ] (φ : TWE.Formula Γ V) : Prop :=
  ∃ m : Linear.Model φ, m.1 ⊨ φ

end Formula

end Linear

end TWE

end Accordion

end
