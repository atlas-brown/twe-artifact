module

@[expose] public section

namespace Accordion

class Sat (M F : Type) where
  sat : M → F → Prop

/-- A Boolean combination of atoms (Fig. 5). -/
inductive Formula (Atom : Type) where
  | top
  | bot
  | atom (a : Atom)
  | conj (φ ψ : Formula Atom)
  | disj (φ ψ : Formula Atom)
  | neg (φ : Formula Atom)

namespace Formula

scoped notation "⊤" => Accordion.Formula.top
scoped notation "⊥" => Accordion.Formula.bot
scoped infixl:55 " ⋏ " => Accordion.Formula.conj
scoped infixl:53 " ⋎ " => Accordion.Formula.disj
scoped prefix:58 "∼" => Accordion.Formula.neg

def bind {A B : Type} (f : A → Formula B) : Formula A → Formula B
  | ⊤ => ⊤
  | ⊥ => ⊥
  | .atom a => f a
  | φ ⋏ ψ => bind f φ ⋏ bind f ψ
  | φ ⋎ ψ => bind f φ ⋎ bind f ψ
  | ∼φ => ∼(bind f φ)

def atoms {A : Type} : Formula A → List A
  | ⊤ => []
  | ⊥ => []
  | .atom a => [a]
  | φ ⋏ ψ => atoms φ ++ atoms ψ
  | φ ⋎ ψ => atoms φ ++ atoms ψ
  | ∼φ => atoms φ

def bigConj : List (Formula A) → Formula A
  | [] => ⊤
  | φ :: Φ => φ ⋏ bigConj Φ

def bigDisj : List (Formula A) → Formula A
  | [] => ⊥
  | φ :: Φ => φ ⋎ bigDisj Φ

/-- Satisfaction of a formula in a model (Fig. 5). -/
@[simp]
def sat {M Atom : Type} [Sat M Atom] (m : M) : Formula Atom → Prop
  | ⊤ => True
  | ⊥ => False
  | .atom a => Sat.sat m a
  | φ ⋏ ψ => sat m φ ∧ sat m ψ
  | φ ⋎ ψ => sat m φ ∨ sat m ψ
  | ∼φ => ¬ sat m φ

end Formula

notation:50 m:51 " ⊨ " φ:51 => Formula.sat m φ

end Accordion

end
