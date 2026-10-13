module

@[expose] public section

namespace Accordion

/-- A path component (Fig. 2). -/
inductive Component (Γ : Type) where
  | name (a : Γ)
  | empty
  | self
  | parent
  deriving DecidableEq, Repr

/-- A path (Fig. 2). -/
inductive Path (Γ : Type) where
  | nil
  | app (p : Path Γ) (q : Component Γ)
  deriving DecidableEq, Repr

namespace Path

variable {Γ : Type}

@[coe] def init (q : Component Γ) : Path Γ := .app .nil q

/-- The concatenation of two paths (Fig. 4). -/
def join (p : Path Γ) : Path Γ → Path Γ
  | .nil => p
  | .app q c => .app (join p q) c

/-- The last component of a path (Fig. 4). -/
def base : Path Γ → Path Γ
  | .nil => .nil
  | .app _ q => .app .nil q

/-- A path without its last component (Fig. 4). -/
def dir : Path Γ → Path Γ
  | .nil => .nil
  | .app p _ => p

def components : Path Γ → List (Component Γ)
  | .nil => []
  | .app p q => components p ++ [q]

/-- The normal form of a path (Fig. 4). -/
def norm : Path Γ → Path Γ
  | .nil => .nil
  | .app p (.name a) => .app (norm p) (.name a)
  | .app p .empty => norm p
  | .app p .self => norm p
  | .app p .parent => dir (norm p)

/-- A path is linear when every component is a name (Fig. 5). -/
def Linear : Path Γ → Prop
  | .nil => True
  | .app p (.name _) => Linear p
  | .app _ .empty => False
  | .app _ .self => False
  | .app _ .parent => False

def isLinear : Path Γ → Bool
  | .nil => true
  | .app p (.name _) => isLinear p
  | .app _ .empty => false
  | .app _ .self => false
  | .app _ .parent => false

instance (p : Path Γ) : Decidable p.Linear :=
  decidable_of_iff (p.isLinear = true) <| by
    induction p with
    | nil => simp [Linear, isLinear]
    | app p c ih => cases c <;> simp [Linear, isLinear, ih]

end Path

instance {Γ : Type} : Coe Γ (Component Γ) := ⟨Component.name⟩
instance {Γ : Type} : Coe (Component Γ) (Path Γ) := ⟨Path.init⟩

instance {Γ : Type} : HDiv (Path Γ) (Component Γ) (Path Γ) := ⟨Path.app⟩
instance {Γ : Type} : Append (Path Γ) := ⟨Path.join⟩

scoped notation "ϵ" => Component.empty
scoped notation "∙" => Component.self
scoped notation "‥" => Component.parent
scoped notation "ε" => Path.nil

def Path.names {Γ : Type} : Path Γ → List Γ
  | .nil => []
  | .app p (.name a) => names p ++ [a]
  | .app p _ => names p

@[coe] def Path.descend {Γ : Type} : List Γ → Path Γ
  | [] => ε
  | a :: w => (a : Path Γ) ++ descend w

instance {Γ : Type} : Coe (List Γ) (Path Γ) := ⟨Path.descend⟩

end Accordion

end
