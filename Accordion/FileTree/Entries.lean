module

@[expose] public section

namespace Accordion

namespace FileTree

/-- The entries of a directory: a finite map from names (Fig. 3). -/
structure Entries (Γ : Type) (β : Type) where
  map : List (Γ × β)
  deriving Repr, DecidableEq

namespace Entries

variable {Γ β : Type}

def empty : Entries Γ β := ⟨[]⟩

instance : EmptyCollection (Entries Γ β) := ⟨empty⟩

variable [Ord Γ]

protected def Mem (m : Entries Γ β) (a : Γ) : Prop := ∃ p ∈ m.map, compare a p.1 = .eq

instance : Membership Γ (Entries Γ β) := ⟨Entries.Mem⟩

def insList (a : Γ) (b : β) : List (Γ × β) → List (Γ × β)
  | [] => [(a, b)]
  | (c, d) :: r =>
      match compare a c with
      | .lt => (a, b) :: (c, d) :: r
      | .eq => (c, b) :: r
      | .gt => (c, d) :: insList a b r

def insert (m : Entries Γ β) (a : Γ) (b : β) : Entries Γ β := ⟨insList a b m.map⟩

def lookup (m : Entries Γ β) (a : Γ) : Option β :=
  m.map.findSome? (fun p => if compare a p.1 = .eq then some p.2 else none)

def erase (m : Entries Γ β) (a : Γ) : Entries Γ β :=
  ⟨m.map.filter (fun p => compare a p.1 != .eq)⟩

instance : GetElem? (Entries Γ β) Γ β (fun m a => a ∈ m) where
  getElem m a h := (m.lookup a).get (by
    obtain ⟨p, hp, hap⟩ := h
    rw [lookup, List.findSome?_isSome_iff]
    exact ⟨p, hp, by simp [hap]⟩)
  getElem? m a := m.lookup a

def Canonical (m : Entries Γ β) : Prop :=
  m.map.Pairwise (fun p q => compare p.1 q.1 = .lt)

end Entries

end FileTree

end Accordion

end
