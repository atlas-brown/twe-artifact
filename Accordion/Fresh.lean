module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Accordion

/-- A supply of fresh elements: one outside every finite set (§6). -/
class Fresh (α : Type) where
  fresh : Finset α → α
  fresh_notMem (s : Finset α) : fresh s ∉ s

instance {α : Type} [Fresh α] : Infinite α :=
  .of_not_fintype fun _ => Fresh.fresh_notMem (Finset.univ : Finset α) (Finset.mem_univ _)

instance {α β : Type} [Fresh α] : Fresh (α ⊕ β) where
  fresh s := .inl (Fresh.fresh s.toLeft)
  fresh_notMem _ h := Fresh.fresh_notMem _ (Finset.mem_toLeft.2 h)

instance : Fresh Nat where
  fresh s := s.sup id + 1
  fresh_notMem _ h := Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)

instance : Fresh String where
  fresh s := String.ofList (List.replicate (s.sup String.length + 1) 'a')
  fresh_notMem s h := by
    have := Finset.le_sup (f := String.length) h
    rw [String.length_ofList, List.length_replicate] at this
    omega

end Accordion

end
