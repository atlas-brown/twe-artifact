module

public import Accordion.FileTree
public import Accordion.FileTree.Entries.Properties
public import Accordion.Path.Properties

@[expose] public section

namespace Accordion

namespace FileTree

variable {Γ : Type}

theorem Ctx.path_compose_node (C : Ctx Γ) (δ : Entries Γ (FileTree Γ)) (a : Γ) :
    (C.compose (.node δ a .hole)).path = C.path ++ (a : Path Γ) := by
  induction C with
  | hole => simp [Ctx.compose, Ctx.path, Path.init, Path.join]
  | node δ0 a0 C0 ih =>
      simp only [Path.append_eq] at ih ⊢
      simp only [Ctx.compose, Ctx.path, ih, Path.append_eq]
      exact Path.join_assoc _ _ _

theorem Ctx.path_linear (C : Ctx Γ) : C.path.Linear := by
  induction C with
  | hole => trivial
  | node δ a C ih => exact Path.join_linear (by simp [Path.init, Path.Linear]) ih

@[simp] theorem Ctx.compose_hole (C : Ctx Γ) : C.compose .hole = C := by
  induction C with
  | hole => rfl
  | node δ a C ih => rw [Ctx.compose, ih]

theorem Ctx.compose_assoc (C D E : Ctx Γ) :
    (C.compose D).compose E = C.compose (D.compose E) := by
  induction C with
  | hole => rfl
  | node δ a C ih => rw [Ctx.compose, Ctx.compose, Ctx.compose, ih]

variable [Ord Γ]

theorem canonical_of_lookup {δ : Entries Γ (FileTree Γ)} {a : Γ} {τ : FileTree Γ}
    (hδ : FileTree.Canonical (.dirc δ)) (h : δ.lookup a = some τ) : τ.Canonical := by
  cases hδ with
  | dirc _ hsub =>
      unfold Entries.lookup at h
      obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
      split at hfx
      · injection hfx with hfx
        exact hfx ▸ hsub x hx
      · exact absurd hfx (by simp)

theorem canonical_erase_dirc {δ : Entries Γ (FileTree Γ)} {a : Γ}
    (hδ : FileTree.Canonical (.dirc δ)) : FileTree.Canonical (.dirc (δ.erase a)) := by
  cases hδ with
  | dirc hcanon hsub =>
      refine .dirc (Entries.canonical_erase hcanon a) (fun p hp => hsub p ?_)
      simp only [Entries.erase, List.mem_filter] at hp
      exact hp.1

theorem canonical_insert_dirc [Std.TransOrd Γ] {δ : Entries Γ (FileTree Γ)} {a : Γ}
    {τ : FileTree Γ} (hδ : FileTree.Canonical (.dirc δ)) (hτ : τ.Canonical) :
    FileTree.Canonical (.dirc (δ.insert a τ)) := by
  cases hδ with
  | dirc hcanon hsub =>
      refine .dirc (Entries.canonical_insert hcanon a τ) (fun p hp => ?_)
      rcases Entries.mem_insert_iff hp with h | h
      · exact h ▸ hτ
      · exact hsub p h

theorem Ctx.canonical_compose_node (C : Ctx Γ) (δ : Entries Γ (FileTree Γ)) (a : Γ) :
    (C.compose (.node δ a .hole)).Canonical ↔ C.Canonical ∧ FileTree.Canonical (.dirc δ) := by
  induction C with
  | hole => simp [Ctx.compose, Ctx.Canonical]
  | node δ0 a0 C0 ih => simp only [Ctx.compose, Ctx.Canonical, ih, and_assoc]

theorem Ctx.fill_canonical [Std.TransOrd Γ] {C : Ctx Γ} {f : Focus Γ}
    {τ : FileTree Γ}
    (hC : C.Canonical) (hf : f.Canonical) (h : C.fill f = some τ) : τ.Canonical := by
  induction C generalizing τ with
  | hole =>
      cases f with
      | tree τ' =>
          simp only [Ctx.fill, Option.some.injEq] at h
          exact h ▸ hf
      | abst => simp [Ctx.fill] at h
  | node δ a C0 ih =>
      obtain ⟨hδ, hC0⟩ := hC
      simp only [Ctx.fill] at h
      cases h0 : C0.fill f with
      | some τ0 =>
          rw [h0] at h
          simp only [Option.some.injEq] at h
          exact h ▸ canonical_insert_dirc hδ (ih hC0 h0)
      | none =>
          rw [h0] at h
          simp only [Option.some.injEq] at h
          exact h ▸ hδ

theorem Entries.mem_dom_iff [Std.LawfulEqOrd Γ] [DecidableEq Γ] {β : Type} (δ : Entries Γ β)
    (a : Γ) : a ∈ δ.dom ↔ a ∈ δ := by
  change _ ↔ ∃ p ∈ δ.map, compare a p.1 = .eq
  simp only [Entries.dom, List.mem_toFinset, List.mem_map, Entries.compare_eq_iff]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

theorem canonical_dirc_ofSigmas [Std.TransOrd Γ] (children : List ((_ : Γ) × FileTree Γ))
    (hchildren : ∀ child ∈ children, child.2.Canonical) :
    (FileTree.dirc (Entries.ofSigmas children)).Canonical := by
  induction children with
  | nil => exact .dirc Entries.canonical_empty fun _ h => nomatch h
  | cons child children ih =>
      exact canonical_insert_dirc (ih fun c hc => hchildren c (.tail _ hc))
        (hchildren child (.head _))

@[simp] theorem canonical_dirc_empty : (FileTree.dirc (∅ : Entries Γ (FileTree Γ))).Canonical :=
  .dirc Entries.canonical_empty nofun

end FileTree

end Accordion

end
