module

public import Accordion.TWE.Linear.ToWE.Properties.RewriteEntriesAtom
public import Mathlib.Data.List.Sublists

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

theorem Tree.updates_subset_of_mem_updates {u U : TWE.Tree V} (h : u ∈ U.updates) :
    u.updates ⊆ U.updates := by
  induction U with
  | select T l ih => exact ih h
  | update T l T' ihT ihT' =>
      simp only [TWE.Tree.updates, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact List.Subset.refl _
      · exact List.Subset.trans (ihT h) fun x hx ↦ by simp [TWE.Tree.updates, hx]
      · exact List.Subset.trans (ihT' h) fun x hx ↦ by simp [TWE.Tree.updates, hx]
  | _ => simp [TWE.Tree.updates] at h

theorem Tree.size_le_of_mem_updates {u U : TWE.Tree V} (h : u ∈ U.updates) : u.size ≤ U.size := by
  induction U with
  | select T l ih => have := ih h; simp only [TWE.Tree.size]; omega
  | update T l T' ihT ihT' =>
      simp only [TWE.Tree.updates, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact le_rfl
      · have := ihT h; simp only [TWE.Tree.size]; omega
      · have := ihT' h; simp only [TWE.Tree.size]; omega
  | _ => simp [TWE.Tree.updates] at h

theorem Tree.exists_eq_update_of_mem_updates {u U : TWE.Tree V} (h : u ∈ U.updates) :
    ∃ T l T', u = .update T l T' := by
  induction U with
  | select T l ih => exact ih h
  | update T l T' ihT ihT' =>
      simp only [TWE.Tree.updates, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      exacts [⟨T, l, T', rfl⟩, ihT h, ihT' h]
  | _ => simp [TWE.Tree.updates] at h

namespace Linear

namespace ToWE

open scoped Accordion.Guess BigConnectives

theorem evalTree_eq_none_of_mem_updates [Ord Γ] {m : WordModel Γ V} {u U : TWE.Tree V}
    (h : u ∈ U.updates) (hu : m.toTWE.evalTree u = none) : m.toTWE.evalTree U = none := by
  induction U with
  | select T l ih => simp [TWE.Model.evalTree, ih h]
  | update T l T' ihT ihT' =>
      simp only [TWE.Tree.updates, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact hu
      · simp [TWE.Model.evalTree, ihT h]
      · simp only [TWE.Model.evalTree, ihT' h]
        rcases m.toTWE.evalTree T with _ | (_ | _) | _ <;> simp
  | _ => simp [TWE.Tree.updates] at h

theorem allAtoms_ne_undefined_updateDefined (T : TWE.Tree V) (l : V.Loc) (T' : TWE.Tree V) :
    (updateDefined T (l : Word Γ V) T').AllAtoms fun α ↦ ∀ U ℓ, α ≠ .undefined U ℓ := by
  simp only [updateDefined]
  all_atoms <;> simp

section Assume

variable [TWE.Vars.Comparable V]

theorem allAtoms_updates_subset_updateCase (defined : List (TWE.Tree V)) (T : TWE.Tree V)
    (l : V.Loc) (T' : TWE.Tree V) :
    (updateCase (Γ := Γ) defined (.update T l T')).AllAtoms fun α ↦
      (∀ v ∈ α.updates, v ∈ T.updates ∨ v ∈ T'.updates) ∧ α.EntriesNamed := by
  simp only [updateCase]
  split <;> simp only [updateDefined, updateUndefined] <;> all_atoms <;>
    simp +contextual [Atom.updates, Atom.EntriesNamed]

theorem run_caseUpdates (β : Conj Γ V) (U : TWE.Free V) :
    ((caseUpdates β).run U).1 =
      (Guess.sublist (β.flatMap Atom.updates).dedup).flatMap fun defined ↦
        ((⋀ α ∈ β, (α : Guess (Conj Γ V))) ∧ ⋀ u ∈ (β.flatMap Atom.updates).dedup,
            updateCase defined u).flatMap fun γ ↦ ⋀ α ∈ γ, assumeDefined defined α :=
  rfl

theorem mem_assumeDefined {defined : List (TWE.Tree V)} {α : Atom Γ V} {κ : Conj Γ V}
    (h : κ ∈ assumeDefined defined α) :
    (κ = [α] ∧ ∀ u ∈ α.updates, u ∈ defined) ∨ κ = [] ∧ ∃ U ℓ, α = .undefined U ℓ := by
  unfold assumeDefined at h
  split_ifs at h with hall hund
  · simp_all
  · cases α <;> simp_all
  · simp at h

theorem allAtoms_flatMap_assumeDefined {defined : List (TWE.Tree V)} {P : Atom Γ V → Prop}
    {E : Guess (Conj Γ V)} (hE : E.AllAtoms P) :
    Guess.AllAtoms P (E.flatMap fun γ ↦ ⋀ α ∈ γ, assumeDefined defined α) :=
  Guess.AllAtoms.flatMap fun γ hγ ↦ Guess.AllAtoms.all fun α hα κ hκ a ha ↦ by
    obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := mem_assumeDefined hκ
    · exact (List.mem_singleton.1 ha) ▸ hE γ hγ α hα
    · cases ha

variable [Ord Γ] [DecidableEq Γ] {m : WordModel Γ V} {defined : List (TWE.Tree V)}

theorem sat_assumeDefined_iff {α : Atom Γ V}
    (hexact : ∀ u ∈ α.updates, u ∈ defined ↔ (m.toTWE.evalTree u).isSome) :
    Guess.sat m (assumeDefined defined α) ↔ α.sat m := by
  by_cases hall : α.updates.all (· ∈ defined)
  · simp [assumeDefined, hall]
  obtain ⟨u, hu, hnot⟩ : ∃ u ∈ α.updates, u ∉ defined := by simpa using hall
  have hnone : m.toTWE.evalTree u = none := by simpa [hexact u hu] using hnot
  cases α with
  | shape T ℓ h =>
      simp [assumeDefined, hall, Atom.sat, ObservesShape,
        evalTree_eq_none_of_mem_updates (U := T) hu hnone]
  | undefined T ℓ =>
      simp [assumeDefined, hall, Atom.sat, ObservesShape,
        evalTree_eq_none_of_mem_updates (U := T) hu hnone]
  | entries R T ℓ =>
      simp [assumeDefined, hall, Atom.sat, ObservesEntries,
        evalTree_eq_none_of_mem_updates (U := T) hu hnone]
  | _ => simp [Atom.updates] at hu

theorem sat_flatMap_assumeDefined_iff_exists {E : Guess (Conj Γ V)} :
    Guess.sat m (E.flatMap fun γ ↦ ⋀ α ∈ γ, assumeDefined defined α) ↔
      ∃ γ ∈ E, ∀ α ∈ γ, Guess.sat m (assumeDefined defined α) := by
  simp

theorem sat_flatMap_assumeDefined_iff {E : Guess (Conj Γ V)}
    (hE : E.AllAtoms fun α ↦ ∀ u ∈ α.updates, u ∈ defined ↔ (m.toTWE.evalTree u).isSome) :
    Guess.sat m (E.flatMap fun γ ↦ ⋀ α ∈ γ, assumeDefined defined α) ↔ Guess.sat m E := by
  rw [sat_flatMap_assumeDefined_iff_exists]
  exact exists_congr fun γ ↦ and_congr_right fun hγ ↦
    forall₂_congr fun α hα ↦ sat_assumeDefined_iff (hE γ hγ α hα)

theorem sat_updateCase_iff {T T' : TWE.Tree V} {l : V.Loc} :
    Guess.sat m (updateCase defined (.update T l T')) ↔
      (.update T l T' ∈ defined ↔ (m.toTWE.evalTree (.update T l T')).isSome) := by
  by_cases hu : TWE.Tree.update T l T' ∈ defined <;>
    simp [updateCase, hu, sat_updateDefined_iff, sat_updateUndefined_iff]

end Assume

section Cases

variable [TWE.Vars.Comparable V] (β : Conj Γ V)

theorem Conj.exists_eq_update_of_mem_updates :
    ∀ u ∈ (β.flatMap Atom.updates).dedup, ∃ T l T', u = .update T l T' := by
  intro u hu
  obtain ⟨α, -, hu⟩ := List.mem_flatMap.1 (List.mem_dedup.1 hu)
  cases α <;> simp only [Atom.updates] at hu <;>
    first | exact Tree.exists_eq_update_of_mem_updates hu | simp at hu

theorem Conj.mem_updates_of_mem_updates : ∀ u ∈ (β.flatMap Atom.updates).dedup, ∀ v ∈ u.updates,
    v ∈ (β.flatMap Atom.updates).dedup := by
  intro u hu v hv
  obtain ⟨α, hα, hu⟩ := List.mem_flatMap.1 (List.mem_dedup.1 hu)
  refine List.mem_dedup.2 (List.mem_flatMap.2 ⟨α, hα, ?_⟩)
  cases α <;> simp only [Atom.updates] at hu ⊢ <;>
    first | exact Tree.updates_subset_of_mem_updates hu hv | simp at hu

theorem allAtoms_all_updateCase (defined : List (TWE.Tree V)) :
    ((⋀ α ∈ β, (α : Guess (Conj Γ V))) ∧ ⋀ u ∈ (β.flatMap Atom.updates).dedup,
        updateCase defined u).AllAtoms fun α ↦
      (∀ u ∈ α.updates, u ∈ (β.flatMap Atom.updates).dedup) ∧ (α ∈ β ∨ α.EntriesNamed) := by
  refine .and (.all fun α hα ↦ .inject ⟨fun u hu ↦ ?_, .inl hα⟩) (.all fun u hu ↦ ?_)
  · exact List.mem_dedup.2 (List.mem_flatMap.2 ⟨α, hα, hu⟩)
  · obtain ⟨T, l, T', rfl⟩ := Conj.exists_eq_update_of_mem_updates β u hu
    refine (allAtoms_updates_subset_updateCase defined T l T').mono fun α ⟨hα, hnamed⟩ ↦
      ⟨fun v hv ↦ Conj.mem_updates_of_mem_updates β _ hu v ?_, .inr hnamed⟩
    simp [TWE.Tree.updates, hα v hv]

theorem run_caseUpdates_mem_entriesNamed (hβ : ∀ α ∈ β, α.EntriesNamed) (U : TWE.Free V) :
    ((caseUpdates β).run U).1.AllAtoms Atom.EntriesNamed := by
  rw [run_caseUpdates]
  exact .flatMap fun defined _ ↦ allAtoms_flatMap_assumeDefined
    ((allAtoms_all_updateCase β defined).mono fun α hα ↦ hα.2.elim (hβ α) id)

variable [Ord Γ] [DecidableEq Γ]

theorem mem_defined_iff_isSome_of_sat_updateCase {m : WordModel Γ V}
    {defined us : List (TWE.Tree V)} (hupdates : ∀ u ∈ us, ∃ T l T', u = .update T l T')
    (hclosed : ∀ u ∈ us, ∀ v ∈ u.updates, v ∈ us)
    (hcases : ∀ u ∈ us, ∃ δ ∈ updateCase defined u,
      ∀ α ∈ δ, Guess.sat m (assumeDefined defined α)) :
    ∀ u ∈ us, u ∈ defined ↔ (m.toTWE.evalTree u).isSome := by
  intro u
  induction hsize : u.size using Nat.strong_induction_on generalizing u with
  | _ n ih =>
      intro hu
      obtain ⟨T, l, T', rfl⟩ := hupdates u hu
      obtain ⟨δ, hδ, hsat⟩ := hcases _ hu
      refine sat_updateCase_iff.1
        ⟨δ, hδ, fun α hα ↦ (sat_assumeDefined_iff fun v hv ↦ ?_).1 (hsat α hα)⟩
      have hsub := (allAtoms_updates_subset_updateCase defined T l T' δ hδ α hα).1 v hv
      have hvT : v ∈ (TWE.Tree.update T l T').updates := by simp [TWE.Tree.updates, hsub]
      refine ih v.size ?_ v rfl (hclosed _ hu v hvT)
      rcases hsub with h | h <;> have := Tree.size_le_of_mem_updates h <;>
        simp only [← hsize, TWE.Tree.size] <;> omega

theorem run_caseUpdates_equisat (U : TWE.Free V) :
    Guess.SAT ((caseUpdates β).run U).1 ↔ β.SAT := by
  rw [run_caseUpdates]
  set us := (β.flatMap Atom.updates).dedup
  have hexact {m : WordModel Γ V} {defined : List (TWE.Tree V)}
      (h : ∀ u ∈ us, u ∈ defined ↔ (m.toTWE.evalTree u).isSome) :=
    (allAtoms_all_updateCase β defined).mono fun α hα u hu ↦ h u (hα.1 u hu)
  constructor
  · rintro ⟨m, hsat⟩
    obtain ⟨defined, -, hsat⟩ := (Guess.sat_flatMap _ _).1 hsat
    obtain ⟨γ, hγ, hγsat⟩ := sat_flatMap_assumeDefined_iff_exists.1 hsat
    obtain ⟨γ₁, -, γ₂, hγ₂, rfl⟩ := Guess.mem_and.1 hγ
    have hdefined := mem_defined_iff_isSome_of_sat_updateCase
      (Conj.exists_eq_update_of_mem_updates β) (Conj.mem_updates_of_mem_updates β)
      fun u hu ↦ by
        obtain ⟨δ, hδ, hsub⟩ := (Guess.mem_all hγ₂).1 u hu
        exact ⟨δ, hδ, fun α hα ↦ hγsat α (List.mem_append_right _ (hsub hα))⟩
    have := ((Guess.sat_and _ _).1 ((sat_flatMap_assumeDefined_iff (hexact hdefined)).1 hsat)).1
    exact ⟨m, by simpa [Conj.sat] using this⟩
  · rintro ⟨m, hsat⟩
    let defined := us.filter fun u ↦ (m.toTWE.evalTree u).isSome
    have hdefined : ∀ u ∈ us, u ∈ defined ↔ (m.toTWE.evalTree u).isSome :=
      fun u hu ↦ by simp [defined, hu]
    refine ⟨m, (Guess.sat_flatMap _ _).2 ⟨defined,
      Guess.mem_sublist.2 (List.mem_sublists.2 List.filter_sublist),
      (sat_flatMap_assumeDefined_iff (hexact hdefined)).2
        ((Guess.sat_and _ _).2 ⟨by simpa [Conj.sat] using hsat, ?_⟩)⟩⟩
    refine (Guess.sat_all _ _).2 fun u hu ↦ ?_
    obtain ⟨T, l, T', rfl⟩ := Conj.exists_eq_update_of_mem_updates β u hu
    exact sat_updateCase_iff.2 (hdefined _ hu)

theorem run_caseUpdates_updatesDefined (U : TWE.Free V) :
    Guess.UpdatesDefined ((caseUpdates β).run U).1 := by
  rw [run_caseUpdates]
  intro γ' hγ' m hor
  obtain ⟨defined, hdefined, hγ'⟩ := Guess.mem_flatMap.1 hγ'
  obtain ⟨γ, hγ, hγ'⟩ := Guess.mem_flatMap.1 hγ'
  obtain ⟨γ₁, -, γ₂, hγ₂, rfl⟩ := Guess.mem_and.1 hγ
  obtain ⟨hcover, hatoms⟩ := Guess.mem_all hγ'
  have hkept : ∀ a ∈ γ', ∀ u ∈ a.updates, u ∈ defined := fun a ha ↦ by
    obtain ⟨α, -, κ, hκ, ha⟩ := hatoms a ha
    obtain ⟨rfl, h⟩ | ⟨rfl, -⟩ := mem_assumeDefined hκ
    · exact List.mem_singleton.1 ha ▸ h
    · cases ha
  suffices h : ∀ u ∈ defined, (m.toTWE.evalTree u).isSome from
    fun a ha u hu ↦ h u (hkept a ha u hu)
  intro u
  induction hsize : u.size using Nat.strong_induction_on generalizing u with
  | _ n ih =>
      intro hu
      have hus := (List.mem_sublists.1 (Guess.mem_sublist.1 hdefined)).subset hu
      obtain ⟨T, l, T', rfl⟩ := Conj.exists_eq_update_of_mem_updates β _ hus
      obtain ⟨δ, hδ, hsub⟩ := (Guess.mem_all hγ₂).1 _ hus
      have hδ' : δ ∈ updateDefined T (l : Word Γ V) T' := by simpa [updateCase, hu] using hδ
      have hδγ : ∀ α ∈ δ, α ∈ γ' := fun α hα ↦ by
        obtain ⟨κ, hκ, hκγ⟩ := hcover α (List.mem_append_right _ (hsub hα))
        obtain ⟨rfl, -⟩ | ⟨-, U, ℓ, rfl⟩ := mem_assumeDefined hκ
        · exact hκγ (List.mem_singleton_self _)
        · exact absurd rfl (allAtoms_ne_undefined_updateDefined T l T' δ hδ' _ hα U ℓ)
      refine (sat_updateCase_iff (m := m)).1
        ⟨δ, hδ, fun α hα ↦ (hor α (hδγ α hα)).resolve_right (not_not.2 fun v hv ↦ ?_)⟩ |>.1 hu
      have hsub := (allAtoms_updates_subset_updateCase defined T l T' δ hδ α hα).1 v hv
      refine ih v.size ?_ v rfl (hkept α (hδγ α hα) v hv)
      rcases hsub with h | h <;> have := Tree.size_le_of_mem_updates h <;>
        simp only [← hsize, TWE.Tree.size] <;> omega

end Cases

end ToWE

end Linear

end TWE

end Accordion

end
