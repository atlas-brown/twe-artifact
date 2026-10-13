module

public import Accordion.TWE.Linear.ToWE.Properties.Basic

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel

variable {Γ : Type} {V : TWE.Vars} [TWE.Vars.Comparable V]
  {rule : Atom Γ V → FreshM V (Guess (Conj Γ V))}

theorem allAtoms_rewritePass {P : Atom Γ V → Prop}
    (hrule : ∀ α U, P α → Guess.AllAtoms P ((rule α).run U).1) :
    ∀ (rest done : Conj Γ V), (∀ a ∈ done, P a) → (∀ a ∈ rest, P a) →
      (rewritePass rule done rest).AllAtoms P
  | [], _, hdone, _ => Guess.AllAtoms.conj hdone
  | α :: rest, done, hdone, hrest => Guess.AllAtoms.flatMap fun γ hγ ↦
      allAtoms_rewritePass hrule rest (done ++ γ)
        (fun a ha ↦ (List.mem_append.1 ha).elim (hdone a)
          (hrule α _ (hrest α List.mem_cons_self) γ hγ a))
        (fun a ha ↦ hrest a (List.mem_cons_of_mem _ ha))

theorem allAtoms_rank_le_rewritePass (f : Atom Γ V → Nat)
    (hrule : ∀ α U, Guess.AllAtoms (fun a ↦ f a = 0 ∨ f a < f α) ((rule α).run U).1) (M : Nat) :
    ∀ (rest done : Conj Γ V), (∀ a ∈ done, f a ≤ M - 1) → (∀ a ∈ rest, f a ≤ M) →
      (rewritePass rule done rest).AllAtoms (f · ≤ M - 1)
  | [], _, hdone, _ => Guess.AllAtoms.conj hdone
  | α :: rest, done, hdone, hrest => Guess.AllAtoms.flatMap fun γ hγ ↦
      allAtoms_rank_le_rewritePass f hrule M rest (done ++ γ)
        (fun a ha ↦ (List.mem_append.1 ha).elim (hdone a) fun ha ↦ by
          have := hrule α _ γ hγ a ha
          have := hrest α List.mem_cons_self
          omega)
        (fun a ha ↦ hrest a (List.mem_cons_of_mem _ ha))

theorem allAtoms_rewriteAtoms {P : Atom Γ V → Prop}
    (hrule : ∀ α U, P α → Guess.AllAtoms P ((rule α).run U).1) (β : Conj Γ V)
    (hβ : ∀ α ∈ β, P α) : (rewriteAtoms rule β).AllAtoms P :=
  Function.Iterate.rec (Guess.AllAtoms P) (Guess.AllAtoms.conj hβ) (fun _ hD ↦
    Guess.AllAtoms.flatMap fun γ hγ ↦ allAtoms_rewritePass hrule γ [] (by simp) (hD γ hγ)) _

private theorem le_sum_map {β : Type} (f : β → Nat) {xs : List β} {x : β} (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · have := ih hx
        simp only [List.map_cons, List.sum_cons]
        omega

theorem allAtoms_rank_eq_zero_rewriteAtoms (f : Atom Γ V → Nat)
    (hrule : ∀ α U, Guess.AllAtoms (fun a ↦ f a = 0 ∨ f a < f α) ((rule α).run U).1)
    (β : Conj Γ V) (hβ : ∀ α ∈ β, f α ≤ 2 * α.treeSize + 1) :
    (rewriteAtoms rule β).AllAtoms (f · = 0) := by
  have hpasses : ∀ k M (D : Guess (Conj Γ V)), D.AllAtoms (f · ≤ M) →
      Guess.AllAtoms (f · ≤ M - k) ((·.flatMap (rewritePass rule []))^[k] D) := by
    intro k
    induction k with
    | zero => exact fun _ _ h ↦ h
    | succ k ih =>
        intro M D hD
        refine (ih (M - 1) _ (Guess.AllAtoms.flatMap fun γ hγ ↦
          allAtoms_rank_le_rewritePass f hrule M γ [] (by simp) (hD γ hγ))).mono fun a h ↦ ?_
        omega
  refine (hpasses β.passes β.passes (pure β) (Guess.AllAtoms.conj fun α hα ↦ ?_)).mono fun a h ↦ ?_
  · exact (hβ α hα).trans (le_sum_map (fun α ↦ 2 * α.treeSize + 1) hα)
  · omega

variable [Ord Γ] [DecidableEq Γ] {cond : Atom Γ V → WordModel Γ V → Prop}

theorem rewritePass_sat_or
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (m : WordModel Γ V) :
    ∀ (rest done γ : Conj Γ V), γ ∈ rewritePass rule done rest →
      (∀ a ∈ γ, a.sat m ∨ ¬cond a m) → ∀ a ∈ done ++ rest, a.sat m ∨ ¬cond a m
  | [], done, γ, hγ, h => by simp_all [rewritePass]
  | α :: rest, done, γ, hγ, h => by
      obtain ⟨δ, hδ, hγ⟩ := Guess.mem_flatMap.1 hγ
      have ih := rewritePass_sat_or hrule hcond m rest (done ++ δ) γ hγ h
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact ih a (by simp [ha])
      rcases List.mem_cons.1 ha with rfl | ha
      · refine or_iff_not_imp_right.2 fun hc ↦ ?_
        have hc := not_not.1 hc
        have hδsat : Conj.sat m δ := fun b hb ↦
          (ih b (by simp [hb])).resolve_right (not_not.2 (hcond a _ m hc δ hδ b hb))
        have := (hrule a _ (Atom.free_subset_of_mem (by simp)) m hc).1
          (Guess.satFresh_of_sat ⟨δ, hδ, hδsat⟩)
        simpa using this
      · exact ih a (by simp [ha])

theorem rewriteAtoms_sat_or
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (β : Conj Γ V) (m : WordModel Γ V) :
    ∀ γ ∈ rewriteAtoms rule β, (∀ a ∈ γ, a.sat m ∨ ¬cond a m) →
      ∀ a ∈ β, a.sat m ∨ ¬cond a m :=
  Function.Iterate.rec (fun D ↦ ∀ γ ∈ D, (∀ a ∈ γ, a.sat m ∨ ¬cond a m) →
      ∀ a ∈ β, a.sat m ∨ ¬cond a m)
    (by simp) (fun D hD γ hγ h ↦ by
      obtain ⟨β', hβ', hγ⟩ := Guess.mem_flatMap.1 hγ
      exact hD β' hβ' (by
        simpa using rewritePass_sat_or hrule hcond m β' [] γ hγ h)) _

theorem ensures_of_mem_rewriteAtoms
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (β : Conj Γ V) (hβ : β.Ensures cond) :
    ∀ γ ∈ rewriteAtoms rule β, γ.Ensures cond := fun γ hγ m h ↦
  allAtoms_rewriteAtoms (fun α U ↦ hcond α U m) β
    (hβ m (rewriteAtoms_sat_or hrule hcond β m γ hγ h)) γ hγ

theorem rewritePass_sat
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (hcongr : ∀ α U m m', α.free ⊆ U → m ≡[U] m' → cond α m → cond α m') :
    ∀ (rest done : Conj Γ V) (m : WordModel Γ V), (∀ a ∈ done ++ rest, cond a m) →
      Conj.sat m (done ++ rest) →
      ∃ m' γ, γ ∈ rewritePass rule done rest ∧ Conj.sat m' γ ∧ ∀ a ∈ γ, cond a m'
  | [], done, m, hc, h => ⟨m, done, by simp [rewritePass], by simpa using h, by simpa using hc⟩
  | α :: rest, done, m, hc, h => by
      have hfree : ∀ a ∈ done ++ α :: rest, a.free ⊆ (done ++ α :: rest).free :=
        fun a ha ↦ Atom.free_subset_of_mem ha
      have hsat : Conj.sat m (done ++ rest) ∧ α.sat m := by
        simp only [Conj.sat_append, Conj.sat_cons] at h ⊢
        tauto
      obtain ⟨m', hm', δ, hδ, hδsat⟩ :=
        (hrule α _ (hfree α (by simp)) m (hc α (by simp))).2 (by simpa using hsat.2)
      have hc' : ∀ a ∈ done ++ α :: rest, cond a m' := fun a ha ↦
        hcongr a _ m m' (hfree a ha) hm' (hc a ha)
      have hrest : Conj.sat m' (done ++ rest) :=
        (Conj.sat_congr hm' fun a ha ↦ hfree a (by simp at ha ⊢; tauto)).1 hsat.1
      obtain ⟨m'', γ, hγ, hγsat, hγc⟩ := rewritePass_sat hrule hcond hcongr rest (done ++ δ) m'
        (fun a ha ↦ by
          simp only [List.mem_append] at ha
          rcases ha with (ha | ha) | ha
          · exact hc' a (by simp [ha])
          · exact hcond α _ m' (hc' α (by simp)) δ hδ a ha
          · exact hc' a (by simp [ha]))
        (by
          simp only [Conj.sat_append] at hrest ⊢
          exact ⟨⟨hrest.1, hδsat⟩, hrest.2⟩)
      exact ⟨m'', γ, Guess.mem_flatMap.2 ⟨δ, hδ, hγ⟩, hγsat, hγc⟩

theorem rewriteAtoms_sat
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (hcongr : ∀ α U m m', α.free ⊆ U → m ≡[U] m' → cond α m → cond α m')
    (β : Conj Γ V) (m : WordModel Γ V) (hβ : ∀ a ∈ β, cond a m)
    (h : Conj.sat m β) : ∃ m', Guess.sat m' (rewriteAtoms rule β) :=
  have ⟨m', γ, hγ, hsat, _⟩ := Function.Iterate.rec
    (fun D ↦ ∃ m' γ, γ ∈ D ∧ Conj.sat m' γ ∧ ∀ a ∈ γ, cond a m')
    ⟨m, β, by simp, h, hβ⟩
    (fun D ⟨m', γ, hγ, hsat, hc⟩ ↦ by
      obtain ⟨m'', γ', hγ', hsat', hc'⟩ := rewritePass_sat hrule hcond hcongr γ [] m'
        (by simpa using hc) (by simpa using hsat)
      exact ⟨m'', γ', Guess.mem_flatMap.2 ⟨γ, hγ, hγ'⟩, hsat', hc'⟩) β.passes
  ⟨m', γ, hγ, hsat⟩

theorem rewriteAtoms_equisat_of_ensures
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn (cond α) U [α] ((rule α).run U).1)
    (hcond : ∀ α U m, cond α m → Guess.AllAtoms (cond · m) ((rule α).run U).1)
    (hcongr : ∀ α U m m', α.free ⊆ U → m ≡[U] m' → cond α m → cond α m')
    (β : Conj Γ V) (hβ : β.Ensures cond) :
    (rewriteAtoms rule β).SAT ↔ β.SAT := by
  constructor
  · rintro ⟨m, γ, hγ, h⟩
    have hor := rewriteAtoms_sat_or hrule hcond β m γ hγ fun a ha ↦ .inl (h a ha)
    exact ⟨m, fun a ha ↦ (hor a ha).resolve_right (not_not.2 (hβ m hor a ha))⟩
  · rintro ⟨m, h⟩
    exact rewriteAtoms_sat hrule hcond hcongr β m (hβ m fun a ha ↦ .inl (h a ha)) h

theorem rewriteAtoms_equisat
    (hrule : ∀ α U, α.free ⊆ U → SatPreserving U [α] ((rule α).run U).1)
    (β : Conj Γ V) : (rewriteAtoms rule β).SAT ↔ β.SAT :=
  rewriteAtoms_equisat_of_ensures (cond := fun _ _ ↦ True)
    (fun α U hα ↦ (hrule α U hα).satPreservingIn _)
    (fun _ _ _ _ _ _ _ _ ↦ trivial) (fun _ _ _ _ _ _ _ ↦ trivial) β fun _ _ _ _ ↦ trivial

theorem flatMap_rewriteAtoms_equisat_of_updatesDefined
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn α.DefinedIn U [α] ((rule α).run U).1)
    (hupdates : ∀ α U, ((rule α).run U).1.AllAtoms (·.updates ⊆ α.updates))
    (D : Guess (Conj Γ V)) (hD : D.UpdatesDefined) :
    Guess.SAT (D.flatMap (rewriteAtoms rule)) ↔ Guess.SAT D :=
  Guess.flatMap_equisat fun β hβ ↦ rewriteAtoms_equisat_of_ensures hrule
    (fun α U _ h ↦ (hupdates α U).mono fun _ ha u hu ↦ h u (ha hu))
    (fun _ _ _ _ hα h hc ↦ (Atom.definedIn_congr h hα).1 hc) β (hD β hβ)

theorem updatesDefined_flatMap_rewriteAtoms
    (hrule : ∀ α U, α.free ⊆ U → SatPreservingIn α.DefinedIn U [α] ((rule α).run U).1)
    (hupdates : ∀ α U, ((rule α).run U).1.AllAtoms (·.updates ⊆ α.updates))
    (D : Guess (Conj Γ V)) (hD : D.UpdatesDefined) :
    Guess.UpdatesDefined (D.flatMap (rewriteAtoms rule)) :=
  Guess.updatesDefined_flatMap fun β hβ ↦ ensures_of_mem_rewriteAtoms hrule
    (fun α U _ h ↦ (hupdates α U).mono fun _ ha u hu ↦ h u (ha hu)) β (hD β hβ)

end ToWE

end Linear

end TWE

end Accordion

end
