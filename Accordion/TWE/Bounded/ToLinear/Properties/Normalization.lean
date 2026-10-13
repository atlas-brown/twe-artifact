module

public import Accordion.TWE.Bounded.ToLinear.Properties.Walks

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open scoped Accordion.Formula Linear.ToWE.WordModel
open Linear.ToWE (WordModel WordModel.evalPath)

variable {Γ : Type} {V : TWE.Vars}

section Run

variable {α β : Type}

@[simp] theorem FreshDefM.run_pure (a : α) (s : FreshState Γ V) :
    (pure a : FreshDefM Γ V α).run s = (a, s) := rfl

@[simp] theorem FreshDefM.run_bind (x : FreshDefM Γ V α) (f : α → FreshDefM Γ V β)
    (s : FreshState Γ V) : (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

@[simp] theorem FreshDefM.run_map (f : α → β) (x : FreshDefM Γ V α) (s : FreshState Γ V) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := rfl

@[simp] theorem run_define (F : TWE.Formula Γ V) (s : FreshState Γ V) :
    (define F).run s = ((), ⟨s.used, s.definitions ++ [F]⟩) := rfl

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

@[simp] theorem run_freshLoc (s : FreshState Γ V) :
    (freshLoc : FreshDefM Γ V _).run s = (Fresh.fresh s.used.loc,
      ⟨{ s.used with loc := insert (Fresh.fresh s.used.loc) s.used.loc }, s.definitions⟩) := rfl

@[simp] theorem run_freshPath (s : FreshState Γ V) :
    (freshPath : FreshDefM Γ V _).run s = (Fresh.fresh s.used.path,
      ⟨{ s.used with path := insert (Fresh.fresh s.used.path) s.used.path }, s.definitions⟩) :=
  rfl

@[simp] theorem run_freshName (s : FreshState Γ V) :
    (freshName : FreshDefM Γ V _).run s = (Fresh.fresh s.used.name,
      ⟨{ s.used with name := insert (Fresh.fresh s.used.name) s.used.name }, s.definitions⟩) :=
  rfl

end Run

section Models

variable [Ord Γ]

theorem ReadsOn.mono {α : Sort _} {U U' : TWE.Free V} {g : WordModel Γ V → α}
    (h : ReadsOn U g) (le : U ⊆ U') : ReadsOn U' g :=
  fun M M' e ↦ h M M' (e.mono le)

variable [DecidableEq Γ]

theorem FreshState.Extends.refl (s : FreshState Γ V) : FreshState.Extends s s :=
  ⟨Free.Subset.refl _, List.Subset.refl _, id, fun _ M h ↦ ⟨M, .refl M _, h⟩⟩

theorem FreshState.Extends.trans {s s' s'' : FreshState Γ V} (h : FreshState.Extends s s')
    (h' : FreshState.Extends s' s'') :
    FreshState.Extends s s'' where
  used_subset := Free.Subset.trans h.used_subset h'.used_subset
  subset := List.Subset.trans h.subset h'.subset
  valid v := h'.valid (h.valid v)
  complete v M hM := by
    obtain ⟨M₁, e₁, h₁⟩ := h.complete v M hM
    obtain ⟨M₂, e₂, h₂⟩ := h'.complete (h.valid v) M₁ h₁
    exact ⟨M₂, e₁.trans (e₂.mono h.used_subset), h₂⟩

theorem FreshState.Holds.of_subset {M : WordModel Γ V} {s s' : FreshState Γ V}
    (h : FreshState.Holds M s')
    (sub : s.definitions ⊆ s'.definitions) : FreshState.Holds M s :=
  fun F hF ↦ h F (sub hF)

theorem FreshState.Extends.exists_model {U : TWE.Free V} {s : FreshState Γ V}
    (h : FreshState.Extends ⟨U, []⟩ s)
    (M : WordModel Γ V) : ∃ M', M ≡[U] M' ∧ FreshState.Holds M' s :=
  h.complete (by simp [FreshState.Valid]) M (by simp [FreshState.Holds])

theorem extends_define {s : FreshState Γ V} {U : TWE.Free V} {Fs : List (TWE.Formula Γ V)}
    (le : s.used ⊆ U) (reads : ∀ F ∈ Fs, ReadsOn U (·.toTWE ⊨ F))
    (solve : ∀ M : WordModel Γ V, ∃ M', M ≡[s.used] M' ∧ ∀ F ∈ Fs, M'.toTWE ⊨ F) :
    FreshState.Extends s ⟨U, s.definitions ++ Fs⟩ where
  used_subset := le
  subset := List.subset_append_left _ _
  valid v F hF := (List.mem_append.1 hF).elim (fun h ↦ (v F h).mono le) (reads F)
  complete v M hM := by
    obtain ⟨M', e, hs⟩ := solve M
    exact ⟨M', e, fun F hF ↦
      (List.mem_append.1 hF).elim (fun h ↦ (v F h M M' e).mp (hM F h)) (hs F)⟩

end Models

section Equations

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem run_normalize (d : Decomposition Γ V) (s : FreshState Γ V) :
    (normalize d).run s =
      (normalize.go (Fresh.fresh s.used.loc) d.rest).run
        ⟨{ s.used with loc := insert (Fresh.fresh s.used.loc) s.used.loc }, s.definitions ++
          [(.loc (Fresh.fresh s.used.loc) : TWE.Path Γ V) ≐ d.first]⟩ := rfl

theorem run_normalize_go_cons (Y : V.Loc) (C : Step) (B : TWE.Path Γ V)
    (rest : List (Step × TWE.Path Γ V)) (s : FreshState Γ V) :
    (normalize.go Y ((C, B) :: rest)).run s =
      let Z := Fresh.fresh s.used.path
      let A := Fresh.fresh s.used.name
      let Y' := Fresh.fresh s.used.loc
      let r := (normalize.go Y' rest).run
        ⟨⟨insert A s.used.name, s.used.comp, insert Z s.used.path, insert Y' s.used.loc,
            s.used.set, s.used.tree⟩,
          s.definitions ++
            [stepEquation C Y Z A, (.loc Y' : TWE.Path Γ V) ≐ .var Z ++ B]⟩
      (⟨Y :: r.1.prefixes, r.1.last⟩, r.2) := by
  simp only [normalize.go, FreshDefM.run_bind, run_freshPath, run_freshName,
    run_freshLoc, run_define, FreshDefM.run_pure, List.append_assoc, List.cons_append,
    List.nil_append]

theorem definitions_subset_normalize_go (Y : V.Loc) (rest : List (Step × TWE.Path Γ V))
    (s : FreshState Γ V) :
    s.definitions ⊆ ((normalize.go Y rest).run s).2.definitions := by
  induction rest generalizing Y s with
  | nil => exact List.Subset.refl _
  | cons p rest ih =>
      rw [run_normalize_go_cons]
      dsimp only
      exact List.Subset.trans (List.subset_append_left _ _) (ih _ ⟨_, _⟩)

theorem definitions_subset_normalize (d : Decomposition Γ V) (s : FreshState Γ V) :
    s.definitions ⊆ ((normalize d).run s).2.definitions := by
  rw [run_normalize]
  exact List.Subset.trans (List.subset_append_left _ _) (definitions_subset_normalize_go _ _ ⟨_, _⟩)

end Equations

section Sound

variable [Ord Γ] [DecidableEq Γ] (M : WordModel Γ V)

theorem sat_stepEquation {C : Step} {Y : V.Loc} {Z : V.Path} {A : V.Name}
    (h : M.toTWE ⊨ (stepEquation C Y Z A : TWE.Formula Γ V)) :
    M.σPath Z = C.apply (M.σLoc Y) := by
  cases C with
  | empty | self => exact (satAtom_pathEq M rfl rfl).1 h
  | parent =>
      simp only [stepEquation, Formula.sat, TWE.Model.sat_iff_satAtom] at h
      rcases h with ⟨hY, hZ⟩ | h
      · have hY := (satAtom_pathEq M rfl rfl).1 hY
        have hZ := (satAtom_pathEq M rfl rfl).1 hZ
        simp_all [WordModel.evalPath, Step.apply]
      · have h := (satAtom_pathEq M rfl rfl).1 h
        simp_all [WordModel.evalPath, Step.apply]

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem normalize_go_sound (Y : V.Loc) (rest : List (Step × TWE.Path Γ V))
    (hrest : ∀ p ∈ rest, p.2.hasLinearConstants) (s : FreshState Γ V)
    (h : FreshState.Holds M ((normalize.go Y rest).run s).2) :
    let r := ((normalize.go Y rest).run s).1
    let rw := rest.map fun p ↦ (p.1, WordModel.evalPath M p.2)
    r.prefixes.map M.σLoc = prefixWords (M.σLoc Y) rw ∧
      M.σLoc r.last = normalWord (M.σLoc Y) rw := by
  induction rest generalizing Y s with
  | nil => simp [prefixWords, normalWord, normalize.go]
  | cons p rest ih =>
      obtain ⟨C, B⟩ := p
      rw [run_normalize_go_cons] at h ⊢
      dsimp only at h ⊢
      have hB : B.hasLinearConstants := hrest _ List.mem_cons_self
      have hs : ∀ F ∈ [_, _], M.toTWE ⊨ F :=
        fun F hF ↦ h F (definitions_subset_normalize_go _ _ _ (List.mem_append_right _ hF))
      have hZ := sat_stepEquation M (hs _ List.mem_cons_self)
      have hY' : M.σLoc (Fresh.fresh s.used.loc) =
          M.σPath (Fresh.fresh s.used.path) ++ WordModel.evalPath M B :=
        (satAtom_pathEq M rfl (by simp [hB])).1 (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))
      obtain ⟨ih₁, ih₂⟩ := ih _ (fun p hp ↦ hrest p (List.mem_cons_of_mem _ hp)) _ h
      simp only [List.map_cons, ih₁, ih₂]
      simp [prefixWords, normalWord, hY', hZ]

theorem normalize_sound (d : Decomposition Γ V) (hd : d.HasLinearConstants) (s : FreshState Γ V)
    (h : FreshState.Holds M ((normalize d).run s).2) :
    let r := ((normalize d).run s).1
    r.prefixes.map M.σLoc = prefixWords (WordModel.evalPath M d.first) (d.restWords M) ∧
      M.σLoc r.last = normalWord (WordModel.evalPath M d.first) (d.restWords M) := by
  rw [run_normalize] at h ⊢
  have hY : M.σLoc (Fresh.fresh s.used.loc) = WordModel.evalPath M d.first :=
    (satAtom_pathEq M rfl hd.1).1
      (h _ (definitions_subset_normalize_go _ _ _
        (List.mem_append_right _ (List.mem_singleton_self _))))
  simpa [hY, Decomposition.restWords] using normalize_go_sound M _ _ hd.2 _ h

end Sound

section Complete

variable [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem extends_normalize_go (Y : V.Loc) (rest : List (Step × TWE.Path Γ V))
    (hlin : ∀ p ∈ rest, p.2.hasLinearConstants) (s : FreshState Γ V)
    (hY : ReadsOn (Γ := Γ) s.used (·.σLoc Y))
    (hrest : ReadsOn s.used fun M ↦ rest.map fun p ↦ (p.1, WordModel.evalPath M p.2)) :
    let r := (normalize.go Y rest).run s
    FreshState.Extends s r.2 ∧ ReadsOn (Γ := Γ) r.2.used (·.σLoc r.1.last) := by
  induction rest generalizing Y s with
  | nil => exact ⟨FreshState.Extends.refl s, hY⟩
  | cons p rest ih =>
      obtain ⟨C, B⟩ := p
      have hlinB : B.hasLinearConstants := hlin _ List.mem_cons_self
      rw [run_normalize_go_cons]
      dsimp only
      have hB : ReadsOn s.used (WordModel.evalPath · B) :=
        fun M M' e ↦ congrArg Prod.snd (List.cons.inj (hrest M M' e)).1
      have hrest' : ReadsOn s.used fun M ↦ rest.map fun p ↦ (p.1, WordModel.evalPath M p.2) :=
        fun M M' e ↦ (List.cons.inj (hrest M M' e)).2
      have le : s.used ⊆ ⟨insert (Fresh.fresh s.used.name) s.used.name, s.used.comp,
          insert (Fresh.fresh s.used.path) s.used.path,
          insert (Fresh.fresh s.used.loc) s.used.loc, s.used.set, s.used.tree⟩ :=
        ⟨Finset.subset_insert _ _, subset_rfl, Finset.subset_insert _ _,
          Finset.subset_insert _ _, subset_rfl, subset_rfl⟩
      obtain ⟨e, last⟩ := ih (Fresh.fresh s.used.loc)
        (fun p hp ↦ hlin p (List.mem_cons_of_mem _ hp)) ⟨_, _⟩
        (fun M M' e ↦ e.2.2.2.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _)))
        (hrest'.mono le)
      refine ⟨FreshState.Extends.trans (extends_define le ?_ ?_) e, last⟩
      · intro F hF M M' e
        have hY := hY M M' (e.mono le)
        have hB := hB M M' (e.mono le)
        have hZ : M.σPath (Fresh.fresh s.used.path) = M'.σPath (Fresh.fresh s.used.path) :=
          e.2.2.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        have hA : M.σName (Fresh.fresh s.used.name) = M'.σName (Fresh.fresh s.used.name) :=
          e.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        have hY' : M.σLoc (Fresh.fresh s.used.loc) = M'.σLoc (Fresh.fresh s.used.loc) :=
          e.2.2.2.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | rfl <;> cases C <;>
          simp [stepEquation, WordModel.evalPath, hY, hB, hZ, hA, hY', hlinB,
            Path.hasLinearConstants.eq_def]
      · intro M
        let y := M.σLoc Y
        let b := WordModel.evalPath M B
        let M' := ((M.setName (Fresh.fresh s.used.name)
            (y.getLast?.getD (M.σName (Fresh.fresh s.used.name)))).setPath
          (Fresh.fresh s.used.path) (C.apply y)).setLoc (Fresh.fresh s.used.loc) (C.apply y ++ b)
        have e : M ≡[s.used] M' :=
          ((WordModel.congr_setName (Fresh.fresh_notMem _)).trans
            (WordModel.congr_setPath (Fresh.fresh_notMem _))).trans
            (WordModel.congr_setLoc (Fresh.fresh_notMem _))
        have hY : M'.σLoc Y = y := (hY M M' e).symm
        have hB : WordModel.evalPath M' B = b := (hB M M' e).symm
        have hZ : M'.σPath (Fresh.fresh s.used.path) = C.apply y := ite_eq_left rfl
        have hA : M'.σName (Fresh.fresh s.used.name) =
            y.getLast?.getD (M.σName (Fresh.fresh s.used.name)) := ite_eq_left rfl
        have hY' : M'.σLoc (Fresh.fresh s.used.loc) = C.apply y ++ b := ite_eq_left rfl
        refine ⟨M', e, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        cases C <;>
          simp [stepEquation, WordModel.evalPath, hY, hB, hZ, hA, hY', Step.apply, hlinB,
            Path.hasLinearConstants.eq_def]
        rcases List.eq_nil_or_concat y with h | ⟨l, a, h⟩ <;> simp [h]

theorem extends_normalize (d : Decomposition Γ V) (hlin : d.HasLinearConstants) (s : FreshState Γ V)
    (hd : ReadsOn s.used (Decomposition.eval · d)) :
    let r := (normalize d).run s
    FreshState.Extends s r.2 ∧ ReadsOn (Γ := Γ) r.2.used (·.σLoc r.1.last) := by
  have words := fun M M' e ↦ blocksPath_eq_blocksPath_iff.1 (hd M M' e)
  rw [run_normalize]
  have le : s.used ⊆ { s.used with loc := insert (Fresh.fresh s.used.loc) s.used.loc } :=
    ⟨subset_rfl, subset_rfl, subset_rfl, Finset.subset_insert _ _, subset_rfl, subset_rfl⟩
  obtain ⟨e, last⟩ := extends_normalize_go (Fresh.fresh s.used.loc) d.rest hlin.2 ⟨_, _⟩
    (fun M M' e ↦ e.2.2.2.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _)))
    (ReadsOn.mono (fun M M' e ↦ (words M M' e).2) le)
  refine ⟨FreshState.Extends.trans (extends_define le ?_ ?_) e, last⟩
  · intro F hF M M' e
    simp only [List.mem_singleton] at hF
    subst hF
    have hY : M.σLoc (Fresh.fresh s.used.loc) = M'.σLoc (Fresh.fresh s.used.loc) :=
      e.2.2.2.1 (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    simp [WordModel.evalPath, hY, (words M M' (e.mono le)).1, hlin.1,
      Path.hasLinearConstants.eq_def]
  · intro M
    have e : M ≡[s.used] M.setLoc (Fresh.fresh s.used.loc) (WordModel.evalPath M d.first) :=
      WordModel.congr_setLoc (Fresh.fresh_notMem _)
    refine ⟨_, e, ?_⟩
    simp [WordModel.evalPath, ← (words M _ e).1, hlin.1, Path.hasLinearConstants.eq_def]

end Complete

end ToLinear

end Bounded

end TWE

end Accordion

end
