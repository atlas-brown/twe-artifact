module

public import Accordion.TWE.Bounded.ToLinear.Properties.Normalization

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open scoped Accordion.Formula Linear.ToWE.BigConnectives Linear.ToWE.WordModel
open Linear.ToWE (WordModel WordModel.evalPath WordModel.evalPath_congr sat_all sat_any)

variable {Γ : Type} {V : TWE.Vars}

theorem hasLinearConstants_appendToLast :
    ∀ (rest : List (Step × TWE.Path Γ V)) (suffix : TWE.Path Γ V),
      (∀ p ∈ rest, p.2.hasLinearConstants) → suffix.hasLinearConstants →
      ∀ p ∈ Decomposition.appendToLast rest suffix, p.2.hasLinearConstants
  | [], _, _, _ => by simp [Decomposition.appendToLast]
  | [(step, block)], suffix, hr, hs => by
      simp_all [Decomposition.appendToLast]
  | pair :: next :: rest, suffix, hr, hs => by
      intro p hp
      rw [Decomposition.appendToLast, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hr _ List.mem_cons_self
      · exact hasLinearConstants_appendToLast (next :: rest) suffix
          (fun q hq ↦ hr q (List.mem_cons_of_mem _ hq)) hs p hp

theorem Decomposition.HasLinearConstants.append {d d' : Decomposition Γ V}
    (h : d.HasLinearConstants) (h' : d'.HasLinearConstants) :
    (d.append d').HasLinearConstants := by
  unfold Decomposition.append
  split
  · exact ⟨by simp [h.1, h'.1], h'.2⟩
  · refine ⟨h.1, fun p hp ↦ ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact hasLinearConstants_appendToLast _ _ h.2 h'.1 p hp
    · exact h'.2 p hp

theorem Decomposition.HasLinearConstants.blocks {d : Decomposition Γ V} (h : d.HasLinearConstants) :
    ∀ B ∈ d.blocks, B.hasLinearConstants := by
  intro B hB
  simp only [Decomposition.blocks, List.mem_cons, List.mem_map] at hB
  rcases hB with rfl | ⟨p, hp, rfl⟩
  exacts [h.1, h.2 p hp]

section Decompose

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (δ : VariableDecomposition V)

theorem hasLinearConstants_decomposePath (P : TWE.Path Γ V) (s : FreshState Γ V) :
    ((decomposePath δ P).run s).1.HasLinearConstants := by
  induction P generalizing s with
  | nil | loc =>
      simp [decomposePath, Decomposition.HasLinearConstants, Decomposition.nil,
        Decomposition.linear]
  | init C =>
      cases C with
      | var x =>
          cases hx : δ.component x <;>
            simp [decomposePath, hx, Decomposition.HasLinearConstants, Decomposition.linear,
              Decomposition.step]
      | name A => simp [decomposePath, Decomposition.HasLinearConstants, Decomposition.linear]
      | _ => simp [decomposePath, Decomposition.HasLinearConstants, Decomposition.step]
  | var X =>
      refine ⟨rfl, fun p hp ↦ ?_⟩
      simp only [decomposePath, FreshDefM.run_pure, Decomposition.var, List.mem_map] at hp
      obtain ⟨q, -, rfl⟩ := hp
      rfl
  | join P Q ihP ihQ =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure]
      exact (ihP s).append (ihQ _)
  | norm P ih => simp [decomposePath, Decomposition.HasLinearConstants, Decomposition.linear]

theorem definitions_subset_decomposePath (P : TWE.Path Γ V) (s : FreshState Γ V) :
    s.definitions ⊆ ((decomposePath δ P).run s).2.definitions := by
  induction P generalizing s with
  | init C => cases C <;> exact List.Subset.refl _
  | join P Q ihP ihQ =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure]
      exact List.Subset.trans (ihP s) (ihQ _)
  | norm P ih =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure]
      exact List.Subset.trans (ih s) (definitions_subset_normalize _ _)
  | _ => exact List.Subset.refl _

variable [Ord Γ] [DecidableEq Γ]

theorem extends_decomposePath (P : TWE.Path Γ V) (s : FreshState Γ V) (hP : P.free ⊆ s.used)
    (hδ : δ.free ⊆ s.used) :
    let r := (decomposePath δ P).run s
    FreshState.Extends s r.2 ∧ ReadsOn r.2.used (Decomposition.eval · r.1) := by
  have linear : ∀ (U : TWE.Free V) (Q : TWE.Path Γ V), Q.free ⊆ U →
      ReadsOn U (Decomposition.eval · (.linear Q)) :=
    fun U Q hQ M M' e ↦ congrArg (blocksPath · []) (WordModel.evalPath_congr e hQ)
  induction P generalizing s with
  | nil => exact ⟨FreshState.Extends.refl s, fun _ _ _ ↦ rfl⟩
  | loc ℓ => exact ⟨FreshState.Extends.refl s, linear _ _ hP⟩
  | init C =>
      cases C with
      | var x =>
          cases hx : δ.component x <;> simp only [decomposePath, hx, FreshDefM.run_pure]
          · exact ⟨FreshState.Extends.refl s, linear _ _ hP⟩
          all_goals exact ⟨FreshState.Extends.refl s, fun _ _ _ ↦ rfl⟩
      | name A => exact ⟨FreshState.Extends.refl s, linear _ _ hP⟩
      | _ => exact ⟨FreshState.Extends.refl s, fun _ _ _ ↦ rfl⟩
  | var X =>
      refine ⟨FreshState.Extends.refl s, fun M M' e ↦ ?_⟩
      simp only [decomposePath, FreshDefM.run_pure, Decomposition.eval_var]
      exact (eqOn_sourceModel δ e hP hδ).2.2.1 (Finset.mem_coe.2 (Finset.mem_singleton_self X))
  | join P Q ihP ihQ =>
      obtain ⟨eP, hP'⟩ := ihP s (Free.union_subset hP).1 hδ
      obtain ⟨eQ, hQ'⟩ := ihQ ((decomposePath δ P).run s).2
        (Free.Subset.trans (Free.union_subset hP).2 eP.used_subset)
        (Free.Subset.trans hδ eP.used_subset)
      refine ⟨eP.trans eQ, fun M M' e ↦ ?_⟩
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure,
        Decomposition.eval_append]
      exact congrArg₂ (· ++ ·) (hP'.mono eQ.used_subset M M' e) (hQ' M M' e)
  | norm P ih =>
      obtain ⟨eP, hP'⟩ := ih s hP hδ
      obtain ⟨eN, hN⟩ := extends_normalize _ (hasLinearConstants_decomposePath δ P s) _ hP'
      refine ⟨eP.trans eN, fun M M' e ↦ ?_⟩
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure, Decomposition.eval,
        Decomposition.linear, Decomposition.restWords, WordModel.evalPath]
      exact congrArg (blocksPath · List.nil) (hN M M' e)

theorem decomposePath_sound (P : TWE.Path Γ V) (s : FreshState Γ V) (M : WordModel Γ V)
    (h : FreshState.Holds M ((decomposePath δ P).run s).2) :
    ((decomposePath δ P).run s).1.eval M = (sourceModel δ M).evalPath P := by
  induction P generalizing s with
  | nil | loc => rfl
  | init C =>
      cases C with
      | name A => cases A <;> rfl
      | var x =>
          cases hx : δ.component x <;>
            simp [decomposePath, sourceModel, hx, TWE.Model.evalPath, TWE.Model.evalComponent] <;>
            rfl
      | _ => rfl
  | var X => exact Decomposition.eval_var δ M X
  | join P Q ihP ihQ =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢
      rw [Decomposition.eval_append, ihP s (h.of_subset (definitions_subset_decomposePath δ Q _)),
        ihQ _ h]
      rfl
  | norm P ih =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢
      have hP := ih s (h.of_subset (definitions_subset_normalize _ _))
      rw [TWE.Model.evalPath, ← hP, Decomposition.eval, Decomposition.eval, norm_blocksPath,
        ← (normalize_sound M _ (hasLinearConstants_decomposePath δ P s) _ h).2]
      rfl

theorem length_rest_decomposePath (P : TWE.Path Γ V) {U : TWE.Free V} (hP : P.free ⊆ U)
    (hδ : δ.free ⊆ U) (M : WordModel Γ V) :
    ((decomposePath δ P).start U).1.rest.length =
      ((sourceModel δ M).evalPath P).nonlinearCount := by
  obtain ⟨M', e, h⟩ := (extends_decomposePath δ P ⟨U, []⟩ hP hδ).1.exists_model M
  rw [TWE.Model.evalPath_congr (eqOn_sourceModel δ e hP hδ) (Free.Subset.refl _),
    ← decomposePath_sound δ P _ _ h, Decomposition.eval, nonlinearCount_blocksPath]
  simp [Decomposition.restWords, FreshDefM.start]

end Decompose

theorem sat_blockEquations [Ord Γ] [DecidableEq Γ] (M : WordModel Γ V)
    {bs bs' : List (TWE.Path Γ V)} (h : ∀ B ∈ bs, B.hasLinearConstants)
    (h' : ∀ B ∈ bs', B.hasLinearConstants) :
    (M.toTWE ⊨ (⋀ B ∈ bs.zip bs', B.1 ≐ B.2 : TWE.Formula Γ V) ↔
      ∀ B ∈ bs.zip bs', WordModel.evalPath M B.1 = WordModel.evalPath M B.2) ∧
    (M.toTWE ⊨ (⋁ B ∈ bs.zip bs', ∼(B.1 ≐ B.2) : TWE.Formula Γ V) ↔
      ∃ B ∈ bs.zip bs', WordModel.evalPath M B.1 ≠ WordModel.evalPath M B.2) := by
  have hB : ∀ B ∈ bs.zip bs',
      (M.toTWE.satAtom (.pathEq B.1 B.2) ↔ WordModel.evalPath M B.1 = WordModel.evalPath M B.2) :=
    fun B hB ↦ satAtom_pathEq M (h _ (List.of_mem_zip hB).1) (h' _ (List.of_mem_zip hB).2)
  refine ⟨?_, ?_⟩
  · rw [sat_all]
    exact forall₂_congr hB
  · rw [sat_any]
    exact exists_congr fun B ↦ and_congr_right fun hb ↦ not_congr (hB B hb)

section Translate

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (δ : VariableDecomposition V)

theorem definitions_subset_translate (b : Bool) (φ : TWE.Formula Γ V) (s : FreshState Γ V) :
    s.definitions ⊆ ((translate δ b φ).run s).2.definitions := by
  induction φ generalizing b s with
  | top | bot => cases b <;> exact List.Subset.refl _
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      cases b <;> exact List.Subset.trans (ihφ _ s) (ihψ _ _)
  | neg φ ih => cases b <;> exact ih _ s
  | atom a =>
      cases a with
      | pathEq P Q =>
          cases b <;> exact List.Subset.trans (definitions_subset_decomposePath δ P s)
            (definitions_subset_decomposePath δ Q _)
      | pathIsLin P => cases b <;> exact definitions_subset_decomposePath δ P s
      | treeWalk P T ℓ =>
          cases b <;> exact List.Subset.trans (definitions_subset_decomposePath δ P s)
            (definitions_subset_normalize _ _)
      | _ => cases b <;> exact List.Subset.refl _

variable [Ord Γ] [DecidableEq Γ]

theorem extends_translate (b : Bool) (φ : TWE.Formula Γ V) (s : FreshState Γ V)
    (hφ : φ.free ⊆ s.used) (hδ : δ.free ⊆ s.used) :
    FreshState.Extends s ((translate δ b φ).run s).2 := by
  induction φ generalizing b s with
  | top | bot => cases b <;> exact FreshState.Extends.refl s
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      have e := fun b ↦ ihφ b s (Free.union_subset hφ).1 hδ
      cases b <;>
        exact (e _).trans (ihψ _ _ (Free.Subset.trans (Free.union_subset hφ).2 (e _).used_subset)
          (Free.Subset.trans hδ (e _).used_subset))
  | neg φ ih => cases b <;> exact ih _ s hφ hδ
  | atom a =>
      cases a with
      | pathEq P Q =>
          have e := (extends_decomposePath δ P s (Free.union_subset hφ).1 hδ).1
          cases b <;> exact e.trans (extends_decomposePath δ Q _
            (Free.Subset.trans (Free.union_subset hφ).2 e.used_subset)
            (Free.Subset.trans hδ e.used_subset)).1
      | pathIsLin P => cases b <;> exact (extends_decomposePath δ P s hφ hδ).1
      | treeWalk P T ℓ =>
          have e := extends_decomposePath δ P s
            (Free.union_subset (Free.union_subset hφ).1).2 hδ
          cases b <;> exact e.1.trans
            (extends_normalize _ (hasLinearConstants_decomposePath δ P s) _ e.2).1
      | _ => cases b <;> exact FreshState.Extends.refl s

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem translate_sound (b : Bool) (φ : TWE.Formula Γ V) (s : FreshState Γ V)
    (M : WordModel Γ V) (h : FreshState.Holds M ((translate δ b φ).run s).2) :
    M.toTWE ⊨ ((translate δ b φ).run s).1 ↔ ((sourceModel δ M ⊨ φ) ↔ b) := by
  induction φ generalizing b s with
  | top | bot => cases b <;> simp [translate]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢ <;>
        simp [ihφ _ s (h.of_subset (definitions_subset_translate δ _ ψ _)), ihψ _ _ h,
          imp_iff_not_or]
  | neg φ ih =>
      cases b <;> simp only [translate, Bool.not_false, Bool.not_true] at h ⊢ <;> simp [ih _ s h]
  | atom a =>
      cases a with
      | pathEq P Q =>
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢
          all_goals
            have hP := decomposePath_sound δ P s M
              (h.of_subset (definitions_subset_decomposePath δ Q _))
            have hQ := decomposePath_sound δ Q _ M h
            have hlin := sat_blockEquations M (hasLinearConstants_decomposePath δ P s).blocks
              (hasLinearConstants_decomposePath δ Q ((decomposePath δ P).run s).2).blocks
            simp only [Accordion.Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom, ← hP,
              ← hQ, Decomposition.eval_eq_iff]
            split_ifs <;> simp_all
      | pathIsLin P =>
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢
          all_goals
            simp only [Accordion.Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom,
              ← decomposePath_sound δ P s M h, Accordion.Path.linear_iff_nonlinearCount_eq_zero,
              Decomposition.eval, nonlinearCount_blocksPath, Decomposition.restWords,
              List.length_map]
            split_ifs <;> simp_all
      | treeWalk P T ℓ =>
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] at h ⊢
          all_goals
            have hP := decomposePath_sound δ P s M (h.of_subset (definitions_subset_normalize _ _))
            obtain ⟨hYs, hY⟩ := normalize_sound M _ (hasLinearConstants_decomposePath δ P s) _ h
            have walk := sat_treeWalk_sourceModel_iff δ M hP.symm T ℓ hYs hY
            simp only [sat_all, sat_any, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom,
              ← walk]
            simp [imp_iff_not_or]
      | _ =>
          cases b <;> simp [translate, TWE.Model.satAtom, evalTree_sourceModel,
            evalNameSet_sourceModel, evalName_sourceModel]

end Translate

section LinearConstants

theorem FreshState.HasLinearConstants.append {s : FreshState Γ V} (hs : s.HasLinearConstants)
    {Fs : List (TWE.Formula Γ V)} (hFs : ∀ F ∈ Fs, F.hasLinearConstants) :
    FreshState.HasLinearConstants { s with definitions := s.definitions ++ Fs } := fun F hF ↦
  (List.mem_append.1 hF).elim (hs F) (hFs F)

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem hasLinearConstants_normalize_go (Y : V.Loc) (rest : List (Step × TWE.Path Γ V))
    (hlin : ∀ p ∈ rest, p.2.hasLinearConstants) (s : FreshState Γ V) (hs : s.HasLinearConstants) :
    FreshState.HasLinearConstants ((normalize.go Y rest).run s).2 := by
  induction rest generalizing Y s with
  | nil => exact hs
  | cons p rest ih =>
      obtain ⟨C, B⟩ := p
      have hB : B.hasLinearConstants := hlin _ List.mem_cons_self
      rw [run_normalize_go_cons]
      refine ih _ (fun p hp ↦ hlin p (List.mem_cons_of_mem _ hp)) _
        (FreshState.HasLinearConstants.append (s := ⟨_, s.definitions⟩) hs ?_)
      cases C <;> simp [stepEquation, hB]

theorem hasLinearConstants_normalize (d : Decomposition Γ V) (hd : d.HasLinearConstants)
    (s : FreshState Γ V) (hs : s.HasLinearConstants) :
    FreshState.HasLinearConstants ((normalize d).run s).2 := by
  rw [run_normalize]
  exact hasLinearConstants_normalize_go _ _ hd.2 _
    (FreshState.HasLinearConstants.append (s := ⟨_, s.definitions⟩) hs (by simp [hd.1]))

variable (δ : VariableDecomposition V)

theorem hasLinearConstants_definitions_decomposePath (P : TWE.Path Γ V) (s : FreshState Γ V)
    (hs : s.HasLinearConstants) :
    FreshState.HasLinearConstants ((decomposePath δ P).run s).2 := by
  induction P generalizing s with
  | init C => cases C <;> exact hs
  | join P Q ihP ihQ =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure]
      exact ihQ _ (ihP s hs)
  | norm P ih =>
      simp only [decomposePath, FreshDefM.run_bind, FreshDefM.run_pure]
      exact hasLinearConstants_normalize _ (hasLinearConstants_decomposePath δ P s) _ (ih s hs)
  | _ => exact hs

theorem hasLinearConstants_translate (b : Bool) (φ : TWE.Formula Γ V) (s : FreshState Γ V)
    (hs : FreshState.HasLinearConstants s) :
    FreshState.HasLinearConstants ((translate δ b φ).run s).2 ∧
      ((translate δ b φ).run s).1.hasLinearConstants := by
  induction φ generalizing b s with
  | top | bot => cases b <;> exact ⟨hs, rfl⟩
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] <;>
        exact ⟨(ihψ _ _ (ihφ _ s hs).1).1, by simp [(ihφ _ s hs).2, (ihψ _ _ (ihφ _ s hs).1).2]⟩
  | neg φ ih => cases b <;> exact ih _ s hs
  | atom a =>
      cases a with
      | pathEq P Q =>
          have hP := (hasLinearConstants_decomposePath δ P s).blocks
          have hQ := (hasLinearConstants_decomposePath δ Q ((decomposePath δ P).run s).2).blocks
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] <;>
            refine ⟨hasLinearConstants_definitions_decomposePath δ Q _
              (hasLinearConstants_definitions_decomposePath δ P s hs), ?_⟩ <;>
            split_ifs <;> first
              | rfl
              | simp only [TWE.Formula.hasLinearConstants_all, TWE.Formula.hasLinearConstants_any,
                  List.all_eq_true]
                intro B hB
                simp [hP _ (List.of_mem_zip hB).1, hQ _ (List.of_mem_zip hB).2]
      | pathIsLin P =>
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] <;>
            exact ⟨hasLinearConstants_definitions_decomposePath δ P s hs, by split_ifs <;> rfl⟩
      | treeWalk P T ℓ =>
          cases b <;> simp only [translate, FreshDefM.run_bind, FreshDefM.run_pure] <;>
            refine ⟨hasLinearConstants_normalize _ (hasLinearConstants_decomposePath δ P s) _
              (hasLinearConstants_definitions_decomposePath δ P s hs), ?_⟩ <;>
            simp [List.all_eq_true]
      | _ => cases b <;> exact ⟨hs, rfl⟩

theorem hasLinearConstants_linearTranslation (φ : TWE.Formula Γ V) :
    (linearTranslation δ φ).hasLinearConstants := by
  have h := hasLinearConstants_translate δ true φ ⟨φ.free ∪ δ.free, []⟩
    (by simp [FreshState.HasLinearConstants])
  simp only [linearTranslation, FreshDefM.start, TWE.Formula.hasLinearConstants_conj,
    TWE.Formula.hasLinearConstants_all, h.2, Bool.and_true, List.all_eq_true]
  exact h.1

end LinearConstants

theorem exists_sat_linearTranslation_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (δ : VariableDecomposition V)
    (φ : TWE.Formula Γ V) :
    (∃ M : WordModel Γ V, M.toTWE ⊨ linearTranslation δ φ) ↔
      ∃ M : WordModel Γ V, sourceModel δ M ⊨ φ := by
  have sat : ∀ M : WordModel Γ V, M.toTWE ⊨ linearTranslation δ φ ↔
      FreshState.Holds M ((translate δ true φ).run ⟨φ.free ∪ δ.free, []⟩).2 ∧
        M.toTWE ⊨ ((translate δ true φ).run ⟨φ.free ∪ δ.free, []⟩).1 :=
    fun M ↦ by simp [linearTranslation, FreshDefM.start, FreshState.Holds]
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨h, hF⟩ := (sat M).1 hM
    exact ⟨M, by simpa using (translate_sound δ true φ _ M h).1 hF⟩
  · rintro ⟨M, hM⟩
    obtain ⟨M', e, h⟩ := (extends_translate δ true φ ⟨φ.free ∪ δ.free, []⟩
      Free.subset_union_left Free.subset_union_right).exists_model M
    have hM' := (TWE.Model.sat_congr (eqOn_sourceModel δ e Free.subset_union_left
      Free.subset_union_right) (Free.Subset.refl _)).1 hM
    exact ⟨M', (sat _).2 ⟨h, (translate_sound δ true φ _ _ h).2 (by simpa using hM')⟩⟩

end ToLinear

end Bounded

end TWE

end Accordion

end
