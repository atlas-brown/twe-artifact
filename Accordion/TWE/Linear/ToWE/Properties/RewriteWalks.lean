module

public import Accordion.TWE.Linear.ToWE.Properties.Trees

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives

variable {Γ : Type} {V : TWE.Vars}

theorem allAtoms_walksRewritten_positive_negative (φ : TWE.Formula Γ V) :
    (rewriteWalks.positive φ).AllAtoms Atom.WalksRewritten ∧
      (rewriteWalks.negative φ).AllAtoms Atom.WalksRewritten := by
  induction φ with
  | conj φ ψ ihφ ihψ =>
      exact ⟨Guess.AllAtoms.and ihφ.1 ihψ.1, Guess.AllAtoms.or ihφ.2 ihψ.2⟩
  | disj φ ψ ihφ ihψ =>
      exact ⟨Guess.AllAtoms.or ihφ.1 ihψ.1, Guess.AllAtoms.and ihφ.2 ihψ.2⟩
  | neg φ ih => exact ⟨ih.2, ih.1⟩
  | atom a =>
      cases a <;> constructor <;>
        (simp only [rewriteWalks.positive, rewriteWalks.negative]; all_atoms <;> trivial)
  | _ => constructor <;> (simp only [rewriteWalks.positive, rewriteWalks.negative]; all_atoms)

theorem allAtoms_walksRewritten_rewriteWalks (φ : TWE.Formula Γ V) :
    (rewriteWalks φ).AllAtoms Atom.WalksRewritten := by
  unfold rewriteWalks
  split_ifs
  exacts [(allAtoms_walksRewritten_positive_negative φ).1, Guess.AllAtoms.bot]

variable [Ord Γ] [DecidableEq Γ]

theorem sat_treeWalk_iff (m : WordModel Γ V) {p : TWE.Path Γ V} (hp : p.hasLinearConstants)
    (τ : TWE.Tree V) (l : V.Loc) :
    m.toTWE ⊨ (τ ⊢ p ⇝ l : TWE.Formula Γ V) ↔
      m.toTWE ⊨ (p ≐ (.loc l : TWE.Path Γ V) : TWE.Formula Γ V) ∧
        (m.toTWE ⊨ (τ ∶ .file : TWE.Formula Γ V) ∨ m.toTWE ⊨ (τ ∶ .dirc : TWE.Formula Γ V)) ∧
        (m.toTWE ⊨ ((τ[l]) ∶ .absent : TWE.Formula Γ V) ∨
          m.toTWE ⊨ ((τ[l]) ∶ .file : TWE.Formula Γ V) ∨
          m.toTWE ⊨ ((τ[l]) ∶ .dirc : TWE.Formula Γ V)) := by
  rw [sat_treeShape_or_iff_exists_evalTree]
  change
    (match m.toTWE.evalTree τ with
      | some (.tree tree) =>
          match FileTree.resolve (m.toTWE.evalPath p) tree with
          | some (C, _) => C.path = m.toTWE.σLoc l
          | none => False
      | _ => False) ↔
      m.toTWE.evalPath p = m.toTWE.σLoc l ∧
        (m.toTWE ⊨ (τ ∶ .file : TWE.Formula Γ V) ∨ m.toTWE ⊨ (τ ∶ .dirc : TWE.Formula Γ V)) ∧
        ∃ f, m.toTWE.evalTree (.select τ l) = some f
  simp only [sat_treeShape_iff, TWE.Model.evalTree_select_eq_some_iff]
  rcases ht : m.toTWE.evalTree τ with _ | tree | _
  · simp
  · dsimp only
    cases hres : FileTree.resolve (m.toTWE.evalPath p) tree with
    | none =>
        simp only [false_iff, not_and]
        rintro hpl - ⟨f, _, C, ⟨⟩, hr⟩
        rw [← hpl] at hr
        exact absurd (hres.symm.trans hr) (by simp)
    | some r =>
        obtain ⟨C, f⟩ := r
        have hC : C.path = m.toTWE.evalPath p := by
          rw [FileTree.path_eq_norm_of_resolve hres, evalPath_toTWE m hp]
          exact Path.norm_descend _
        dsimp only
        rw [hC]
        refine ⟨fun hpl ↦ ⟨hpl, ?_, f, _, C, rfl, hpl ▸ hres⟩, fun h ↦ h.1⟩
        cases tree <;> simp [FileTree.Focus.shape]
  · simp [FileTree.Focus.shape]

theorem sat_positive_treeWalk_iff (m : WordModel Γ V) {P : TWE.Path Γ V}
    (hP : P.hasLinearConstants) (T : TWE.Tree V) (ℓ : V.Loc) :
    Guess.sat m (rewriteWalks.positive (.atom (.treeWalk P T ℓ))) ↔
      m.toTWE ⊨ (T ⊢ P ⇝ ℓ : TWE.Formula Γ V) := by
  rw [sat_treeWalk_iff m hP, sat_treeShape_select_iff, sat_treeShape_select_iff,
    sat_treeShape_select_iff,
    ← observesShape_nil_iff_sat m T .file, ← observesShape_nil_iff_sat m T .dirc,
    ← sat_toWE_toWord_eq_iff m hP (rfl : (TWE.Path.loc ℓ : TWE.Path Γ V).hasLinearConstants)]
  simp only [rewriteWalks.positive, Guess.sat_any, Guess.sat_and, InjectAtom.inject_guess,
    Guess.sat_atom, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    Atom.sat, Path.evalWord_toWord, WordModel.evalPath, evalWord_empty]
  grind

theorem sat_negative_treeWalk_iff (m : WordModel Γ V) {P : TWE.Path Γ V}
    (hP : P.hasLinearConstants) (T : TWE.Tree V) (ℓ : V.Loc) :
    Guess.sat m (rewriteWalks.negative (.atom (.treeWalk P T ℓ))) ↔
      ¬m.toTWE ⊨ (T ⊢ P ⇝ ℓ : TWE.Formula Γ V) := by
  rw [sat_treeWalk_iff m hP, sat_treeShape_select_iff, sat_treeShape_select_iff,
    sat_treeShape_select_iff]
  simp only [not_and_or]
  rw [← not_exists_observesShape_nil_or_absent_iff, ← exists_observesShape_iff,
    ← sat_toWE_toWord_ne_iff m hP (rfl : (TWE.Path.loc ℓ : TWE.Path Γ V).hasLinearConstants)]
  simp [rewriteWalks.negative, Atom.sat, Path.evalWord_toWord, WordModel.evalPath]
  tauto

theorem sat_positive_iff_and_sat_negative_iff (m : WordModel Γ V) {φ : TWE.Formula Γ V}
    (hφ : φ.hasLinearConstants) :
    (Guess.sat m (rewriteWalks.positive φ) ↔ m.toTWE ⊨ φ) ∧
      (Guess.sat m (rewriteWalks.negative φ) ↔ ¬m.toTWE ⊨ φ) := by
  induction φ with
  | top | bot => simp [rewriteWalks.positive, rewriteWalks.negative]
  | conj φ ψ ihφ ihψ =>
      simp only [TWE.Formula.hasLinearConstants, TWE.Formula.paths, List.all_append,
        Bool.and_eq_true] at hφ
      simp [rewriteWalks.positive, rewriteWalks.negative, (ihφ hφ.1).1, (ihφ hφ.1).2,
        (ihψ hφ.2).1, (ihψ hφ.2).2, or_iff_not_imp_left]
  | disj φ ψ ihφ ihψ =>
      simp only [TWE.Formula.hasLinearConstants, TWE.Formula.paths, List.all_append,
        Bool.and_eq_true] at hφ
      simp [rewriteWalks.positive, rewriteWalks.negative, (ihφ hφ.1).1, (ihφ hφ.1).2,
        (ihψ hφ.2).1, (ihψ hφ.2).2]
  | neg φ ih => simp [rewriteWalks.positive, rewriteWalks.negative, (ih hφ).1, (ih hφ).2]
  | atom a =>
      have hpath {p : TWE.Path Γ V} (hp : p ∈ TWE.Formula.paths (.atom a)) :
          p.hasLinearConstants := List.all_eq_true.1 hφ p hp
      cases a with
      | pathEq P Q =>
          have hP := hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])
          have hQ := hpath (p := Q) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])
          exact ⟨by simpa [rewriteWalks.positive, Atom.sat] using sat_toWE_toWord_eq_iff m hP hQ,
            by simpa [rewriteWalks.negative, Atom.sat] using sat_toWE_toWord_ne_iff m hP hQ⟩
      | pathIsLin P =>
          have hP := hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])
          have h : m.toTWE ⊨ (Lin P : TWE.Formula Γ V) := by
            change (m.toTWE.evalPath P).Linear
            rw [evalPath_toTWE m hP]
            exact Path.linear_descend _
          simpa [rewriteWalks.positive, rewriteWalks.negative] using h
      | treeWalk P T ℓ =>
          have hP := hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])
          exact ⟨sat_positive_treeWalk_iff m hP T ℓ, sat_negative_treeWalk_iff m hP T ℓ⟩
      | treeShape T h =>
          refine ⟨by
            simpa [rewriteWalks.positive, Atom.sat] using observesShape_nil_iff_sat m T h, ?_⟩
          simp only [rewriteWalks.negative, Guess.sat_or, InjectAtom.inject_guess, Guess.sat_atom,
            Guess.sat_any, Atom.sat, evalWord_empty]
          rw [← observesShape_nil_iff_sat, not_observesShape_iff]
      | setEq | setMem =>
          simp [rewriteWalks.positive, rewriteWalks.negative, Atom.sat, TWESetAtom.sat]

theorem SAT_rewriteWalks_iff [Nonempty Γ] (φ : TWE.Formula Γ V) :
    Guess.SAT (rewriteWalks φ) ↔ TWE.Linear.Formula.SAT φ := by
  unfold rewriteWalks
  split_ifs with hφ
  · rw [SAT_iff_exists_sat_toTWE hφ]
    exact exists_congr fun m ↦ (sat_positive_iff_and_sat_negative_iff m hφ).1
  · exact iff_of_false (by simp [Guess.SAT]) fun h ↦ hφ (TWE.Formula.hasLinearConstants_of_SAT h)

end ToWE

end Linear

end TWE

end Accordion

end
