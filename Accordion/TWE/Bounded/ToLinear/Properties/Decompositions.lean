module

public import Accordion.TWE.Bounded.ToLinear.Properties.Translation

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open Linear.ToWE (WordModel WordModel.evalPath)
open WE (GroundWord)

variable {Γ : Type} {V : TWE.Vars}

theorem blocksPath_splitPath (p : Accordion.Path Γ) :
    blocksPath (splitPath p).1 (splitPath p).2 = p := by
  apply Accordion.Path.eq_of_components_eq
  unfold splitPath
  induction p.components with
  | nil => rfl
  | cons c cs ih =>
      cases c <;> simp only [splitComponents]
      case name a =>
        rw [← List.singleton_append, blocksPath_append, Accordion.Path.components_join, ih]
        rfl
      all_goals
        rw [blocksPath, Accordion.Path.components_join, Accordion.Path.components_join, ih]
        rfl

theorem length_splitPath (p : Accordion.Path Γ) :
    (splitPath p).2.length = p.nonlinearCount := by
  rw [← nonlinearCount_blocksPath (splitPath p).1, blocksPath_splitPath]

section Free

variable [TWE.Vars.Comparable V]

theorem mem_pathVariables {P : TWE.Path Γ V} :
    (∀ x ∈ P.free.comp, x ∈ TWE.Path.compVars P) ∧
      (∀ X ∈ P.free.path, X ∈ TWE.Path.pathVars P) ∧
      ∀ X ∈ TWE.Path.pathVars P, .var X ∈ TWE.Path.subterms P := by
  induction P with
  | init C =>
      cases C with
      | name A => simp [TWE.Path.free, TWE.Component.free, Name.free_comp_path, TWE.Path.pathVars]
      | _ => simp [TWE.Path.free, TWE.Component.free, TWE.Path.compVars, TWE.Path.pathVars]
  | _ => aesop (add norm simp [TWE.Path.free, TWE.Path.compVars, TWE.Path.pathVars,
      TWE.Path.subterms])

theorem mem_formulaVariables {φ : TWE.Formula Γ V} :
    (∀ x ∈ φ.free.comp, x ∈ TWE.Formula.compVars φ) ∧
      (∀ X ∈ φ.free.path, X ∈ TWE.Formula.pathVars φ) ∧
      ∀ X ∈ TWE.Formula.pathVars φ, .var X ∈ TWE.Formula.paths φ := by
  induction φ with
  | atom a =>
      cases a <;> aesop (add norm simp [TWE.Formula.free, TWE.Atom.free,
        TWE.Formula.compVars, TWE.Formula.pathVars, TWE.Formula.paths,
        Tree.free_comp_path, Set.free_comp_path, Name.free_comp_path, mem_pathVariables])
  | _ => aesop (add norm simp [TWE.Formula.free, TWE.Formula.compVars,
      TWE.Formula.pathVars, TWE.Formula.paths])

end Free

section Blocks

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem freshBlocks_cons (C : Step) (steps : List Step) (U : TWE.Free V) :
    (freshBlocks (C :: steps)).run U =
      let r := (freshBlocks steps).run { U with path := insert (Fresh.fresh U.path) U.path }
      ((C, Fresh.fresh U.path) :: r.1, r.2) := rfl

theorem freshDecompositions_cons (p : V.Path × List Step) (paths : List (V.Path × List Step))
    (U : TWE.Free V) :
    (freshDecompositions (p :: paths)).run U =
      let b := (freshBlocks p.2).run { U with path := insert (Fresh.fresh U.path) U.path }
      let r := (freshDecompositions paths).run b.2
      ((p.1, Fresh.fresh U.path, b.1) :: r.1, r.2) := rfl

theorem exists_words_freshBlocks (r : List (Step × List Γ)) (U : TWE.Free V)
    (σ : V.Path → List Γ) :
    ∃ σ' : V.Path → List Γ, (∀ X ∈ U.path, σ' X = σ X) ∧
      ((freshBlocks (r.map Prod.fst)).run U).1.map (fun p ↦ (p.1, σ' p.2)) = r ∧
      U.path ⊆ ((freshBlocks (r.map Prod.fst)).run U).2.path ∧
      ∀ p ∈ ((freshBlocks (r.map Prod.fst)).run U).1,
        p.2 ∈ ((freshBlocks (r.map Prod.fst)).run U).2.path := by
  induction r generalizing U σ with
  | nil => exact ⟨σ, fun _ _ ↦ rfl, rfl, subset_rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
  | cons p r ih =>
      obtain ⟨C, w⟩ := p
      obtain ⟨σ', agree, words, sub, mem⟩ :=
        ih { U with path := insert (Fresh.fresh U.path) U.path }
          (Function.update σ (Fresh.fresh U.path) w)
      have first : σ' (Fresh.fresh U.path) = w :=
        (agree _ (Finset.mem_insert_self _ _)).trans (Function.update_self ..)
      rw [List.map_cons, freshBlocks_cons]
      refine ⟨σ', fun X hX ↦ ?_, ?_, (Finset.subset_insert _ _).trans sub, ?_⟩
      · exact (agree X (Finset.mem_insert_of_mem hX)).trans
          (Function.update_of_ne (Fresh.ne_fresh_of_mem hX) _ _)
      · simp only [List.map_cons, first, words]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact sub (Finset.mem_insert_self _ _)
        · exact mem p hp

theorem exists_words_freshDecompositions (vars : List V.Path)
    (f : V.Path → List Γ × List (Step × List Γ)) (U : TWE.Free V) (σ : V.Path → List Γ) :
    ∃ σ' : V.Path → List Γ, (∀ X ∈ U.path, σ' X = σ X) ∧
      ∀ X ∈ vars, ∃ b,
        ((freshDecompositions (vars.map fun X ↦ (X, (f X).2.map Prod.fst))).run U).1.lookup X =
          some b ∧
        σ' b.1 = (f X).1 ∧ b.2.map (fun p ↦ (p.1, σ' p.2)) = (f X).2 := by
  induction vars generalizing U σ with
  | nil => exact ⟨σ, fun _ _ ↦ rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
  | cons X vars ih =>
      obtain ⟨σ₁, agree₁, words, sub, mem⟩ := exists_words_freshBlocks (f X).2
        { U with path := insert (Fresh.fresh U.path) U.path }
        (Function.update σ (Fresh.fresh U.path) (f X).1)
      obtain ⟨σ₂, agree₂, all⟩ := ih
        ((freshBlocks ((f X).2.map Prod.fst)).run
          { U with path := insert (Fresh.fresh U.path) U.path }).2 σ₁
      rw [List.map_cons, freshDecompositions_cons]
      refine ⟨σ₂, fun Y hY ↦ ?_, fun Y hY ↦ ?_⟩
      · exact (agree₂ Y (sub (Finset.mem_insert_of_mem hY))).trans
          ((agree₁ Y (Finset.mem_insert_of_mem hY)).trans
            (Function.update_of_ne (Fresh.ne_fresh_of_mem hY) _ _))
      · by_cases hYX : Y = X
        · subst hYX
          refine ⟨_, List.lookup_cons_self, ?_, ?_⟩
          · exact (agree₂ _ (sub (Finset.mem_insert_self _ _))).trans
              ((agree₁ _ (Finset.mem_insert_self _ _)).trans (Function.update_self ..))
          · exact (List.map_congr_left fun p hp ↦ by rw [agree₂ p.2 (mem p hp)]).trans words
        · obtain ⟨b, hb, h⟩ := all Y (List.mem_of_ne_of_mem hYX hY)
          refine ⟨b, ?_, h⟩
          rw [List.lookup_cons, beq_eq_false_iff_ne.2 hYX]
          exact hb

end Blocks

private theorem lookup_map_self {α β : Type} [DecidableEq α] {xs : List α} {x : α} (f : α → β)
    (h : x ∈ xs) : (xs.map fun y ↦ (y, f y)).lookup x = some (f x) := by
  induction xs with
  | nil => simp at h
  | cons y xs ih =>
      by_cases e : x = y
      · simp [e]
      · simp_all [List.lookup, beq_eq_false_iff_ne.2 e]

theorem exists_sourceModel_modelDecomposition [Ord Γ] [Nonempty Γ] [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] (m : TWE.Model Γ V) (wf : m.WF) (φ : TWE.Formula Γ V) :
    ∃ M : WordModel Γ V, TWE.Model.EqOn (sourceModel (modelDecomposition m φ) M) m φ.free := by
  obtain ⟨a⟩ := ‹Nonempty Γ›
  obtain ⟨σ, -, blocks⟩ := exists_words_freshDecompositions (TWE.Formula.pathVars φ)
    (fun X ↦ splitPath (m.σPath X)) φ.free (fun _ ↦ [])
  refine ⟨⟨m.σName, fun x ↦ match m.σComp x with | .name b => b | _ => a, σ,
    fun ℓ ↦ (m.σLoc ℓ).names, m.σSet, fun T ↦ ⟨m.θ T, wf.2 T⟩⟩,
    fun _ _ ↦ rfl, fun x hx ↦ ?_, fun X hX ↦ ?_, fun ℓ _ ↦ ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  · simp only [sourceModel, VariableDecomposition.component, modelDecomposition,
      lookup_map_self _ (mem_formulaVariables.1 x hx), Option.getD_some]
    cases h : m.σComp x <;> simp [Accordion.Component.kind]
  · obtain ⟨b, hb, first, rest⟩ := blocks X (mem_formulaVariables.2.1 X hX)
    simp only [sourceModel, VariableDecomposition.path, modelDecomposition, hb, Option.getD_some,
      first, rest, blocksPath_splitPath]
  · exact Path.descend_names_of_linear (wf.1 ℓ)

theorem mem_assignments {α β : Type} (keys : List α) (values : Guess β) (f : α → β)
    (h : ∀ x ∈ keys, f x ∈ values) : (keys.map fun x ↦ (x, f x)) ∈ assignments keys values := by
  induction keys with
  | nil => simp [assignments]
  | cons x keys ih =>
      simp only [assignments, Guess.mem_bind, Guess.mem_pure, List.map_cons]
      exact ⟨f x, h x List.mem_cons_self, _, ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy), rfl⟩

theorem mem_stepPatterns {steps : List Step} {k : Nat} (h : steps.length ≤ k) :
    steps ∈ stepPatterns k := by
  induction k generalizing steps with
  | zero => simp_all [stepPatterns]
  | succ k ih =>
      cases steps with
      | nil => simp [stepPatterns]
      | cons C steps => cases C <;> simp_all [stepPatterns]

section Equivalence

variable [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem VariableDecomposition.isBounded_iff_boundedAt_sourceModel (k : Nat)
    (δ : VariableDecomposition V) (M : WordModel Γ V)
    (φ : TWE.Formula Γ V) : δ.isBounded k φ = true ↔ (sourceModel δ M).BoundedAt k φ := by
  simp only [VariableDecomposition.isBounded, TWE.Model.BoundedAt, List.all_eq_true,
    decide_eq_true_eq]
  exact forall₂_congr fun P hP ↦ by
    rw [length_rest_decomposePath δ P
      (Free.Subset.trans (TWE.Formula.free_subset_of_mem_paths hP) Free.subset_union_left)
      Free.subset_union_right M]

omit [Ord Γ] [DecidableEq Γ] in
theorem mem_boundedDecompositions {k : Nat} {φ : TWE.Formula Γ V} {δ : VariableDecomposition V} :
    δ ∈ boundedDecompositions k φ ↔ δ ∈ variableDecompositions k φ ∧ δ.isBounded k φ = true := by
  simp only [boundedDecompositions, Guess.mem_bind, Guess.mem_guard, Guess.mem_pure, exists_const]
  exact ⟨fun ⟨_, h, hb, e⟩ ↦ e ▸ ⟨h, hb⟩, fun ⟨h, hb⟩ ↦ ⟨δ, h, hb, rfl⟩⟩

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem linearTranslation_equisat [Nonempty Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ δ ∈ boundedDecompositions k φ, ∃ M : WordModel Γ V, M.toTWE ⊨ linearTranslation δ φ) ↔
      Bounded.Formula.SAT k φ := by
  simp only [exists_sat_linearTranslation_iff]
  constructor
  · rintro ⟨δ, hδ, M, sat⟩
    exact ⟨⟨sourceModel δ M, wf_sourceModel δ M,
      (VariableDecomposition.isBounded_iff_boundedAt_sourceModel k δ M φ).1
      (mem_boundedDecompositions.1 hδ).2⟩, sat⟩
  · rintro ⟨⟨m, wf, bounded⟩, sat⟩
    obtain ⟨M, eq⟩ := exists_sourceModel_modelDecomposition m wf φ
    refine ⟨modelDecomposition m φ, mem_boundedDecompositions.2
      ⟨?_, (VariableDecomposition.isBounded_iff_boundedAt_sourceModel _ _ M _).2 ?_⟩, M,
      (TWE.Model.sat_congr eq (Free.Subset.refl _)).2 sat⟩
    · simp only [variableDecompositions, Guess.mem_bind, Guess.mem_pure]
      refine ⟨_, mem_assignments _ _ _ fun x _ ↦ ?_, _, mem_assignments _ _ _ fun X hX ↦ ?_, rfl⟩
      · cases m.σComp x <;> simp [ComponentKind.all, Accordion.Component.kind]
      · apply mem_stepPatterns
        simpa [length_splitPath, TWE.Model.evalPath] using
          bounded _ (mem_formulaVariables.2.2 X hX)
    · intro P hP
      rw [TWE.Model.evalPath_congr eq (TWE.Formula.free_subset_of_mem_paths hP)]
      exact bounded P hP

theorem guess_linearTranslation_equisat [Nonempty Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ (do
          let δ ← boundedDecompositions k φ
          return linearTranslation δ φ : Guess (TWE.Formula Γ V)),
        Linear.Formula.SAT ψ) ↔
      Bounded.Formula.SAT k φ := by
  simp [← linearTranslation_equisat k φ,
    Linear.ToWE.SAT_iff_exists_sat_toTWE (hasLinearConstants_linearTranslation _ _)]

end Equivalence

end ToLinear

end Bounded

end TWE

end Accordion

end
