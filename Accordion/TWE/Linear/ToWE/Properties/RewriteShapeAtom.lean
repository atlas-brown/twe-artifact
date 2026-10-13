module

public import Accordion.TWE.Linear.ToWE.Properties.Trees

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open WE (GroundWord)
open FileTree.Focus (follow shapeFollow entriesFollow follow_append map_snd_resolve_descend)

variable {Γ : Type} {V : TWE.Vars}

theorem observesShape_select_iff [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V) (l : V.Loc)
    (query : List Γ) (h : TWE.Shape) :
    ObservesShape m (.select T l) query h ↔ ObservesShape m T (m.σLoc l ++ query) h := by
  have hselect : m.toTWE.evalTree (.select T l) =
      (m.toTWE.evalTree T).bind (fun f ↦ follow f (m.σLoc l)) := by
    cases hT : m.toTWE.evalTree T with
    | none => simp [TWE.Model.evalTree, hT]
    | some base =>
        rw [TWE.Model.evalTree, hT]
        change (base.resolve (Path.descend (m.σLoc l))).bind (fun (_, f) ↦ some f) =
          follow base (m.σLoc l)
        simpa [Option.map_eq_bind] using map_snd_resolve_descend (m.σLoc l) base
  simp only [ObservesShape, hselect, shapeFollow, follow_append]
  rcases m.toTWE.evalTree T with _ | base
  · simp
  · cases hf : follow base (m.σLoc l) <;> simp [hf]

theorem sat_updateDefined_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (l : V.Loc) (T' : TWE.Tree V) :
    Guess.sat m (updateDefined T ↑l T') ↔ (m.toTWE.evalTree (.update T l T')).isSome := by
  rw [TWE.Model.isSome_evalTree_update_iff]
  have hselect (h : TWE.Shape) :
      ObservesShape m T (m.σLoc l) h ↔ ObservesShape m (.select T l) [] h := by
    rw [observesShape_select_iff, List.append_nil]
  simp only [updateDefined, Guess.sat_or, Guess.sat_and, Guess.sat_any, InjectAtom.inject_guess,
    Guess.sat_atom, Atom.sat, Formula.sat, WE.Model.sat_wordEq_iff, evalWord_loc, evalWord_empty,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hselect,
    observesShape_nil_iff, exists_evalTree_update_iff]
  rcases m.toTWE.evalTree (.select T l) with _ | (_ | (_ | _)) | _ <;>
    rcases m.toTWE.evalTree T with _ | (_ | (_ | _)) | _ <;>
    rcases m.toTWE.evalTree T' with _ | (_ | (_ | _)) | _ <;>
    simp [FileTree.Focus.shape]

theorem sat_updateUndefined_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (l : V.Loc) (T' : TWE.Tree V) :
    Guess.sat m (updateUndefined T ↑l T') ↔ ¬(m.toTWE.evalTree (.update T l T')).isSome := by
  rw [TWE.Model.isSome_evalTree_update_iff]
  have hselect (h : TWE.Shape) :
      ObservesShape m T (m.σLoc l) h ↔ ObservesShape m (.select T l) [] h := by
    rw [observesShape_select_iff, List.append_nil]
  simp only [updateUndefined, Guess.sat_or, Guess.sat_and, InjectAtom.inject_guess, Guess.sat_atom,
    Atom.sat, Formula.sat, WE.Model.sat_wordEq_iff, evalWord_loc, evalWord_empty, hselect,
    observesShape_nil_iff, exists_evalTree_update_iff]
  by_cases hloc : m.σLoc l = [] <;>
    rcases m.toTWE.evalTree (.select T l) with _ | (_ | (_ | _)) | _ <;>
    rcases m.toTWE.evalTree T with _ | (_ | (_ | _)) | _ <;>
    rcases m.toTWE.evalTree T' with _ | (_ | (_ | _)) | _ <;>
    simp [FileTree.Focus.shape, hloc]

/-- Stated for an atom `atom T w` that means `P m T w`, so that it serves both `T[w] ∶ h` and
`T[w]↑`. -/
theorem satFresh_updateCases [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] (m : WordModel Γ V) {U W : TWE.Free V} (T : TWE.Tree V) (l : V.Loc)
    (T' : TWE.Tree V) (ℓ : Word Γ V) (hT : T.free ⊆ U) (hl : l ∈ U.loc) (hT' : T'.free ⊆ U)
    (hℓ : Word.free ℓ ⊆ U) (atom : TWE.Tree V → Word Γ V → Atom Γ V)
    (P : WordModel Γ V → TWE.Tree V → List Γ → Prop)
    (hatom : ∀ m T w, (atom T w).sat m ↔ P m T (m.toWE.evalWord w))
    (hP : ∀ m m' T w, m ≡[U] m' → T.free ⊆ U → (P m T w ↔ P m' T w))
    (K : V.Path) (hK : K ∉ U.path) (hUW : U ⊆ W) :
    Guess.satFresh m U
        ((ℓ ≐ (l : Word Γ V) ++ (K : Word Γ V) ∧ pure [atom T' (K : Word Γ V)]) ∨
          ⌜(((l : Word Γ V) ⋠ ℓ).run W).1⌝ ∧ pure [atom T ℓ]) ↔
      (∃ suffix, m.toWE.evalWord ℓ = m.σLoc l ++ suffix ∧ P m T' suffix) ∨
        (¬m.σLoc l <+: m.toWE.evalWord ℓ ∧ P m T (m.toWE.evalWord ℓ)) := by
  have hloc : Word.free (l : Word Γ V) ⊆ U := by free_vars
  rw [Guess.satFresh_or]
  refine or_congr ?_ ?_
  · simp only [Guess.satFresh, Guess.sat_and, InjectAtom.inject_guess, Guess.sat_atom, hatom]
    simp only [Atom.sat, Formula.sat, WE.Model.sat_wordEq_iff, WE.Model.evalWord_append,
      evalWord_loc,
      evalWord_pathVar]
    constructor
    · rintro ⟨m', hm, hword, hP'⟩
      exact ⟨m'.σPath K, by rw [evalWord_congr hm hℓ, hword, hm.σLoc_eq hl],
        (hP m m' T' _ hm hT').2 hP'⟩
    · rintro ⟨suffix, hword, hP'⟩
      have hm : m ≡[U] m.setPath K suffix := WordModel.congr_setPath hK
      refine ⟨_, hm, ?_, (hP _ _ T' _ hm hT').1 (by simpa using hP')⟩
      rw [← evalWord_congr hm hℓ, hword]
      simp
  · simp only [Guess.satFresh, Guess.sat_and, InjectAtom.inject_guess, Guess.sat_atom, hatom]
    simp only [Atom.sat]
    constructor
    · rintro ⟨m', hm, hpre, hP'⟩
      have hpre := not_prefix_of_sat_notPrefixFormula _ _ _ _ hpre
      rw [evalWord_loc, ← hm.σLoc_eq hl, ← evalWord_congr hm hℓ] at hpre
      exact ⟨hpre, (hP m m' T _ hm hT).2 (by rwa [evalWord_congr hm hℓ])⟩
    · rintro ⟨hpre, hP'⟩
      obtain ⟨m', hm, hsat⟩ := (exists_sat_notPrefixFormula_iff m hUW hloc hℓ).2
        (by rwa [evalWord_loc])
      exact ⟨m', hm, hsat, by rw [← evalWord_congr hm hℓ]; exact (hP m m' T _ hm hT).1 hP'⟩

theorem not_exists_observesShape_update_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (m : WordModel Γ V)
    {T replacement : TWE.Tree V} {l : V.Loc}
    (hdefined : (m.toTWE.evalTree (.update T l replacement)).isSome) (query : List Γ) :
    (¬∃ h, ObservesShape m (.update T l replacement) query h) ↔
      (∃ suffix, query = m.σLoc l ++ suffix ∧ ¬∃ h, ObservesShape m replacement suffix h) ∨
        (¬m.σLoc l <+: query ∧ ¬∃ h, ObservesShape m T query h) := by
  simp only [observesShape_update_iff m hdefined]
  by_cases hp : m.σLoc l <+: query
  · obtain ⟨suffix, rfl⟩ := hp
    simp
  · have hne : ∀ s, query ≠ m.σLoc l ++ s := fun s h ↦ hp ⟨s, h.symm⟩
    simp [hp, hne]

theorem observesShape_file_iff [Ord Γ] (m : WordModel Γ V) (w : List Γ) (h : TWE.Shape) :
    ObservesShape m .file w h ↔ h = .file ∧ w = [] := by
  cases w <;> cases h <;>
    simp [ObservesShape, TWE.Model.evalTree, shapeFollow, follow, FileTree.Focus.shape]

theorem observesShape_abst_iff [Ord Γ] (m : WordModel Γ V) (w : List Γ) (h : TWE.Shape) :
    ObservesShape m .abst w h ↔ h = .absent ∧ w = [] := by
  cases w <;> cases h <;>
    simp [ObservesShape, TWE.Model.evalTree, shapeFollow, follow, FileTree.Focus.shape]

theorem observesShape_emptyDirc_iff [Ord Γ] (m : WordModel Γ V) (w : List Γ) (h : TWE.Shape) :
    ObservesShape m .emptyDirc w h ↔ (h = .dirc ∧ w = []) ∨ (h = .absent ∧ ∃ a, w = [a]) := by
  rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩ <;> cases h <;>
    simp [ObservesShape, TWE.Model.evalTree, shapeFollow, follow, FileTree.Focus.shape]

theorem not_exists_observesShape_var_iff [Ord Γ] (m : WordModel Γ V) (x : V.Tree) (query : List Γ) :
    (¬∃ h, ObservesShape m (.var x) query h) ↔
      ∃ pre a suffix, query = pre ++ a :: suffix ∧
        (ObservesShape m (.var x) pre .file ∨ ObservesShape m (.var x) pre .absent) := by
  have hobserves : ∀ w h, ObservesShape m (.var x) w h ↔
      ∃ f, follow (m.θ x).1 w = some f ∧ f.shape = h := fun w h ↦ by
    simp [ObservesShape, shapeFollow, TWE.Model.evalTree, WordModel.toTWE]
  simp only [hobserves, ← exists_or, ← and_or_left]
  rw [show (¬∃ h f, follow (m.θ x).1 query = some f ∧ f.shape = h) ↔
      follow (m.θ x).1 query = none by
    cases follow (m.θ x).1 query <;> simp, follow_eq_none_iff]
  simp [Leaf, eq_comm]

theorem rewriteShapeAtom_satPreserving [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] {U : TWE.Free V} (α : Atom Γ V)
    (hα : α.free ⊆ U) : SatPreservingIn α.DefinedIn U [α] ((rewriteShapeAtom α).run U).1 := by
  refine .of_atom fun m hdefined ↦ ?_
  cases α with
  | shape T ℓ h =>
      obtain ⟨hT, hℓ⟩ : T.free ⊆ U ∧ Word.free ℓ ⊆ U := Free.union_subset hα
      cases T with
      | var t => exact Guess.satFresh_atom hα
      | file | abst =>
          simp only [rewriteShapeAtom, FreshM.run_pure, InjectAtom.inject_guess]
          split_ifs with hh
          · rw [Guess.satFresh_atom (by free_vars)]
            simp [Atom.sat, observesShape_file_iff, observesShape_abst_iff, hh]
          · simp [Atom.sat, observesShape_file_iff, observesShape_abst_iff, hh]
      | emptyDirc =>
          cases h <;>
            simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, FreshM.run_pure,
              InjectAtom.inject_guess, Atom.sat, observesShape_emptyDirc_iff, reduceCtorEq,
              true_and, false_and, or_false, false_or, Guess.satFresh_bot]
          case dirc =>
              rw [Guess.satFresh_atom (by free_vars)]
              simp [Atom.sat]
          case absent =>
              constructor
              · rintro ⟨m', hm, hsat⟩
                have hsat : m'.toWE.evalWord ℓ = [m'.σName (Fresh.fresh U.name)] := by
                  simpa [Atom.sat] using hsat
                exact ⟨_, (evalWord_congr hm hℓ).trans hsat⟩
              · rintro ⟨a, ha⟩
                have hm : m ≡[U] m.setName (Fresh.fresh U.name) a :=
                  WordModel.congr_setName (Fresh.fresh_notMem _)
                refine ⟨_, hm, ?_⟩
                simpa [Atom.sat, ← evalWord_congr hm hℓ] using ha
      | select T l =>
          simp only [rewriteShapeAtom, FreshM.run_pure, InjectAtom.inject_guess]
          rw [Guess.satFresh_atom (by free_vars)]
          simp only [Atom.sat, WE.Model.evalWord_append, evalWord_loc, observesShape_select_iff]
      | update T l T' =>
          have hfree : T.free ⊆ U ∧ l ∈ U.loc ∧ T'.free ⊆ U := by free_vars
          exact (satFresh_updateCases m T l T' ℓ hfree.1 hfree.2.1 hfree.2.2 hℓ (.shape · · h)
            (ObservesShape · · · h) (fun _ _ _ ↦ Iff.rfl)
            (fun _ _ _ _ hm hT ↦ observesShape_congr hm hT _ _) _ (Fresh.fresh_notMem _)
            (subset_freshPath U)).trans
              (observesShape_update_iff m (hdefined _ (by simp [Atom.updates, TWE.Tree.updates])) _
                h).symm
  | undefined T ℓ =>
      obtain ⟨hT, hℓ⟩ : T.free ⊆ U ∧ Word.free ℓ ⊆ U := Free.union_subset hα
      cases T with
      | var t =>
          let A : V.Name := Fresh.fresh U.name
          let J : V.Path := Fresh.fresh U.path
          let K : V.Path := Fresh.fresh (insert J U.path)
          have hJK : J ≠ K := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
          have hrun (m' : WordModel Γ V) :
              Guess.sat m' ((rewriteShapeAtom (.undefined (.var t) ℓ)).run U).1 ↔
                m'.toWE.evalWord ℓ = m'.σPath J ++ [m'.σName A] ++ m'.σPath K ∧
                  (ObservesShape m' (.var t) (m'.σPath J) .file ∨
                    ObservesShape m' (.var t) (m'.σPath J) .absent) := by
            simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, run_freshPath,
              FreshM.run_pure]
            simp [Atom.sat, A, J, K]
          rw [Atom.sat, not_exists_observesShape_var_iff]
          simp only [Guess.satFresh, hrun]
          constructor
          · rintro ⟨m', hm, hword, hJ⟩
            refine ⟨m'.σPath J, m'.σName A, m'.σPath K, ?_, ?_⟩
            · rw [evalWord_congr hm hℓ, hword]
              simp
            · simpa only [observesShape_congr hm hT] using hJ
          · rintro ⟨pre, a, suffix, hword, hJ⟩
            let m' := ((m.setName A a).setPath J pre).setPath K suffix
            have hm : m ≡[U] m' :=
              ((WordModel.congr_setName (Fresh.fresh_notMem _)).trans
                (WordModel.congr_setPath (Fresh.fresh_notMem _))).trans
                (WordModel.congr_setPath (Fresh.fresh_notMem_of_subset (Finset.subset_insert _ _)))
            have hσJ : m'.σPath J = pre := by simp [m', hJK]
            refine ⟨m', hm, ?_, ?_⟩
            · rw [← evalWord_congr hm hℓ, hword, hσJ]
              simp [m']
            · simpa only [hσJ, ← observesShape_congr hm hT] using hJ
      | file | abst =>
          simp only [rewriteShapeAtom, FreshM.run_pure, InjectAtom.inject_guess]
          rw [Guess.satFresh_atom (by free_vars)]
          simp [Atom.sat, observesShape_file_iff, observesShape_abst_iff]
      | emptyDirc =>
          let A : V.Name := Fresh.fresh U.name
          let B : V.Name := Fresh.fresh (insert A U.name)
          let K : V.Path := Fresh.fresh U.path
          have hAB : A ≠ B := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
          have hrun (m' : WordModel Γ V) :
              Guess.sat m' ((rewriteShapeAtom (.undefined .emptyDirc ℓ)).run U).1 ↔
                m'.toWE.evalWord ℓ = [m'.σName A] ++ [m'.σName B] ++ m'.σPath K := by
            simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, run_freshPath,
              FreshM.run_pure]
            simp [Atom.sat, A, B, K]
          simp only [Guess.satFresh, hrun, Atom.sat, observesShape_emptyDirc_iff]
          constructor
          · rintro ⟨m', hm, hword⟩
            rw [evalWord_congr hm hℓ, hword]
            simp
          · intro hnot
            rcases hw : m.toWE.evalWord ℓ with _ | ⟨a, _ | ⟨b, w⟩⟩
            · simp [hw] at hnot
            · simp [hw] at hnot
            · let m' := ((m.setName A a).setName B b).setPath K w
              have hm : m ≡[U] m' :=
                ((WordModel.congr_setName (Fresh.fresh_notMem _)).trans
                  (WordModel.congr_setName
                    (Fresh.fresh_notMem_of_subset (Finset.subset_insert _ _)))).trans
                  (WordModel.congr_setPath (Fresh.fresh_notMem _))
              refine ⟨m', hm, ?_⟩
              rw [← evalWord_congr hm hℓ, hw]
              simp [m', hAB]
      | select T l =>
          simp only [rewriteShapeAtom, FreshM.run_pure, InjectAtom.inject_guess]
          rw [Guess.satFresh_atom (by free_vars)]
          simp only [Atom.sat, WE.Model.evalWord_append, evalWord_loc, observesShape_select_iff]
      | update T l T' =>
          have hfree : T.free ⊆ U ∧ l ∈ U.loc ∧ T'.free ⊆ U := by free_vars
          exact (satFresh_updateCases m T l T' ℓ hfree.1 hfree.2.1 hfree.2.2 hℓ (.undefined · ·)
            (fun m T w ↦ ¬∃ h, ObservesShape m T w h) (fun _ _ _ ↦ Iff.rfl)
            (fun _ _ _ _ hm hT ↦ by simp only [observesShape_congr hm hT]) _
            (Fresh.fresh_notMem _) (subset_freshPath U)).trans
              (not_exists_observesShape_update_iff m
                (hdefined _ (by simp [Atom.updates, TWE.Tree.updates])) _).symm
  | _ => exact Guess.satFresh_atom hα

section Rank

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem run_rewriteShapeAtom_of_shapeRank_eq_zero (α : Atom Γ V) (hα : α.shapeRank = 0)
    (U : TWE.Free V) :
    ((rewriteShapeAtom α).run U).1 = pure [α] := by
  rcases α with _ | ⟨T, ℓ, h⟩ | ⟨T, ℓ⟩ | _ | _ | _ <;> try rfl
  · cases T <;> first | rfl | simp [Atom.shapeRank, TWE.Tree.size] at hα
  · simp [Atom.shapeRank] at hα

theorem allAtoms_shapeRank_lt_rewriteShapeAtom (α : Atom Γ V) (U : TWE.Free V) :
    ((rewriteShapeAtom α).run U).1.AllAtoms
      fun a ↦ a.shapeRank = 0 ∨ a.shapeRank < α.shapeRank := by
  by_cases hα : α.shapeRank = 0
  · rw [run_rewriteShapeAtom_of_shapeRank_eq_zero α hα U]
    exact Guess.AllAtoms.atom (Or.inl hα)
  rcases α with _ | ⟨T, ℓ, h⟩ | ⟨T, ℓ⟩ | _ | _ | _ <;>
    simp only [Atom.shapeRank, not_true_eq_false] at hα <;>
    cases T <;> (try cases h) <;>
    simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, run_freshPath,
      FreshM.run_pure] <;>
    all_atoms <;> simp [Atom.shapeRank, TWE.Tree.size] <;> omega

theorem run_rewriteShapeAtom_mem_entriesRewritten (α : Atom Γ V) (U : TWE.Free V)
    (hα : α.EntriesRewritten) :
    ((rewriteShapeAtom α).run U).1.AllAtoms Atom.EntriesRewritten := by
  by_cases hrank : α.shapeRank = 0
  · rw [run_rewriteShapeAtom_of_shapeRank_eq_zero α hrank U]
    exact Guess.AllAtoms.atom hα
  rcases α with _ | ⟨T, ℓ, h⟩ | ⟨T, ℓ⟩ | _ | _ | _ <;>
    simp only [Atom.shapeRank, not_true_eq_false] at hrank <;>
    cases T <;> (try cases h) <;>
    simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, run_freshPath,
      FreshM.run_pure] <;>
    all_atoms <;> trivial

theorem allAtoms_updates_subset_rewriteShapeAtom (α : Atom Γ V) (U : TWE.Free V) :
    ((rewriteShapeAtom α).run U).1.AllAtoms (·.updates ⊆ α.updates) := by
  by_cases hrank : α.shapeRank = 0
  · rw [run_rewriteShapeAtom_of_shapeRank_eq_zero α hrank U]
    exact Guess.AllAtoms.atom (List.Subset.refl _)
  rcases α with _ | ⟨T, ℓ, h⟩ | ⟨T, ℓ⟩ | _ | _ | _ <;>
    simp only [Atom.shapeRank, not_true_eq_false] at hrank <;>
    cases T <;> (try cases h) <;>
    simp only [rewriteShapeAtom, FreshM.run_bind, run_freshName, run_freshPath,
      FreshM.run_pure] <;>
    all_atoms <;> intro a ha <;> simp_all [Atom.updates, TWE.Tree.updates]

theorem rewriteAtoms_rewriteShapeAtom_mem_updatesEliminated (β : Conj Γ V)
    (hβ : ∀ α ∈ β, α.EntriesRewritten) :
    (rewriteAtoms rewriteShapeAtom β).AllAtoms Atom.UpdatesEliminated := by
  intro γ hγ α hα
  have hentries := allAtoms_rewriteAtoms
    (fun α U ↦ run_rewriteShapeAtom_mem_entriesRewritten α U) β hβ γ hγ α hα
  have hrank := allAtoms_rank_eq_zero_rewriteAtoms Atom.shapeRank
    allAtoms_shapeRank_lt_rewriteShapeAtom β
    (fun α _ ↦ by cases α <;> simp [Atom.shapeRank, Atom.treeSize]) γ hγ α hα
  rcases α with _ | ⟨T, ℓ, h⟩ | ⟨T, ℓ⟩ | ⟨R, T, ℓ⟩ | _ | _ <;> (try cases T) <;>
    simp_all [Atom.shapeRank, Atom.EntriesRewritten, Atom.UpdatesEliminated, TWE.Tree.size]

end Rank

end ToWE

end Linear

end TWE

end Accordion

end
