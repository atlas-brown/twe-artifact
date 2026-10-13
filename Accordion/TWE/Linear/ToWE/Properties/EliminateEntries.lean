module

public import Accordion.TWE.Linear.ToWE.Properties.BaseTrees
public import Mathlib.Data.List.Sections

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open FileTree.Focus (follow shapeFollow entriesFollow follow_append)

variable {Γ : Type} {V : TWE.Vars}

section Run

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem run_eliminateEntries (source : Conj Γ V) (W : TWE.Free V) :
    ((eliminateEntries source).run W).1 =
      ((⋀ α ∈ source.filter (·.baseEntries?.isNone), (α : Guess (Conj Γ V))) ∧
        (endpointShapes source.baseEntries).flatMap fun hs ↦ ((entriesCase source hs).run W).1) :=
  rfl

theorem run_entriesCase (source : Conj Γ V) (hs : List TWE.Shape) (W : TWE.Free V) :
    ((entriesCase source hs).run W).1 =
      ((⋀ p ∈ source.baseEntries.zip hs, endpointRewrite p.1 p.2) ∧
        entriesFunctional source.baseEntries ∧
        ⋀ D ∈ (((caseDirectories source hs ×ˢ caseShapes source hs).mapM entriesLocation).run W).1,
          D) :=
  rfl

theorem subset_entriesLocationRewrite (e : BaseEntryObservation Γ V)
    (s : BaseShapeAssertion Γ V) (W : TWE.Free V) :
    W ⊆ ((entriesLocationRewrite e s).run W).2 := by
  simp only [entriesLocationRewrite, notPrefixFormula, FreshM.run_bind, run_freshName,
    run_freshPath, FreshM.run_pure]
  refine ⟨?_, subset_rfl, ?_, subset_rfl, subset_rfl, subset_rfl⟩ <;> intro x hx <;> simp [hx]

theorem subset_entriesLocation (p : BaseEntryObservation Γ V × BaseShapeAssertion Γ V)
    (W : TWE.Free V) : W ⊆ ((entriesLocation p).run W).2 := by
  unfold entriesLocation
  split
  · exact subset_entriesLocationRewrite _ _ W
  · exact Free.Subset.refl W

theorem free_entriesLocationRewrite_subset (e : BaseEntryObservation Γ V)
    (s : BaseShapeAssertion Γ V) {W : TWE.Free V} (he : Word.free e.query ⊆ W)
    (hs : Word.free s.query ⊆ W) (hR : e.set ∈ W.set) :
    Guess.AllAtoms (·.free ⊆ ((entriesLocationRewrite e s).run W).2)
      ((entriesLocationRewrite e s).run W).1 := by
  have hsub := subset_entriesLocationRewrite e s W
  have he := Free.Subset.trans he hsub
  have hs := Free.Subset.trans hs hsub
  simp only [entriesLocationRewrite, notPrefixFormula, FreshM.run_bind, run_freshName,
    run_freshPath, FreshM.run_pure] at he hs ⊢
  all_atoms
  all_goals
    simp only [Atom.free, WordFormula.free, WE.Word.append_eq, Word.free, SetAtom.free,
      SetTerm.free, TWE.Free.union_subset_iff, he, hs, true_and, and_true]
  all_goals
    simp [TWE.Name.toWord, TWE.Path.toWord, Word.free, TWE.Name.free, TWE.Free.subset_iff, hR]

end Run

theorem mem_endpointShapes (es : List (BaseEntryObservation Γ V)) (hs : List TWE.Shape) :
    hs ∈ endpointShapes es ↔ hs.length = es.length := by
  induction es generalizing hs with
  | nil => cases hs <;> simp [endpointShapes]
  | cons e es ih =>
      simp only [endpointShapes, Guess.mem_bind, Guess.mem_pure, mem_guess, ih]
      cases hs with
      | nil => simp
      | cons h hs => cases h <;> simp

section Free

variable [TWE.Vars.Comparable V] {β : Conj Γ V} {U : TWE.Free V}

theorem free_subset_of_mem_baseShapes (hβ : β.free ⊆ U) {s : BaseShapeAssertion Γ V}
    (hs : s ∈ β.baseShapes) :
    (TWE.Tree.var s.tree : TWE.Tree V).free ⊆ U ∧ Word.free s.query ⊆ U := by
  have h : (Atom.shape (.var s.tree) s.query s.shape : Atom Γ V).free ⊆ U :=
    Free.Subset.trans (Atom.free_subset_of_mem (Conj.mem_baseShapes.1 hs)) hβ
  exact TWE.Free.union_subset h

theorem free_subset_of_mem_baseEntries (hβ : β.free ⊆ U) {e : BaseEntryObservation Γ V}
    (he : e ∈ β.baseEntries) :
    (TWE.Tree.var e.tree : TWE.Tree V).free ⊆ U ∧ Word.free e.query ⊆ U ∧ e.set ∈ U.set := by
  have h : (Atom.entries e.set (.var e.tree) e.query : Atom Γ V).free ⊆ U :=
    Free.Subset.trans (Atom.free_subset_of_mem (Conj.mem_baseEntries.1 he)) hβ
  obtain ⟨hRT, hℓ⟩ := TWE.Free.union_subset h
  obtain ⟨hR, hT⟩ := TWE.Free.union_subset hRT
  exact ⟨hT, hℓ, hR.2.2.2.2.1 (Finset.mem_singleton_self _)⟩

theorem SetTerm.free_var_subset {x : V.Set} (hx : x ∈ U.set) :
    (SetTerm.var x : SetTerm Γ V).free ⊆ U := by
  simp [SetTerm.free, TWE.Free.subset_iff, hx]

end Free

theorem atom_cases_of_updatesEliminated {α : Atom Γ V} (hα : α.UpdatesEliminated) :
    (∃ F, α = .word F) ∨ (∃ s : BaseShapeAssertion Γ V, α = s.atom) ∨
      (∃ e : BaseEntryObservation Γ V, α = e.atom) ∨ ∃ a, α = .set a := by
  rcases α with F | ⟨_ | _, ℓ, h⟩ | _ | ⟨R, _ | _, ℓ⟩ | a | _ <;>
    simp [Atom.UpdatesEliminated] at hα
  exacts [Or.inl ⟨F, rfl⟩, Or.inr (Or.inl ⟨⟨_, ℓ, h⟩, rfl⟩),
    Or.inr (Or.inr (Or.inl ⟨⟨_, ℓ, R⟩, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨a, rfl⟩))]

theorem mem_caseDirectories {β : Conj Γ V} {hs : List TWE.Shape} {e : BaseEntryObservation Γ V} :
    e ∈ caseDirectories β hs ↔ (e, .dirc) ∈ β.baseEntries.zip hs := by
  simp [caseDirectories]

theorem forall_mem_caseShapes {P : BaseShapeAssertion Γ V → Prop} {β : Conj Γ V}
    {hs : List TWE.Shape} (hshapes : ∀ s ∈ β.baseShapes, P s)
    (hends : ∀ p ∈ β.baseEntries.zip hs, P ⟨p.1.tree, p.1.query, p.2⟩) :
    ∀ s ∈ caseShapes β hs, P s := by
  intro s hmem
  rcases List.mem_append.1 hmem with hmem | hmem
  · exact hshapes s hmem
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmem
    exact hends p hp

theorem directoryRelation_iff (ℓ ℓ' : List Γ) (R : Finset Γ) (h : TWE.Shape) :
    DirectoryRelation ℓ ℓ' R h ↔ ℓ' = ℓ ∨ ¬ℓ <+: ℓ' ∨
      (∃ A, ℓ' = ℓ ++ [A] ∧ (A ∈ R ↔ h ≠ .absent)) ∨
      ∃ B B' K, ℓ' = ℓ ++ [B] ++ [B'] ++ K ∧ B ∈ R := by
  constructor
  · intro hrel
    by_cases hprefix : ℓ <+: ℓ'
    · obtain ⟨_ | ⟨A, _ | ⟨B', K⟩⟩, rfl⟩ := hprefix
      · simp
      · exact Or.inr (Or.inr (Or.inl ⟨A, rfl, by simpa using hrel A [] rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨A, B', K, by simp, (hrel A _ rfl).2 (by simp)⟩))
    · exact Or.inr (Or.inl hprefix)
  · rintro (rfl | hprefix | ⟨A, rfl, hA⟩ | ⟨B, B', K, rfl, hB⟩) A' K' heq
    · simp at heq
    · exact absurd ⟨_, heq.symm⟩ hprefix
    · simp only [List.append_cancel_left_eq, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simpa using hA
    · simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simpa using hB

section Observations

variable [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)

theorem exists_shape_of_observesEntries {w : List Γ} {R : Finset Γ}
    (hR : ObservesEntries m T w R) : ∃ h, ObservesShape m T w h ∧ (h ≠ .dirc → R = ∅) := by
  obtain ⟨f, hf, hR⟩ := hR
  cases hfollow : follow f w with
  | none => simp [entriesFollow, hfollow] at hR
  | some g =>
      refine ⟨g.shape, ⟨f, hf, by simp [shapeFollow, hfollow]⟩, fun hg ↦ ?_⟩
      rcases g with (_ | _) | _ <;>
        simp_all [entriesFollow, FileTree.Focus.entryNames, FileTree.Focus.shape]

theorem observesEntries_of_observesShape {w : List Γ} {h : TWE.Shape}
    (hh : ObservesShape m T w h) (hdirc : h ≠ .dirc) : ObservesEntries m T w ∅ := by
  obtain ⟨f, hf, hh⟩ := hh
  refine ⟨f, hf, ?_⟩
  cases hfollow : follow f w with
  | none => simp [shapeFollow, hfollow] at hh
  | some g =>
      rcases g with (_ | _) | _ <;>
        simp_all [shapeFollow, entriesFollow, FileTree.Focus.entryNames, FileTree.Focus.shape]

theorem directoryRelation_of_observes [Std.LawfulEqOrd Γ] {ℓ ℓ' : List Γ} {R : Finset Γ}
    {h : TWE.Shape} (hR : ObservesEntries m T ℓ R) (hh : ObservesShape m T ℓ' h) :
    DirectoryRelation ℓ ℓ' R h := by
  rintro A K rfl
  obtain ⟨f, hf, hR⟩ := hR
  obtain ⟨f', hf', hh⟩ := hh
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  simp only [entriesFollow, shapeFollow, follow_append, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at hR hh
  obtain ⟨g, hg, rfl⟩ := hR
  obtain ⟨g', ⟨g'', hg'', hfollow⟩, rfl⟩ := hh
  obtain rfl := Option.some.inj (hg.symm.trans hg'')
  rcases g with (_ | entries) | _ <;> try simp [follow] at hfollow
  rw [FileTree.Focus.entryNames, FileTree.Entries.mem_dom_iff,
    FileTree.Entries.mem_iff_lookup_isSome]
  cases hlookup : entries.lookup A <;> rcases K with _ | ⟨_, _⟩ <;> simp_all [follow] <;>
    subst g'
  · rfl
  · cases ‹FileTree Γ› <;> simp [FileTree.Focus.shape]

end Observations

section Parts

variable [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V)

theorem sat_endpointRewrite_iff (e : BaseEntryObservation Γ V) (h : TWE.Shape) :
    Guess.sat m (endpointRewrite e h) ↔
      ObservesShape m (.var e.tree) (m.toWE.evalWord e.query) h ∧
        (h ≠ .dirc → m.σSet e.set = ∅) := by
  unfold endpointRewrite
  split <;> simp [Atom.sat, SetAtom.sat, SetTerm.eval, *]

variable [TWE.Vars.Comparable V]

theorem sat_entriesFunctional_iff (es : List (BaseEntryObservation Γ V)) :
    Guess.sat m (entriesFunctional es) ↔
      ∀ p ∈ es ×ˢ es, p.1.tree = p.2.tree →
        m.toWE.evalWord p.1.query = m.toWE.evalWord p.2.query →
          m.σSet p.1.set = m.σSet p.2.set := by
  simp only [entriesFunctional, Guess.sat_all]
  refine forall₂_congr fun p _ ↦ ?_
  split <;> simp [Atom.sat, SetAtom.sat, SetTerm.eval, *, imp_iff_not_or]

variable [TWE.Vars.Fresh V]

theorem satFresh_entriesLocationRewrite_iff {U W : TWE.Free V} (hUW : U ⊆ W)
    (e : BaseEntryObservation Γ V) (s : BaseShapeAssertion Γ V)
    (he : Word.free e.query ⊆ U) (hs : Word.free s.query ⊆ U) (hR : e.set ∈ U.set) :
    Guess.satFresh m U ((entriesLocationRewrite e s).run W).1 ↔
      DirectoryRelation (m.toWE.evalWord e.query) (m.toWE.evalWord s.query) (m.σSet e.set)
        s.shape := by
  let A : V.Name := Fresh.fresh W.name
  let B : V.Name := Fresh.fresh (insert A W.name)
  let B' : V.Name := Fresh.fresh (insert B (insert A W.name))
  let L : V.Path := Fresh.fresh W.path
  let W₄ : TWE.Free V :=
    { W with name := insert B' (insert B (insert A W.name)), path := insert L W.path }
  have hUW₄ : U ⊆ W₄ := Free.Subset.trans hUW
    ⟨fun x hx ↦ by simp [W₄, hx], subset_rfl, Finset.subset_insert _ _, subset_rfl, subset_rfl,
      subset_rfl⟩
  have hA : A ∉ U.name := Fresh.fresh_notMem_of_subset hUW.1
  have hB : B ∉ U.name := Fresh.fresh_notMem_of_subset (hUW.1.trans (Finset.subset_insert _ _))
  have hB' : B' ∉ U.name := Fresh.fresh_notMem_of_subset
    (hUW.1.trans ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
  have hL : L ∉ U.path := Fresh.fresh_notMem_of_subset hUW.2.2.1
  have hBB' : B ≠ B' := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
  have hsat : ∀ m' : WordModel Γ V, Guess.sat m' ((entriesLocationRewrite e s).run W).1 ↔
      m'.toWE.evalWord s.query = m'.toWE.evalWord e.query ∨
      m'.toWE ⊨ ((e.query ⋠ s.query).run W₄).1 ∨
      (m'.toWE.evalWord s.query = m'.toWE.evalWord e.query ++ [m'.σName A] ∧
        (m'.σName A ∈ m'.σSet e.set ↔ s.shape ≠ .absent)) ∨
      (m'.toWE.evalWord s.query =
          m'.toWE.evalWord e.query ++ [m'.σName B] ++ [m'.σName B'] ++ m'.σPath L ∧
        m'.σName B ∈ m'.σSet e.set) := by
    intro m'
    change Guess.sat m' (s.query ≐ e.query ∨ ⌜((e.query ⋠ s.query).run W₄).1⌝ ∨
      s.query ≐ e.query ++ A ∧ (if s.shape = .absent then A ∉̇ e.set else A ∈̇ e.set) ∨
      s.query ≐ e.query ++ B ++ B' ++ L ∧ B ∈̇ e.set) ↔ _
    simp only [Guess.sat_or, Guess.sat_and, InjectAtom.inject_guess, Guess.sat_atom, Atom.sat,
      Formula.sat, WE.Model.sat_wordEq_iff, WE.Model.evalWord_append, evalWord_nameVar,
      evalWord_pathVar]
    cases s.shape <;>
      simp [Atom.sat, SetAtom.sat, SetTerm.eval, TWE.Model.evalName, WordModel.toTWE]
  rw [directoryRelation_iff]
  constructor
  · rintro ⟨m', hm, hD⟩
    have hq : m.σSet e.set = m'.σSet e.set := hm.2.2.2.2.1 (Finset.mem_coe.2 hR)
    rcases (hsat m').1 hD with h | h | ⟨h, hA'⟩ | ⟨h, hB''⟩
    · exact .inl (by rwa [evalWord_congr hm he, evalWord_congr hm hs])
    · exact .inr (.inl (by
        simpa only [evalWord_congr hm he, evalWord_congr hm hs] using
          not_prefix_of_sat_notPrefixFormula _ _ _ _ h))
    · exact .inr (.inr (.inl ⟨m'.σName A,
        by rwa [evalWord_congr hm he, evalWord_congr hm hs], by rwa [hq]⟩))
    · exact .inr (.inr (.inr ⟨m'.σName B, m'.σName B', m'.σPath L,
        by rwa [evalWord_congr hm he, evalWord_congr hm hs], by rwa [hq]⟩))
  · rintro (h | h | ⟨a, h, ha⟩ | ⟨b, b', K, h, hb⟩)
    · exact ⟨m, .refl m U, (hsat m).2 (.inl h)⟩
    · obtain ⟨m', hm, h⟩ := (exists_sat_notPrefixFormula_iff m hUW₄ he hs).2 h
      exact ⟨m', hm, (hsat m').2 (.inr (.inl h))⟩
    · have hm : m ≡[U] m.setName A a := WordModel.congr_setName hA
      refine ⟨_, hm, (hsat _).2 (.inr (.inr (.inl ?_)))⟩
      rw [← evalWord_congr hm he, ← evalWord_congr hm hs]
      simpa using And.intro h ha
    · let m' := ((m.setName B b).setName B' b').setPath L K
      have hm : m ≡[U] m' :=
        ((WordModel.congr_setName hB).trans (WordModel.congr_setName hB')).trans
          (WordModel.congr_setPath hL)
      refine ⟨m', hm, (hsat m').2 (.inr (.inr (.inr ?_)))⟩
      rw [← evalWord_congr hm he, ← evalWord_congr hm hs]
      simpa [m', hBB'] using And.intro h hb

end Parts

section Case

variable [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]

theorem satFresh_entriesCase_iff [TWE.Vars.Fresh V] (m : WordModel Γ V) (source : Conj Γ V)
    {U W : TWE.Free V} (hsource : source.free ⊆ U) (hUW : U ⊆ W) (hs : List TWE.Shape) :
    Guess.satFresh m U ((entriesCase source hs).run W).1 ↔ EntriesCaseHolds m source hs := by
  have hentries := fun e (he : e ∈ source.baseEntries) ↦
    free_subset_of_mem_baseEntries hsource he
  have hendpoints : Guess.AllAtoms (·.free ⊆ U)
      (⋀ p ∈ source.baseEntries.zip hs, endpointRewrite p.1 p.2) := by
    refine Guess.AllAtoms.all fun p hp ↦ ?_
    obtain ⟨hT, hℓ, hR⟩ := hentries p.1 (List.of_mem_zip hp).1
    unfold endpointRewrite
    split
    · exact Guess.AllAtoms.and
        (Guess.AllAtoms.inject (TWE.Free.union_subset_iff.2 ⟨hT, hℓ⟩)) Guess.AllAtoms.top
    · exact Guess.AllAtoms.and (Guess.AllAtoms.inject (TWE.Free.union_subset_iff.2 ⟨hT, hℓ⟩))
        (Guess.AllAtoms.inject (TWE.Free.union_subset_iff.2
          ⟨SetTerm.free_var_subset hR, TWE.Free.empty_subset U⟩))
  have hfunctional : Guess.AllAtoms (·.free ⊆ U) (entriesFunctional source.baseEntries) := by
    refine Guess.AllAtoms.all fun p hp ↦ ?_
    obtain ⟨h₁, h₂⟩ := List.mem_product.1 hp
    obtain ⟨-, hℓ₁, hR₁⟩ := hentries _ h₁
    obtain ⟨-, hℓ₂, hR₂⟩ := hentries _ h₂
    split
    · exact Guess.AllAtoms.or (Guess.AllAtoms.inject (TWE.Free.union_subset_iff.2 ⟨hℓ₁, hℓ₂⟩))
        (Guess.AllAtoms.inject (TWE.Free.union_subset_iff.2
          ⟨SetTerm.free_var_subset hR₁, SetTerm.free_var_subset hR₂⟩))
    · exact Guess.AllAtoms.top
  have hpairs : ∀ p ∈ caseDirectories source hs ×ˢ caseShapes source hs,
      Word.free p.1.query ⊆ U ∧ p.1.set ∈ U.set ∧ Word.free p.2.query ⊆ U := fun p hp ↦
    have he := hentries _ (List.of_mem_zip (mem_caseDirectories.1 (List.mem_product.1 hp).1)).1
    ⟨he.2.1, he.2.2, forall_mem_caseShapes (P := fun s ↦ Word.free s.query ⊆ U)
      (fun s hs ↦ (free_subset_of_mem_baseShapes hsource hs).2)
      (fun p hp ↦ (hentries _ (List.of_mem_zip hp).1).2.1) _ (List.mem_product.1 hp).2⟩
  rw [run_entriesCase, Guess.satFresh_and_of_free_subset hendpoints,
    Guess.satFresh_and_of_free_subset hfunctional]
  simp only [Guess.sat_all, sat_endpointRewrite_iff, sat_entriesFunctional_iff, EntriesCaseHolds]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  refine Guess.satFresh_mapM_iff (fun D ↦ D) entriesLocation
    (fun m p ↦ p.1.tree = p.2.tree → DirectoryRelation (m.toWE.evalWord p.1.query)
      (m.toWE.evalWord p.2.query) (m.σSet p.1.set) p.2.shape)
    subset_entriesLocation (U₀ := U) (fun p hp W hW ↦ ?_) (fun p hp {U' W'} m' hU' hW' ↦ ?_) m
    (Free.Subset.refl U) hUW <;> obtain ⟨he, hR, hs'⟩ := hpairs p hp <;> unfold entriesLocation
  · split
    · exact free_entriesLocationRewrite_subset p.1 p.2 (Free.Subset.trans he hW)
        (Free.Subset.trans hs' hW) (hW.2.2.2.2.1 hR)
    · exact Guess.AllAtoms.top
  · split
    · next htree =>
      rw [satFresh_entriesLocationRewrite_iff m' hW' p.1 p.2 (Free.Subset.trans he hU')
        (Free.Subset.trans hs' hU') (hU'.2.2.2.2.1 hR)]
      simp [htree]
    · next htree =>
      exact iff_of_true (Guess.satFresh_of_sat (by simp)) fun h ↦ absurd h htree

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem exists_withTrees_sat_of_entriesCaseHolds (m : WordModel Γ V) (source : Conj Γ V)
    (hs : List TWE.Shape) (hlength : hs.length = source.baseEntries.length)
    (hshapes : ∀ s ∈ source.baseShapes,
      ObservesShape m (.var s.tree) (m.toWE.evalWord s.query) s.shape)
    (hcase : EntriesCaseHolds m source hs) :
    ∃ θ, (∀ s ∈ caseShapes source hs, ObservesShape (m.withTrees θ) (.var s.tree)
        (m.toWE.evalWord s.query) s.shape) ∧
      ∀ e ∈ source.baseEntries, ObservesEntries (m.withTrees θ) (.var e.tree)
        (m.toWE.evalWord e.query) (m.σSet e.set) := by
  obtain ⟨hends, hfunctional, hrelations⟩ := hcase
  let ev := fun w : Word Γ V ↦ m.toWE.evalWord w
  let shapes := caseShapes source hs
  let directories : List (GroundTreeDirectoryObservation Γ V.Tree) :=
    (caseDirectories source hs).map fun e ↦ ⟨e.tree, ev e.query, m.σSet e.set⟩
  have hground := (baseTreeRealisation_iff m shapes).1
    ⟨m.θ, forall_mem_caseShapes hshapes fun p hp ↦ (hends p hp).1⟩
  obtain ⟨θ, hθshapes, hθdirectories⟩ :=
    groundShapesDirectories_realisable (evalBaseShapeAssertions m shapes) directories
    { shapesFunctional := hground.1
      shapesLeafCompatible := hground.2
      directoriesFunctional := by
        simp only [GroundDirectoriesFunctional, directories, List.forall_mem_map]
        exact fun e he e' he' ↦ hfunctional (e, e') (List.mem_product.2
          ⟨(List.of_mem_zip (mem_caseDirectories.1 he)).1,
            (List.of_mem_zip (mem_caseDirectories.1 he')).1⟩)
      endpointsObserved := by
        simp only [GroundDirectoryEndpointsObserved, directories, List.forall_mem_map]
        exact fun e he ↦ List.mem_map.2 ⟨⟨e.tree, e.query, .dirc⟩,
          List.mem_append_right _ (List.mem_map.2 ⟨_, mem_caseDirectories.1 he, rfl⟩), rfl⟩
      shapesCompatible := by
        simp only [GroundDirectoryShapesCompatible, directories, evalBaseShapeAssertions,
          List.forall_mem_map]
        exact fun e he s hs ↦ hrelations (e, s) (List.mem_product.2 ⟨he, hs⟩) }
  have hθ : ∀ s ∈ shapes, ObservesShape (m.withTrees θ) (.var s.tree) (ev s.query) s.shape :=
    fun s hs ↦ (observesShape_var_withTrees m θ _ _ _).2
      (hθshapes _ (List.mem_map_of_mem (f := fun s ↦ _) hs))
  refine ⟨θ, hθ, fun e he ↦ ?_⟩
  obtain ⟨⟨e, h⟩, hp, rfl⟩ : ∃ p ∈ source.baseEntries.zip hs, p.1 = e := by
    rw [← List.map_fst_zip (l₁ := source.baseEntries) (l₂ := hs) (by omega)] at he
    simpa using he
  by_cases hdirc : h = .dirc
  · subst hdirc
    have := hθdirectories _ (List.mem_map_of_mem (f := fun e ↦ _) (mem_caseDirectories.2 hp))
    simpa [ObservesEntries, WordModel.withTrees, TWE.Model.evalTree, WordModel.toTWE] using this
  · rw [(hends _ hp).2 hdirc]
    exact observesEntries_of_observesShape _ _
      (hθ ⟨e.tree, e.query, h⟩ (List.mem_append_right _ (List.mem_map_of_mem hp))) hdirc

end Case

theorem run_eliminateEntries_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (β : Conj Γ V) (hβ : ∀ α ∈ β, α.UpdatesEliminated) {W : TWE.Free V} (hW : β.free ⊆ W) :
    Guess.SAT ((eliminateEntries β).run W).1 ↔ β.SAT := by
  have hrest : ∀ α ∈ β.filter (·.baseEntries?.isNone), α ∈ β := fun α hα ↦
    (List.mem_filter.1 hα).1
  simp only [run_eliminateEntries, Guess.SAT, Conj.SAT, Guess.sat_and, Guess.sat_all,
    Guess.sat_flatMap, InjectAtom.inject_guess, Guess.sat_atom]
  constructor
  · rintro ⟨m, hrestSat, hs, hhs, hDsat⟩
    have hcase := (satFresh_entriesCase_iff m β hW (Free.Subset.refl W) hs).1
      (Guess.satFresh_of_sat hDsat)
    have hkept : ∀ α ∈ β, α.baseEntries? = none → α.sat m := fun α hα hnone ↦
      hrestSat α (List.mem_filter.2 ⟨hα, by simp [hnone]⟩)
    obtain ⟨θ, hshapes, hentries⟩ := exists_withTrees_sat_of_entriesCaseHolds m β hs
      ((mem_endpointShapes _ _).1 hhs)
      (fun s hs ↦ hkept s.atom (Conj.mem_baseShapes.1 hs) rfl) hcase
    refine ⟨m.withTrees θ, fun α hα ↦ ?_⟩
    rcases atom_cases_of_updatesEliminated (hβ α hα) with ⟨F, rfl⟩ | ⟨s, rfl⟩ | ⟨e, rfl⟩ |
      ⟨a, rfl⟩
    · exact hkept _ hα rfl
    · exact hshapes s (List.mem_append_left _ (Conj.mem_baseShapes.2 hα))
    · exact hentries e (Conj.mem_baseEntries.2 hα)
    · exact (SetAtom.sat_withTrees m θ a).2 (hkept _ hα rfl)
  · rintro ⟨m, hsat⟩
    have hentries : ∀ e ∈ β.baseEntries, ObservesEntries m (.var e.tree)
        (m.toWE.evalWord e.query) (m.σSet e.set) := fun e he ↦
      hsat _ (Conj.mem_baseEntries.1 he)
    have : Nonempty TWE.Shape := ⟨.file⟩
    choose! shape hshape using fun e he ↦ exists_shape_of_observesEntries m _ (hentries e he)
    have hzip : β.baseEntries.zip (β.baseEntries.map shape) =
        β.baseEntries.map fun e ↦ (e, shape e) := by
      simpa using List.zip_map' (f := id) (g := shape) (l := β.baseEntries)
    have hcase : EntriesCaseHolds m β (β.baseEntries.map shape) := by
      refine ⟨by simpa [hzip] using hshape, ?_, ?_⟩
      · rintro ⟨e, e'⟩ hp (htree : e.tree = e'.tree)
          (hquery : m.toWE.evalWord e.query = m.toWE.evalWord e'.query)
        obtain ⟨he, he'⟩ := List.mem_product.1 hp
        obtain ⟨f, hf, hR⟩ := hentries e he
        obtain ⟨f', hf', hR'⟩ := hentries e' he'
        rw [← htree] at hf'
        rw [← hquery] at hR'
        obtain rfl := Option.some.inj (hf.symm.trans hf')
        exact Option.some.inj (hR.symm.trans hR')
      · have hshapes : ∀ s ∈ caseShapes β (β.baseEntries.map shape), ObservesShape m
            (.var s.tree) (m.toWE.evalWord s.query) s.shape :=
          forall_mem_caseShapes (fun s hs ↦ hsat _ (Conj.mem_baseShapes.1 hs))
            (by simpa [hzip] using fun e he ↦ (hshape e he).1)
        rintro ⟨e, s⟩ hp (htree : e.tree = s.tree)
        obtain ⟨he, hs⟩ := List.mem_product.1 hp
        exact directoryRelation_of_observes m _
          (hentries _ (List.of_mem_zip (mem_caseDirectories.1 he)).1) (htree ▸ hshapes s hs)
    obtain ⟨m', hm, hcaseSat⟩ :=
      (satFresh_entriesCase_iff m β hW (Free.Subset.refl W) _).2 hcase
    exact ⟨m', fun α hα ↦ (Atom.sat_congr hm (Free.Subset.trans
      (Atom.free_subset_of_mem (hrest α hα)) hW)).1 (hsat α (hrest α hα)), _,
      (mem_endpointShapes _ _).2 (List.length_map _), hcaseSat⟩

theorem run_eliminateEntries_mem_entriesEliminated [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (β : Conj Γ V) (hβ : ∀ α ∈ β, α.UpdatesEliminated) (W : TWE.Free V) :
    Guess.AllAtoms Atom.EntriesEliminated ((eliminateEntries β).run W).1 := by
  rw [run_eliminateEntries]
  refine Guess.AllAtoms.and (Guess.AllAtoms.all fun α hα ↦ Guess.AllAtoms.inject ?_)
    (Guess.AllAtoms.flatMap fun hs _ ↦ ?_)
  · obtain ⟨hα, hnone⟩ := List.mem_filter.1 hα
    have := hβ α hα
    rcases α with _ | ⟨_ | _, _, _⟩ | _ | ⟨_, _ | _, _⟩ | _ | _ <;>
      simp_all [Atom.UpdatesEliminated, Atom.EntriesEliminated, Atom.baseEntries?]
  obtain ⟨hlocations, -⟩ := FreshM.run_mapM entriesLocation subset_entriesLocation
    (caseDirectories β hs ×ˢ caseShapes β hs) W
  rw [run_entriesCase]
  refine Guess.AllAtoms.and (Guess.AllAtoms.all fun p _ ↦ ?_)
    (Guess.AllAtoms.and ?_ (Guess.AllAtoms.all fun D hD ↦ ?_))
  · unfold endpointRewrite
    all_atoms <;> trivial
  · unfold entriesFunctional
    all_atoms <;> trivial
  · obtain ⟨p, -, W'', -, rfl⟩ := hlocations D hD
    unfold entriesLocation
    split
    · simp only [entriesLocationRewrite, FreshM.run_bind, run_freshName, run_freshPath,
        FreshM.run_pure]
      all_atoms <;> trivial
    · exact Guess.AllAtoms.top

end ToWE

end Linear

end TWE

end Accordion

end
