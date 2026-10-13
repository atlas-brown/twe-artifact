module

public import Accordion.TWE.Linear.ToWE.Properties.Trees

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open FileTree.Focus (follow shapeFollow entriesFollow)

variable {Γ : Type} {V : TWE.Vars}

section Build

variable {observations : List (GroundShapeObservation Γ)} {h : TWE.Shape}

theorem mem_of_rootShape_eq_some (hroot : rootShape observations = some h) :
    ([], h) ∈ observations := by
  obtain ⟨⟨w, k⟩, hfind, rfl⟩ := Option.map_eq_some_iff.1 hroot
  have hw : w = [] := by simpa using List.find?_some hfind
  exact hw ▸ List.mem_of_find?_eq_some hfind

theorem notMem_of_rootShape_eq_none (hroot : rootShape observations = none) :
    ([], h) ∉ observations :=
  fun hmem ↦ by simpa using List.find?_eq_none.1 (Option.map_eq_none_iff.1 hroot) _ hmem

theorem mem_observationHeads {a : Γ} :
    a ∈ observationHeads observations ↔ ∃ w h, (a :: w, h) ∈ observations := by
  simp only [observationHeads, List.mem_filterMap, List.head?_eq_some_iff]
  constructor
  · rintro ⟨⟨_, h⟩, hmem, w, rfl⟩
    exact ⟨w, h, hmem⟩
  · rintro ⟨w, h, hmem⟩
    exact ⟨_, hmem, w, rfl⟩

@[simp] theorem mem_childObservations [DecidableEq Γ] {a : Γ} {w : List Γ} :
    (w, h) ∈ childObservations a observations ↔ (a :: w, h) ∈ observations := by
  simp only [childObservations, List.mem_filterMap]
  constructor
  · rintro ⟨⟨_ | ⟨b, u⟩, k⟩, hmem, he⟩
    · simp at he
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact hmem
  · exact fun hmem ↦ ⟨_, hmem, by simp⟩

theorem forced_cons [DecidableEq Γ] {a : Γ} {w : List Γ} :
    Forced observations (a :: w) ↔ Forced (childObservations a observations) w := by
  simp [Forced]

theorem buildShapeFocus_nil [Ord Γ] [DecidableEq Γ] (fuel : Nat) :
    buildShapeFocus fuel ([] : List (GroundShapeObservation Γ)) = .abst := by
  cases fuel <;> simp [buildShapeFocus, rootShape, observationHeads]

private theorem dlookup_filterMap [DecidableEq Γ] {β : Type} (heads : List Γ) (f : Γ → Option β)
    (a : Γ) :
    (heads.filterMap fun b ↦ (f b).map (⟨b, ·⟩)).dlookup a = if a ∈ heads then f a else none := by
  induction heads with
  | nil => rfl
  | cons b heads ih =>
      by_cases hab : a = b
      · subst hab
        cases hf : f a <;> simp [hf, ih, List.dlookup_cons_eq]
      · cases hf : f b <;> simp [hf, ih, List.dlookup_cons_ne, hab]

variable [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]

theorem follow_buildShapeFocus_cons {fuel : Nat} {a : Γ} {w : List Γ}
    (hroot : rootShape observations = none ∨ rootShape observations = some .dirc)
    (hdirc : rootShape observations = some .dirc ∨ observationHeads observations ≠ []) :
    follow (buildShapeFocus (fuel + 1) observations) (a :: w) =
      follow (buildShapeFocus fuel (childObservations a observations)) w := by
  have hchild : ∀ δ : FileTree.Entries Γ (FileTree Γ),
      δ.lookup a = FileTree.Focus.tree? (buildShapeFocus fuel (childObservations a observations)) →
        follow (.tree (.dirc δ)) (a :: w) =
          follow (buildShapeFocus fuel (childObservations a observations)) w := by
    intro δ hδ
    rcases hb : buildShapeFocus fuel (childObservations a observations) <;>
      simp_all [follow, FileTree.Focus.tree?]
  have hnil (ha : a ∉ observationHeads observations) : childObservations a observations = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun ⟨u, k⟩ hu ↦
      ha (mem_observationHeads.2 ⟨u, k, mem_childObservations.1 hu⟩)
  rcases hroot with hroot | hroot <;> simp only [buildShapeFocus, hroot] <;>
    rw [ite_eq_left (by simp_all)] <;>
    refine hchild _ ?_ <;>
    rw [FileTree.Entries.lookup_ofSigmas, dlookup_filterMap] <;>
    split_ifs with ha <;> simp [hnil, ha, buildShapeFocus_nil, FileTree.Focus.tree?]

theorem buildShapeFocus_spec {fuel : Nat}
    (hfunctional : ShapeFunctional observations) (hleaf : ShapeLeafCompatible observations)
    (hbounded : ∀ w h, (w, h) ∈ observations → w.length < fuel) (w : List Γ) :
    (∀ h, (w, h) ∈ observations → shapeFollow (buildShapeFocus fuel observations) w = some h) ∧
      ((∃ T, follow (buildShapeFocus fuel observations) w = some (.tree T)) ↔
        Forced observations w) := by
  induction fuel generalizing observations w with
  | zero =>
      obtain rfl : observations = [] := List.eq_nil_iff_forall_not_mem.2
        fun ⟨u, k⟩ hu ↦ Nat.not_lt_zero _ (hbounded u k hu)
      cases w <;> simp [buildShapeFocus, Forced, follow]
  | succ fuel ih =>
      have hbelow : ∀ k, rootShape observations = some k → k ≠ .dirc →
          ∀ u s h, (u ++ s, h) ∈ observations → s = [] := by
        intro k hroot hk u s h hmem
        by_contra hs
        exact hleaf [] k (mem_of_rootShape_eq_some hroot) hk _ h hmem
          ⟨List.nil_prefix, by simp [hs]⟩
      cases w with
      | nil =>
          rcases hroot : rootShape observations with _ | ((_ | _ | _))
          · have hheads : observationHeads observations ≠ [] ↔ Forced observations [] := by
              simp only [ne_eq, List.eq_nil_iff_forall_not_mem, not_forall, not_not,
                mem_observationHeads, Forced]
              constructor
              · rintro ⟨a, w, h, hmem⟩
                exact ⟨a :: w, h, by simpa using hmem, by simp⟩
              · rintro ⟨_ | ⟨a, w⟩, h, hmem, -⟩
                · exact absurd hmem (notMem_of_rootShape_eq_none hroot)
                · exact ⟨a, w, h, by simpa using hmem⟩
            refine ⟨fun h hmem ↦ absurd hmem (notMem_of_rootShape_eq_none hroot), ?_⟩
            rw [← hheads]
            by_cases hnil : observationHeads observations = [] <;>
              simp [buildShapeFocus, hroot, hnil, follow]
          all_goals
            have hk := mem_of_rootShape_eq_some hroot
            refine ⟨fun h hmem ↦ by simp [buildShapeFocus, hroot, shapeFollow, follow,
              FileTree.Focus.shape, hfunctional _ _ _ hmem hk], ?_⟩
          · simp only [buildShapeFocus, hroot, follow, Option.some.injEq, reduceCtorEq,
              exists_false, false_iff]
            rintro ⟨s, h, hmem, hs⟩
            obtain rfl := hbelow _ hroot (by simp) [] s h hmem
            simp [hfunctional _ _ _ hmem hk] at hs
          all_goals
            exact iff_of_true (by simp [buildShapeFocus, hroot, follow])
              ⟨[], _, by simpa using hk, by simp⟩
      | cons a w =>
          have hchild := @ih (childObservations a observations)
            (fun u h k hh hk ↦ hfunctional (a :: u) h k (by simpa using hh) (by simpa using hk))
            (fun u h hh hd q k hq hpre ↦ hleaf (a :: u) h (by simpa using hh) hd (a :: q) k
              (by simpa using hq) (by simpa [List.cons_prefix_cons] using hpre))
            (fun u h hu ↦ Nat.lt_of_succ_lt_succ (hbounded (a :: u) h (by simpa using hu))) w
          simp only [mem_childObservations, ← forced_cons] at hchild
          rcases hroot : rootShape observations with _ | ((_ | _ | _))
          · by_cases hnil : observationHeads observations = []
            · have hnone : ∀ u h, (a :: u, h) ∉ observations := fun u h hmem ↦
                List.not_mem_nil (hnil ▸ mem_observationHeads.2 ⟨u, h, hmem⟩)
              refine ⟨fun h hmem ↦ absurd hmem (hnone _ _), ?_⟩
              simp [buildShapeFocus, hroot, hnil, follow, Forced, hnone]
            · rwa [follow_buildShapeFocus_cons (Or.inl hroot) (Or.inr hnil), shapeFollow,
                follow_buildShapeFocus_cons (Or.inl hroot) (Or.inr hnil)]
          all_goals first
            | rwa [shapeFollow, follow_buildShapeFocus_cons (Or.inr hroot) (Or.inl hroot)]
            | have hnone : ∀ u h, (a :: u, h) ∉ observations := fun u h hmem ↦
                  List.cons_ne_nil a u (hbelow _ hroot (by simp) [] _ h hmem)
              refine ⟨fun h hmem ↦ absurd hmem (hnone _ _), ?_⟩
              simp [buildShapeFocus, hroot, follow, Forced, hnone]

end Build

theorem buildShapeFocus_canonical [Ord Γ] [Std.TransOrd Γ] [DecidableEq Γ]
    (fuel : Nat) (observations : List (GroundShapeObservation Γ)) :
    (buildShapeFocus fuel observations).Canonical := by
  induction fuel generalizing observations with
  | zero => trivial
  | succ fuel ih =>
      simp only [buildShapeFocus]
      split
      · trivial
      · exact .file
      · split
        · refine FileTree.canonical_dirc_ofSigmas _ fun child hchild ↦ ?_
          obtain ⟨a, -, hchild⟩ := List.mem_filterMap.1 hchild
          have := ih (childObservations a observations)
          rcases hb : buildShapeFocus fuel (childObservations a observations) <;>
            simp_all [FileTree.Focus.tree?]
          exact hchild ▸ this
        · trivial

theorem length_lt_observationFuel {observations : List (GroundShapeObservation Γ)} {w : List Γ}
    {h : TWE.Shape} (hmem : (w, h) ∈ observations) : w.length < observationFuel observations := by
  induction observations with
  | nil => simp at hmem
  | cons o observations ih =>
      simp only [observationFuel, List.map_cons, List.sum_cons] at ih ⊢
      rcases List.mem_cons.1 hmem with rfl | hmem
      · dsimp only
        omega
      · have := ih hmem
        omega

theorem exists_realising_focus [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    {shapes : List (GroundShapeObservation Γ)} {directories : List (GroundDirectoryObservation Γ)}
    (hfunctional : ShapeFunctional shapes) (hleaf : ShapeLeafCompatible shapes)
    (hdirFunctional : ∀ w N N', (w, N) ∈ directories → (w, N') ∈ directories → N = N')
    (hendpoints : ∀ w N, (w, N) ∈ directories → (w, .dirc) ∈ shapes)
    (hcompatible : ∀ w N, (w, N) ∈ directories → ∀ a s h, (w ++ a :: s, h) ∈ shapes →
      (a ∈ N ↔ s ≠ [] ∨ h ≠ .absent)) :
    ∃ f : FileTree.Focus Γ, f.Canonical ∧
      (∀ w h, (w, h) ∈ shapes → shapeFollow f w = some h) ∧
      ∀ w N, (w, N) ∈ directories → entriesFollow f w = some N := by
  classical
  obtain ⟨completed, hcompleted⟩ : ∃ completed : List (GroundShapeObservation Γ), ∀ o,
      o ∈ completed ↔ o ∈ shapes ∨
        ∃ w N, (w, N) ∈ directories ∧ ∃ a ∈ N, (¬∃ o ∈ shapes, w ++ [a] <+: o.1) ∧
          o = (w ++ [a], .file) := by
    refine ⟨shapes ++ directories.flatMap fun d ↦ d.2.toList.filterMap fun a ↦
      if ∃ o ∈ shapes, d.1 ++ [a] <+: o.1 then none else some (d.1 ++ [a], .file), fun o ↦ ?_⟩
    simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap, Finset.mem_toList,
      Option.ite_none_left_eq_some, Option.some.injEq, Prod.exists]
    aesop
  have hcompletedFunctional : ShapeFunctional completed := by
    intro w h k hh hk
    rw [hcompleted] at hh hk
    rcases hh with hh | ⟨v, N, -, a, -, hfree, he⟩ <;>
      rcases hk with hk | ⟨v', N', -, a', -, hfree', he'⟩
    · exact hfunctional w h k hh hk
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact absurd ⟨_, hh, List.prefix_refl _⟩ hfree'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact absurd ⟨_, hk, List.prefix_refl _⟩ hfree
    · exact (Prod.mk.inj he).2.trans (Prod.mk.inj he').2.symm
  have hcompletedLeaf : ShapeLeafCompatible completed := by
    intro w h hw hd q k hq ⟨hpre, hne⟩
    rw [hcompleted] at hw hq
    rcases hw with hw | ⟨v, N, -, a, -, hfree, he⟩ <;>
      rcases hq with hq | ⟨v', N', hv', a', -, -, he'⟩
    · exact hleaf w h hw hd q k hq ⟨hpre, hne⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      have hpre := (List.prefix_concat_iff.1 hpre).resolve_left hne
      by_cases hwv : w = v'
      · exact hd (hfunctional w h .dirc hw (hwv ▸ hendpoints v' N' hv'))
      · exact hleaf w h hw hd v' .dirc (hendpoints v' N' hv') ⟨hpre, hwv⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hfree ⟨_, hq, hpre⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact hfree ⟨_, hendpoints v' N' hv', (List.prefix_concat_iff.1 hpre).resolve_left hne⟩
  have hspec := buildShapeFocus_spec hcompletedFunctional hcompletedLeaf
    (fun _ _ ↦ length_lt_observationFuel)
  have hforced : ∀ w N, (w, N) ∈ directories → ∀ a, Forced completed (w ++ [a]) ↔ a ∈ N := by
    intro w N hwN a
    constructor
    · rintro ⟨s, h, hmem, hs⟩
      rcases (hcompleted _).1 hmem with hmem | ⟨v, N', hv, a', ha', -, he⟩
      · exact (hcompatible w N hwN a s h (by simpa using hmem)).2 hs
      · obtain ⟨hpath, rfl⟩ := Prod.mk.inj he
        rcases List.prefix_concat_iff.1 ⟨s, hpath⟩ with heq | ⟨t, rfl⟩
        · obtain ⟨rfl, ha⟩ := List.append_inj' heq rfl
          cases ha
          exact hdirFunctional w N N' hwN hv ▸ ha'
        · exact (hcompatible w N hwN a t .dirc (by simpa using hendpoints _ N' hv)).2
            (Or.inr (by simp))
    · intro ha
      by_cases hfree : ∃ o ∈ shapes, w ++ [a] <+: o.1
      · obtain ⟨⟨_, h⟩, hmem, s, rfl⟩ := hfree
        exact ⟨s, h, (hcompleted _).2 (Or.inl hmem),
          (hcompatible w N hwN a s h (by simpa using hmem)).1 ha⟩
      · exact ⟨[], .file, (hcompleted _).2 (Or.inr ⟨w, N, hwN, a, ha, hfree, by simp⟩),
          Or.inr (by simp)⟩
  refine ⟨_, buildShapeFocus_canonical _ completed,
    fun w h hmem ↦ (hspec w).1 h ((hcompleted _).2 (Or.inl hmem)), fun w N hwN ↦ ?_⟩
  obtain ⟨g, hg, hshape⟩ := Option.map_eq_some_iff.1
    ((hspec w).1 .dirc ((hcompleted _).2 (Or.inl (hendpoints w N hwN))))
  rcases g with (_ | δ) | _ <;> simp only [FileTree.Focus.shape, reduceCtorEq] at hshape
  rw [entriesFollow, hg]
  refine congrArg some (Finset.ext fun a ↦ ?_)
  rw [FileTree.Focus.entryNames, mem_dom_iff_follow_child_tree _ _ δ hg, (hspec _).2,
    hforced w N hwN]

section Ground

variable {X : Type}

@[simp] theorem mem_shapeObservationsFor [DecidableEq X] {x : X} {w : List Γ} {h : TWE.Shape}
    {atoms : List (GroundTreeShapeAssertion Γ X)} :
    (w, h) ∈ shapeObservationsFor x atoms ↔ ⟨x, w, h⟩ ∈ atoms := by
  simp only [shapeObservationsFor, List.mem_filterMap]
  refine ⟨fun ⟨⟨y, u, k⟩, hmem, he⟩ ↦ ?_, fun hmem ↦ ⟨_, hmem, by simp⟩⟩
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact hmem

@[simp] theorem mem_directoryObservationsFor [DecidableEq X] {x : X} {w : List Γ} {N : Finset Γ}
    {atoms : List (GroundTreeDirectoryObservation Γ X)} :
    (w, N) ∈ directoryObservationsFor x atoms ↔ ⟨x, w, N⟩ ∈ atoms := by
  simp only [directoryObservationsFor, List.mem_filterMap]
  refine ⟨fun ⟨⟨y, u, M⟩, hmem, he⟩ ↦ ?_, fun hmem ↦ ⟨_, hmem, by simp⟩⟩
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact hmem

variable [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ] [DecidableEq X]

theorem groundShapesDirectories_realisable
    (shapes : List (GroundTreeShapeAssertion Γ X))
    (directories : List (GroundTreeDirectoryObservation Γ X))
    (hcompat : GroundDirectoryShapeCompatibility shapes directories) :
    ∃ θ, GroundShapesRealised θ shapes ∧ GroundDirectoriesRealised θ directories := by
  have key := fun x : X ↦ exists_realising_focus (shapes := shapeObservationsFor x shapes)
    (directories := directoryObservationsFor x directories)
    (fun w h k hh hk ↦ hcompat.shapesFunctional _ (mem_shapeObservationsFor.1 hh) _
      (mem_shapeObservationsFor.1 hk) rfl rfl)
    (fun w h hh hd q k hq ↦ hcompat.shapesLeafCompatible _ (mem_shapeObservationsFor.1 hh) hd _
      (mem_shapeObservationsFor.1 hq) rfl)
    (fun w N N' hN hN' ↦ hcompat.directoriesFunctional _ (mem_directoryObservationsFor.1 hN) _
      (mem_directoryObservationsFor.1 hN') rfl rfl)
    (fun w N hN ↦ mem_shapeObservationsFor.2
      (hcompat.endpointsObserved _ (mem_directoryObservationsFor.1 hN)))
    (fun w N hN a s h hh ↦ hcompat.shapesCompatible _ (mem_directoryObservationsFor.1 hN) _
      (mem_shapeObservationsFor.1 hh) rfl a s rfl)
  choose f hcanonical hshapes hdirectories using key
  exact ⟨fun x ↦ ⟨f x, hcanonical x⟩,
    fun atom hatom ↦ hshapes _ _ _ (mem_shapeObservationsFor.2 hatom),
    fun atom hatom ↦ hdirectories _ _ _ (mem_directoryObservationsFor.2 hatom)⟩

theorem groundBaseTreeRealisation_iff
    (atoms : List (GroundTreeShapeAssertion Γ X)) :
    (∃ θ, GroundShapesRealised θ atoms) ↔
      FunctionalConsistency atoms ∧ LeafCondition atoms := by
  constructor
  · rintro ⟨θ, hrealized⟩
    refine ⟨fun left hleft right hright htree hpath ↦ ?_,
      fun leaf hleaf hshape atom hatom htree ↦ ?_⟩
    · have hl := hrealized left hleft
      rw [htree, hpath] at hl
      exact Option.some.inj (hl.symm.trans (hrealized right hright))
    · have hl := hrealized leaf hleaf
      rw [htree] at hl
      exact shapeFollow_leaf_not_strictPrefix _ _ _ _ _ hl hshape (hrealized atom hatom)
  · rintro ⟨hfunctional, hleaf⟩
    obtain ⟨θ, hθ, -⟩ := groundShapesDirectories_realisable atoms []
      ⟨hfunctional, hleaf, by simp [GroundDirectoriesFunctional],
        by simp [GroundDirectoryEndpointsObserved], by simp [GroundDirectoryShapesCompatible]⟩
    exact ⟨θ, hθ⟩

end Ground

theorem baseTreeRealisation_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [DecidableEq V.Tree] (m : WordModel Γ V) (atoms : List (BaseShapeAssertion Γ V)) :
    (∃ θ, BaseShapeAssertionsSat (m.withTrees θ) atoms) ↔
      FunctionalConsistency (evalBaseShapeAssertions m atoms) ∧
        LeafCondition (evalBaseShapeAssertions m atoms) := by
  rw [← groundBaseTreeRealisation_iff]
  simp only [BaseShapeAssertionsSat, GroundShapesRealised, evalBaseShapeAssertions,
    List.forall_mem_map, observesShape_var_withTrees]
  rfl

end ToWE

end Linear

end TWE

end Accordion

end
