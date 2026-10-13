module

public import Accordion.TWE.Linear.ToWE.Properties.RewriteShapeAtom

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open FileTree.Focus (follow shapeFollow entriesFollow)

variable {Γ : Type} {V : TWE.Vars}

theorem not_exists_observesShape_nil_iff_entriesValue_eq_none [Ord Γ] [DecidableEq Γ]
    (m : WordModel Γ V)
    (T : TWE.Tree V) :
    (¬∃ h, ObservesShape m T ([] : List Γ) h) ↔ WordModel.entriesValue m T = none := by
  cases heval : m.toTWE.evalTree T with
  | none => simp [WordModel.entriesValue, TWE.Model.evalNameSet, heval, ObservesShape]
  | some focus =>
      rcases focus with (_ | _) | _ <;>
        simp [WordModel.entriesValue, TWE.Model.evalNameSet, heval, ObservesShape, shapeFollow,
          follow]

theorem find?_set_eq_some_of_nodup [TWE.Vars.Comparable V] (terms : List (EntriesTerm V))
    (hnodup : (terms.map EntriesTerm.set).Nodup) {e : EntriesTerm V} (he : e ∈ terms) :
    terms.find? (·.set = e.set) = some e := by
  induction terms with
  | nil => simp at he
  | cons e' terms ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
      rcases List.mem_cons.1 he with rfl | he
      · simp
      · have hne : e'.set ≠ e.set := fun heq ↦ hnodup.1 ⟨e, he, heq.symm⟩
        simp [hne, ih hnodup.2 he]

section NameEntries

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem nodup_and_notMem_run_flattenSet (S : TWE.Set Γ V) (W : TWE.Free V) :
    (((flattenSet S).run W).1.2.map EntriesTerm.set).Nodup ∧
      (∀ e ∈ ((flattenSet S).run W).1.2,
        e.set ∉ W.set ∧ e.set ∈ ((flattenSet S).run W).2.set ∧ e.tree.free ⊆ S.free) ∧
      W ⊆ ((flattenSet S).run W).2 := by
  induction S generalizing W with
  | insert a S ih =>
      obtain ⟨h₁, h₂, h₃⟩ := ih W
      exact ⟨h₁, fun e he ↦ ⟨(h₂ e he).1, (h₂ e he).2.1,
        Free.Subset.trans (h₂ e he).2.2 Free.subset_union_right⟩, h₃⟩
  | entries T =>
      refine ⟨List.nodup_singleton _, fun e he ↦ ?_, subset_freshSet W⟩
      obtain rfl : e = ⟨Fresh.fresh W.set, T⟩ := List.mem_singleton.1 he
      exact ⟨Fresh.fresh_notMem _, Finset.mem_insert_self _ _, Free.Subset.refl _⟩
  | var x | empty => exact ⟨List.nodup_nil, fun e he ↦ (by cases he), Free.Subset.refl W⟩

theorem nodup_and_notMem_run_flattenSetAtom (α : TWESetAtom Γ V) (W : TWE.Free V) :
    (((flattenSetAtom α).run W).1.2.map EntriesTerm.set).Nodup ∧
      ∀ e ∈ ((flattenSetAtom α).run W).1.2, e.set ∉ W.set ∧ e.tree.free ⊆ α.free := by
  cases α with
  | eq positive S S' =>
      obtain ⟨h₁, h₂, h₃⟩ := nodup_and_notMem_run_flattenSet S W
      obtain ⟨h₁', h₂', -⟩ := nodup_and_notMem_run_flattenSet S' ((flattenSet S).run W).2
      change (((flattenSet S).run W).1.2 ++
          ((flattenSet S').run ((flattenSet S).run W).2).1.2 |>.map EntriesTerm.set).Nodup ∧
        ∀ e ∈ ((flattenSet S).run W).1.2 ++ ((flattenSet S').run ((flattenSet S).run W).2).1.2,
          e.set ∉ W.set ∧ e.tree.free ⊆ S.free ∪ S'.free
      refine ⟨?_, fun e he ↦ ?_⟩
      · rw [List.map_append]
        refine List.nodup_append'.2 ⟨h₁, h₁', fun x hx hx' ↦ ?_⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        obtain ⟨e', he', heq⟩ := List.mem_map.1 hx'
        exact (h₂' e' he').1 (heq ▸ (h₂ e he).2.1)
      · rcases List.mem_append.1 he with he | he
        · exact ⟨(h₂ e he).1, Free.Subset.trans (h₂ e he).2.2 Free.subset_union_left⟩
        · exact ⟨fun h ↦ (h₂' e he).1 (h₃.2.2.2.2.1 h),
            Free.Subset.trans (h₂' e he).2.2 Free.subset_union_right⟩
  | mem positive a S =>
      obtain ⟨h₁, h₂, -⟩ := nodup_and_notMem_run_flattenSet S W
      exact ⟨h₁, fun e he ↦
        ⟨(h₂ e he).1, Free.Subset.trans (h₂ e he).2.2 Free.subset_union_right⟩⟩

variable [Ord Γ] [DecidableEq Γ]

theorem evalNameSet_eq_some_eval_flattenSet (m : WordModel Γ V) (S : TWE.Set Γ V) (W : TWE.Free V)
    (hterms : ∀ e ∈ ((flattenSet S).run W).1.2, e.Holds m) :
    m.toTWE.evalNameSet S = some (((flattenSet S).run W).1.1.eval m) := by
  induction S generalizing W with
  | var x => rfl
  | empty => rfl
  | insert a S ih =>
      rw [TWE.Model.evalNameSet, ih W hterms]
      rfl
  | entries T => exact hterms ⟨Fresh.fresh W.set, T⟩ (List.mem_singleton_self _)

theorem evalNameSet_eq_none_of_mem_flattenSet (m : WordModel Γ V) (S : TWE.Set Γ V) (W : TWE.Free V)
    (e : EntriesTerm V) (he : e ∈ ((flattenSet S).run W).1.2)
    (hnone : WordModel.entriesValue m e.tree = none) : m.toTWE.evalNameSet S = none := by
  induction S generalizing W with
  | var x | empty => cases he
  | insert a S ih =>
      rw [TWE.Model.evalNameSet, ih W he]
      rfl
  | entries T =>
      obtain rfl : e = ⟨Fresh.fresh W.set, T⟩ := List.mem_singleton.1 he
      exact hnone

theorem sat_flattenSetAtom_iff (m : WordModel Γ V) (α : TWESetAtom Γ V) (W : TWE.Free V)
    (hterms : ∀ e ∈ ((flattenSetAtom α).run W).1.2, e.Holds m) :
    ((flattenSetAtom α).run W).1.1.sat m ↔ α.sat m := by
  cases α with
  | eq positive S S' =>
      have hS := evalNameSet_eq_some_eval_flattenSet m S W fun e he ↦
        hterms e (List.mem_append_left _ he)
      have hS' := evalNameSet_eq_some_eval_flattenSet m S' ((flattenSet S).run W).2 fun e he ↦
        hterms e (List.mem_append_right _ he)
      cases positive <;>
        simp only [TWESetAtom.sat, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom,
          TWE.Model.satAtom, hS, hS'] <;> rfl
  | mem positive a S =>
      have hS := evalNameSet_eq_some_eval_flattenSet m S W hterms
      cases positive <;>
        simp only [TWESetAtom.sat, Accordion.Formula.sat, TWE.Model.sat_iff_satAtom,
          TWE.Model.satAtom, hS] <;> rfl

theorem sat_iff_positive_eq_false_of_mem_flattenSetAtom (m : WordModel Γ V) (α : TWESetAtom Γ V)
    (W : TWE.Free V)
    (e : EntriesTerm V) (he : e ∈ ((flattenSetAtom α).run W).1.2)
    (hnone : WordModel.entriesValue m e.tree = none) : α.sat m ↔ α.positive = false := by
  have hpolarity : ∀ (positive : Bool) (A : Prop), ¬A →
      ((if positive then A else ¬A) ↔ positive = false) := by
    intro positive A hA
    cases positive <;> simp [hA]
  cases α with
  | eq positive S S' =>
      refine hpolarity positive _ ?_
      simp only [Accordion.Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom]
      rcases List.mem_append.1 he with he | he
      · simp [evalNameSet_eq_none_of_mem_flattenSet m S W e he hnone]
      · rw [evalNameSet_eq_none_of_mem_flattenSet m S' _ e he hnone]
        cases m.toTWE.evalNameSet S <;> simp
  | mem positive a S =>
      refine hpolarity positive _ ?_
      simp [TWE.Model.satAtom, evalNameSet_eq_none_of_mem_flattenSet m S W e he hnone]

open scoped WE in
theorem nameEntries_satPreserving {U : TWE.Free V} (α : Atom Γ V) (hα : α.free ⊆ U) :
    SatPreserving U [α] ((nameEntries α).run U).1 := by
  cases α with
  | tweSet α => ?_
  | _ => exact SatPreserving.of_free_subset hα
  refine .of_atom fun m ↦ ?_
  obtain ⟨hnodup, hfresh⟩ := nodup_and_notMem_run_flattenSetAtom α U
  set flat := ((flattenSetAtom α).run U).1.1
  set terms := ((flattenSetAtom α).run U).1.2
  set D : Guess (Conj Γ V) := (⋀ e ∈ terms, e.set ≐ entries(e.tree[ε])) ∧ Atom.set flat
  have hdefined (m' : WordModel Γ V) :
      Guess.sat m' D ↔ (∀ e ∈ terms, e.Holds m') ∧ flat.sat m' := by
    simp [D, Atom.sat, EntriesTerm.Holds, entriesValue_eq_some_iff_observesEntries]
  have hundefined (m' : WordModel Γ V) :
      Guess.sat m' (⋁ e ∈ terms, e.tree[ε]↑ : Guess (Conj Γ V)) ↔
        ∃ e ∈ terms, WordModel.entriesValue m' e.tree = none := by
    simp only [Guess.sat_any, InjectAtom.inject_guess, Guess.sat_atom, Atom.sat,
      evalWord_empty, not_exists_observesShape_nil_iff_entriesValue_eq_none]
  have hvalue (m' : WordModel Γ V) (hm : m ≡[U] m') (e : EntriesTerm V) (he : e ∈ terms) :
      WordModel.entriesValue m' e.tree = WordModel.entriesValue m e.tree :=
    (TWE.Model.evalNameSet_congr hm.toTWE (s := .entries e.tree)
      (Free.Subset.trans (hfresh e he).2 hα)).symm
  have hrun : ((nameEntries (.tweSet α)).run U).1 =
      if α.positive then D else D ∨ ⋁ e ∈ terms, e.tree[ε]↑ := rfl
  rw [hrun, Atom.sat]
  by_cases hall : ∀ e ∈ terms, ∃ v, WordModel.entriesValue m e.tree = some v
  · let m' := m.withSets fun x ↦
      (terms.find? (·.set = x)).elim (m.σSet x) fun e ↦ (WordModel.entriesValue m e.tree).getD ∅
    have hm : m ≡[U] m' := by
      refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun x hx ↦ ?_,
        fun _ _ ↦ rfl⟩
      have hnone : terms.find? (·.set = x) = none := List.find?_eq_none.2 fun e he ↦ by
        simpa using fun h : e.set = x ↦ (hfresh e he).1 (h ▸ Finset.mem_coe.1 hx)
      simp [m', WordModel.withSets,hnone]
    have hholds : ∀ e ∈ terms, e.Holds m' := by
      intro e he
      obtain ⟨v, hv⟩ := hall e he
      rw [EntriesTerm.Holds, hvalue m' hm e he, hv]
      simp [m', WordModel.withSets,find?_set_eq_some_of_nodup terms hnodup he, hv]
    have hnamed : Guess.satFresh m U D ↔ α.sat m := by
      constructor
      · rintro ⟨m₁, hm₁, hsat⟩
        obtain ⟨hterms, hflat⟩ := (hdefined m₁).1 hsat
        exact (TWESetAtom.sat_congr hm₁ hα).2 ((sat_flattenSetAtom_iff m₁ α U hterms).1 hflat)
      · intro hsat
        exact ⟨m', hm, (hdefined m').2 ⟨hholds,
          (sat_flattenSetAtom_iff m' α U hholds).2 ((TWESetAtom.sat_congr hm hα).1 hsat)⟩⟩
    split
    · exact hnamed
    · rw [Guess.satFresh_or, hnamed, or_iff_left]
      rintro ⟨m₁, hm₁, h⟩
      obtain ⟨e, he, hnone⟩ := (hundefined m₁).1 h
      obtain ⟨v, hv⟩ := hall e he
      rw [hvalue m₁ hm₁ e he, hv] at hnone
      cases hnone
  · push Not at hall
    obtain ⟨e, he, hnone⟩ := hall
    have hnone : WordModel.entriesValue m e.tree = none := Option.eq_none_iff_forall_ne_some.2 hnone
    rw [sat_iff_positive_eq_false_of_mem_flattenSetAtom m α U e he hnone]
    have hnamed : ¬Guess.satFresh m U D := fun ⟨m₁, hm₁, hsat⟩ ↦ by
      have := ((hdefined m₁).1 hsat).1 e he
      rw [EntriesTerm.Holds, hvalue m₁ hm₁ e he, hnone] at this
      cases this
    split <;> rename_i hpositive
    · simpa [hpositive] using hnamed
    · simp only [hpositive, iff_true, Guess.satFresh_or, hnamed, false_or]
      exact Guess.satFresh_of_sat ((hundefined m).2 ⟨e, he, hnone⟩)

end NameEntries

section Entries

variable [Ord Γ] [DecidableEq Γ] [Std.LawfulEqOrd Γ]

theorem observesEntries_select_iff (m : WordModel Γ V) (T : TWE.Tree V) (l : V.Loc)
    (query : List Γ) (value : Finset Γ) :
    ObservesEntries m (.select T l) query value ↔
      ObservesEntries m T (m.σLoc l ++ query) value := by
  simp only [observesEntries_iff, observesShape_select_iff, List.append_assoc]

theorem observesEntries_file_iff (m : WordModel Γ V) (query : List Γ) (value : Finset Γ) :
    ObservesEntries m .file query value ↔ query = [] ∧ value = ∅ := by
  simp [observesEntries_iff, observesShape_file_iff, Finset.eq_empty_iff_forall_notMem]

theorem observesEntries_abst_iff (m : WordModel Γ V) (query : List Γ) (value : Finset Γ) :
    ObservesEntries m .abst query value ↔ query = [] ∧ value = ∅ := by
  simp [observesEntries_iff, observesShape_abst_iff, Finset.eq_empty_iff_forall_notMem]

theorem observesEntries_emptyDirc_iff (m : WordModel Γ V) (query : List Γ)
    (value : Finset Γ) :
    ObservesEntries m .emptyDirc query value ↔
      (query = [] ∨ ∃ name, query = [name]) ∧ value = ∅ := by
  simp [observesEntries_iff, observesShape_emptyDirc_iff, Finset.eq_empty_iff_forall_notMem,
    exists_or]

theorem observesEntries_update_iff [Std.TransOrd Γ] (m : WordModel Γ V) {T T' : TWE.Tree V}
    {l : V.Loc} (hdefined : (m.toTWE.evalTree (.update T l T')).isSome) (w : List Γ)
    (N : Finset Γ) :
    ObservesEntries m (.update T l T') w N ↔
      (∃ suffix, w = m.σLoc l ++ suffix ∧ ObservesEntries m T' suffix N) ∨
        (∃ c old, m.σLoc l = w ++ [c] ∧ ObservesEntries m T w old ∧
          ((ObservesShape m T' [] .file ∨ ObservesShape m T' [] .dirc) ∧ N = insert c old ∨
            ObservesShape m T' [] .absent ∧ c ∉ N ∧ insert c N = insert c old)) ∨
        (¬m.σLoc l <+: w ∧ (∀ c, m.σLoc l ≠ w ++ [c]) ∧ ObservesEntries m T w N) := by
  have hT' : m.σLoc l ≠ [] → ∃ h, ObservesShape m T' [] h := by
    intro hne
    rcases (exists_evalTree_update_iff m T T' l).1
        ((TWE.Model.isSome_evalTree_update_iff _ _ _ _).1 hdefined) with
      ⟨h0, -⟩ | ⟨-, -, f, hf⟩
    · exact absurd h0 hne
    · exact ⟨f.shape, f, hf, rfl⟩
  simp only [observesEntries_iff, observesShape_update_iff m hdefined]
  generalize m.σLoc l = L at hT' ⊢
  by_cases hinside : L <+: w
  · obtain ⟨s, rfl⟩ := hinside
    simp [List.append_assoc]
  by_cases hchild : ∃ c, L = w ++ [c]
  · obtain ⟨c, rfl⟩ := hchild
    have hparent : ∀ h, ((∃ s, w = w ++ [c] ++ s ∧ ObservesShape m T' s h) ∨
        ¬w ++ [c] <+: w ∧ ObservesShape m T w h) ↔ ObservesShape m T w h := by
      simp [hinside]
    have hchildren : ∀ a h, ((∃ s, w ++ [a] = w ++ [c] ++ s ∧ ObservesShape m T' s h) ∨
        ¬w ++ [c] <+: w ++ [a] ∧ ObservesShape m T (w ++ [a]) h) ↔
          if a = c then ObservesShape m T' [] h else ObservesShape m T (w ++ [a]) h := by
      intro a h
      split_ifs with hac
      · simp [hac]
      · simp [hac, Ne.symm hac]
    simp only [hparent, hchildren]
    simp [hinside]
    obtain ⟨-, f, hf, -⟩ := hT' (by simp)
    have hobs : ∀ h, ObservesShape m T' [] h ↔ f.shape = h := fun h ↦ by
      simp [observesShape_nil_iff, hf]
    have hinsert : ∀ old : Finset Γ, N = insert c old ↔ c ∈ N ∧ ∀ a ≠ c, a ∈ N ↔ a ∈ old := by
      intro old
      simp only [Finset.ext_iff, Finset.mem_insert]
      exact ⟨fun h ↦ ⟨(h c).2 (.inl rfl), fun a hac ↦ by simp [h a, hac]⟩,
        fun ⟨hc, h⟩ a ↦ by by_cases hac : a = c <;> simp [hac, hc, h]⟩
    have herase : ∀ old : Finset Γ, insert c N = insert c old ↔ ∀ a ≠ c, a ∈ N ↔ a ∈ old := by
      intro old
      simp only [Finset.ext_iff, Finset.mem_insert]
      exact ⟨fun h a hac ↦ by simpa [hac] using h a,
        fun h a ↦ by by_cases hac : a = c <;> simp [hac, h]⟩
    simp only [hobs, hinsert, herase]
    constructor
    · rintro ⟨hw, hN⟩
      obtain ⟨old, hold⟩ := exists_observesEntries hw
      rw [observesEntries_iff] at hold
      have hrest : ∀ a ≠ c, a ∈ N ↔ a ∈ old := fun a hac ↦ by rw [hN a, hold.2 a]; simp [hac]
      have hc := hN c
      refine ⟨old, hold, ?_⟩
      cases hs : f.shape <;> simp_all
    · rintro ⟨old, ⟨hw, hold⟩, hcase⟩
      refine ⟨hw, fun a ↦ ?_⟩
      by_cases hac : a = c
      · subst hac
        rcases hcase with ⟨hs, hc, -⟩ | ⟨hs, hc, -⟩ <;> simp [hc, hs]
      · rcases hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> simp [hac, h a hac, hold a]
  · push Not at hchild
    have hbelow : ∀ a, ¬L <+: w ++ [a] := fun a h ↦
      (List.prefix_concat_iff.1 h).elim (hchild a) hinside
    have hw : ∀ s, w ≠ L ++ s := fun s h ↦ hinside ⟨s, h.symm⟩
    have hwa : ∀ a s, w ++ [a] ≠ L ++ s := fun a s h ↦ hbelow a ⟨s, h.symm⟩
    simp [hinside, hchild, hbelow, hw, hwa]

end Entries

theorem rewriteEntriesAtom_satPreserving [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] {U : TWE.Free V} (α : Atom Γ V)
    (hα : α.free ⊆ U) : SatPreservingIn α.DefinedIn U [α] ((rewriteEntriesAtom α).run U).1 := by
  refine .of_atom fun m hdefined ↦ ?_
  cases α with
  | entries R T ℓ =>
      have hℓ : Word.free ℓ ⊆ U := (Free.union_subset hα).2
      have hR : R ∈ U.set := by free_vars
      cases T with
      | var t => exact Guess.satFresh_atom hα
      | file | abst =>
          simp only [rewriteEntriesAtom, FreshM.run_pure]
          rw [Guess.satFresh_iff_of_free_subset (by all_atoms <;> free_vars)]
          simp [Atom.sat, SetAtom.sat, SetTerm.eval, observesEntries_file_iff,
            observesEntries_abst_iff]
      | emptyDirc =>
          let A : V.Name := Fresh.fresh U.name
          have hrun (m' : WordModel Γ V) :
              Guess.sat m' ((rewriteEntriesAtom (.entries R .emptyDirc ℓ)).run U).1 ↔
                (m'.toWE.evalWord ℓ = [] ∨ m'.toWE.evalWord ℓ = [m'.σName A]) ∧
                  m'.σSet R = ∅ := by
            simp only [rewriteEntriesAtom, FreshM.run_bind, run_freshName, FreshM.run_pure]
            simp [Atom.sat, SetAtom.sat, SetTerm.eval, A]
          rw [Atom.sat, observesEntries_emptyDirc_iff]
          simp only [Guess.satFresh, hrun]
          constructor
          · rintro ⟨m', hm, h, hset⟩
            rw [evalWord_congr hm hℓ, hm.σSet_eq hR]
            exact ⟨h.imp_right fun h ↦ ⟨_, h⟩, hset⟩
          · rintro ⟨h | ⟨a, h⟩, hset⟩
            · exact ⟨m, .refl m U, .inl h, hset⟩
            · have hm : m ≡[U] m.setName A a := WordModel.congr_setName (Fresh.fresh_notMem _)
              refine ⟨_, hm, .inr ?_, by rw [← hm.σSet_eq hR]; exact hset⟩
              rw [← evalWord_congr hm hℓ, h]
              simp
      | select T l =>
          simp only [rewriteEntriesAtom, FreshM.run_pure, InjectAtom.inject_guess]
          rw [Guess.satFresh_atom (by free_vars)]
          simp only [Atom.sat, WE.Model.evalWord_append, evalWord_loc, observesEntries_select_iff]
      | update T l T' =>
          obtain ⟨hT, hl, hT'⟩ : T.free ⊆ U ∧ l ∈ U.loc ∧ T'.free ⊆ U := by free_vars
          have hloc : Word.free (l : Word Γ V) ⊆ U := by free_vars
          let ℓ₂ : V.Path := Fresh.fresh U.path
          let A : V.Name := Fresh.fresh U.name
          let A' : V.Name := Fresh.fresh (insert A U.name)
          let ℓ₃ : V.Path := Fresh.fresh (insert ℓ₂ U.path)
          let W : TWE.Free V :=
            { U with name := insert A' (insert A U.name), path := insert ℓ₃ (insert ℓ₂ U.path) }
          let W' : TWE.Free V := ((ℓ ∥ (l : Word Γ V)).run W).2
          let B : V.Name := Fresh.fresh W'.name
          let R' : V.Set := Fresh.fresh W'.set
          have hUW : U ⊆ W :=
            ⟨(Finset.subset_insert _ _).trans (Finset.subset_insert _ _), subset_rfl,
              (Finset.subset_insert _ _).trans (Finset.subset_insert _ _), subset_rfl,
              subset_rfl, subset_rfl⟩
          have hUW' : U ⊆ W' := Free.Subset.trans hUW (subset_pathIncomparableFormula _ _ _)
          have hAA' : A ≠ A' := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
          have hℓ₃ : ℓ₃ ∉ U.path := Fresh.fresh_notMem_of_subset (Finset.subset_insert _ _)
          have hA' : A' ∉ U.name := Fresh.fresh_notMem_of_subset (Finset.subset_insert _ _)
          have hB : B ∉ U.name := Fresh.fresh_notMem_of_subset hUW'.1
          have hR' : R' ∉ U.set := Fresh.fresh_notMem_of_subset hUW'.2.2.2.2.1
          have hrun (m' : WordModel Γ V) :
              Guess.sat m' ((rewriteEntriesAtom (.entries R (.update T l T') ℓ)).run U).1 ↔
                (m'.toWE.evalWord ℓ = m'.σLoc l ++ m'.σPath ℓ₂ ∧
                    ObservesEntries m' T' (m'.σPath ℓ₂) (m'.σSet R)) ∨
                  ((m'.σLoc l = m'.toWE.evalWord ℓ ++ [m'.σName A] ++ [m'.σName A'] ++
                        m'.σPath ℓ₃ ∨
                      m'.toWE ⊨ ((ℓ ∥ (l : Word Γ V)).run W).1) ∧
                    ObservesEntries m' T (m'.toWE.evalWord ℓ) (m'.σSet R)) ∨
                  (m'.σLoc l = m'.toWE.evalWord ℓ ++ [m'.σName B] ∧
                    ObservesEntries m' T (m'.toWE.evalWord ℓ) (m'.σSet R') ∧
                    ((ObservesShape m' T' [] .file ∨ ObservesShape m' T' [] .dirc) ∧
                        m'.σSet R = insert (m'.σName B) (m'.σSet R') ∨
                      ObservesShape m' T' [] .absent ∧ m'.σName B ∉ m'.σSet R ∧
                        insert (m'.σName B) (m'.σSet R) =
                          insert (m'.σName B) (m'.σSet R'))) := by
            simp only [rewriteEntriesAtom, FreshM.run_bind, run_freshPath, run_freshName,
              run_freshSet, FreshM.run_pure, Guess.sat_and, Guess.sat_or, InjectAtom.inject_guess,
              Guess.sat_atom, Atom.sat, SetAtom.sat, SetTerm.eval, Formula.sat,
              WE.Model.sat_wordEq_iff, WE.Model.evalWord_append, evalWord_loc, evalWord_pathVar,
              evalWord_nameVar, evalWord_empty, ite_true]
            exact Iff.rfl
          rw [Atom.sat, observesEntries_update_iff m
            (hdefined _ (by simp [Atom.updates, TWE.Tree.updates]))]
          simp only [Guess.satFresh, hrun]
          constructor
          · rintro ⟨m', hm, h⟩
            simp only [← evalWord_congr hm hℓ, ← hm.σLoc_eq hl, ← hm.σSet_eq hR,
              ← observesEntries_congr hm hT, ← observesEntries_congr hm hT',
              ← observesShape_congr hm hT'] at h
            rcases h with ⟨heq, hentries⟩ | ⟨hdeep | hinc, hentries⟩ | ⟨hchild, hold, hset⟩
            · exact .inl ⟨_, heq, hentries⟩
            · refine .inr (.inr ⟨fun hpre ↦ ?_, fun c hc ↦ ?_, hentries⟩)
              · have := hpre.length_le
                simp [hdeep] at this
                omega
              · have := congrArg List.length (hdeep.symm.trans hc)
                simp at this
            · obtain ⟨h₁, h₂⟩ :=
                (exists_sat_pathIncomparableFormula_iff m hUW hℓ hloc).1 ⟨m', hm, hinc⟩
              rw [evalWord_loc] at h₁ h₂
              exact .inr (.inr ⟨h₂, fun c hc ↦ h₁ ⟨[c], hc.symm⟩, hentries⟩)
            · exact .inr (.inl ⟨_, _, hchild, hold, hset⟩)
          · rintro (⟨suffix, hword, hentries⟩ | ⟨c, old, hchild, hold, hset⟩ |
              ⟨hnotPrefix, hnotChild, hentries⟩)
            · have hm : m ≡[U] m.setPath ℓ₂ suffix :=
                WordModel.congr_setPath (Fresh.fresh_notMem _)
              refine ⟨_, hm, .inl ⟨?_, ?_⟩⟩
              · rw [← evalWord_congr hm hℓ, ← hm.σLoc_eq hl, hword]
                simp
              · rw [← hm.σSet_eq hR, ← observesEntries_congr hm hT']
                simpa using hentries
            · let m' := (m.setName B c).setSet R' old
              have hm : m ≡[U] m' :=
                (WordModel.congr_setName hB).trans (WordModel.congr_setSet hR')
              have hσB : m'.σName B = c := by simp [m']
              have hσR' : m'.σSet R' = old := by simp [m']
              refine ⟨m', hm, .inr (.inr ?_)⟩
              rw [hσB, hσR', ← evalWord_congr hm hℓ, ← hm.σLoc_eq hl, ← hm.σSet_eq hR]
              simp only [← observesEntries_congr hm hT, ← observesShape_congr hm hT']
              exact ⟨hchild, hold, hset⟩
            rw [WE.GroundWord.not_prefix_iff_exists] at hnotPrefix
            rcases hnotPrefix with ⟨a, _ | ⟨b, rest⟩, hword⟩ |
              ⟨common, a, k, b, k', hlocWord, hword, hne⟩
            · exact absurd hword (hnotChild a)
            · let m' := ((m.setName A a).setName A' b).setPath ℓ₃ rest
              have hm : m ≡[U] m' :=
                ((WordModel.congr_setName (Fresh.fresh_notMem _)).trans
                  (WordModel.congr_setName hA')).trans (WordModel.congr_setPath hℓ₃)
              refine ⟨m', hm, .inr (.inl ⟨.inl ?_, ?_⟩)⟩
              · rw [← evalWord_congr hm hℓ, ← hm.σLoc_eq hl, hword]
                simp [m', hAA']
              · rw [← evalWord_congr hm hℓ, ← hm.σSet_eq hR]
                exact (observesEntries_congr hm hT _ _).1 hentries
            · obtain ⟨m', hm, hinc⟩ := (exists_sat_pathIncomparableFormula_iff m hUW hℓ hloc).2 (by
                rw [evalWord_loc, WE.GroundWord.not_prefix_iff_exists,
                  WE.GroundWord.not_prefix_iff_exists]
                exact ⟨.inr ⟨common, b, k', a, k, hword, hlocWord, Ne.symm hne⟩,
                  .inr ⟨common, a, k, b, k', hlocWord, hword, hne⟩⟩)
              refine ⟨m', hm, .inr (.inl ⟨.inr hinc, ?_⟩)⟩
              rw [← evalWord_congr hm hℓ, ← hm.σSet_eq hR]
              exact (observesEntries_congr hm hT _ _).1 hentries
  | _ => exact Guess.satFresh_atom hα

section

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem allAtoms_tweSetRank_lt_nameEntries (α : Atom Γ V) (U : TWE.Free V) :
    ((nameEntries α).run U).1.AllAtoms
      fun a ↦ a.tweSetRank = 0 ∨ a.tweSetRank < α.tweSetRank := by
  cases α with
  | tweSet a =>
      simp only [nameEntries, FreshM.run_bind, FreshM.run_pure]
      all_atoms <;> simp [Atom.tweSetRank]
  | _ => exact Guess.AllAtoms.atom (Or.inl rfl)

theorem rewriteAtoms_nameEntries_mem_entriesNamed (β : Conj Γ V) :
    (rewriteAtoms nameEntries β).AllAtoms Atom.EntriesNamed := by
  refine fun γ hγ α hα ↦ ?_
  have := allAtoms_rank_eq_zero_rewriteAtoms Atom.tweSetRank allAtoms_tweSetRank_lt_nameEntries β
    (fun α _ ↦ by cases α <;> simp [Atom.tweSetRank]) γ hγ α hα
  cases α <;> simp_all [Atom.tweSetRank, Atom.EntriesNamed]

theorem run_rewriteEntriesAtom_of_entriesRank_eq_zero (α : Atom Γ V) (hα : α.entriesRank = 0)
    (U : TWE.Free V) : ((rewriteEntriesAtom α).run U).1 = pure [α] := by
  rcases α with _ | _ | _ | ⟨R, T, ℓ⟩ | _ | _ <;> try rfl
  cases T <;> first | rfl | simp [Atom.entriesRank, TWE.Tree.size] at hα

theorem allAtoms_entriesRank_lt_rewriteEntriesAtom (α : Atom Γ V) (U : TWE.Free V) :
    ((rewriteEntriesAtom α).run U).1.AllAtoms
      fun a ↦ a.entriesRank = 0 ∨ a.entriesRank < α.entriesRank := by
  by_cases hα : α.entriesRank = 0
  · rw [run_rewriteEntriesAtom_of_entriesRank_eq_zero α hα U]
    exact Guess.AllAtoms.atom (Or.inl hα)
  rcases α with _ | _ | _ | ⟨R, T, ℓ⟩ | _ | _ <;>
    simp only [Atom.entriesRank, not_true_eq_false] at hα
  cases T <;>
    simp only [rewriteEntriesAtom, FreshM.run_bind, run_freshName, run_freshPath, run_freshSet,
      FreshM.run_pure] <;>
    all_atoms <;> simp [Atom.entriesRank, TWE.Tree.size] <;> omega

theorem run_rewriteEntriesAtom_mem_entriesNamed (α : Atom Γ V) (U : TWE.Free V)
    (hα : α.EntriesNamed) : ((rewriteEntriesAtom α).run U).1.AllAtoms Atom.EntriesNamed := by
  by_cases hrank : α.entriesRank = 0
  · rw [run_rewriteEntriesAtom_of_entriesRank_eq_zero α hrank U]
    exact Guess.AllAtoms.atom hα
  rcases α with _ | _ | _ | ⟨R, T, ℓ⟩ | _ | _ <;>
    simp only [Atom.entriesRank, not_true_eq_false] at hrank
  cases T <;>
    simp only [rewriteEntriesAtom, FreshM.run_bind, run_freshName, run_freshPath, run_freshSet,
      FreshM.run_pure] <;>
    all_atoms <;> trivial

theorem allAtoms_updates_subset_rewriteEntriesAtom (α : Atom Γ V) (U : TWE.Free V) :
    ((rewriteEntriesAtom α).run U).1.AllAtoms (·.updates ⊆ α.updates) := by
  by_cases hrank : α.entriesRank = 0
  · rw [run_rewriteEntriesAtom_of_entriesRank_eq_zero α hrank U]
    exact Guess.AllAtoms.atom (List.Subset.refl _)
  rcases α with _ | _ | _ | ⟨R, T, ℓ⟩ | _ | _ <;>
    simp only [Atom.entriesRank, not_true_eq_false] at hrank
  cases T <;>
    simp only [rewriteEntriesAtom, FreshM.run_bind, run_freshName, run_freshPath, run_freshSet,
      FreshM.run_pure] <;>
    all_atoms <;> intro a ha <;> simp_all [Atom.updates, TWE.Tree.updates]

theorem rewriteAtoms_rewriteEntriesAtom_mem_entriesRewritten (β : Conj Γ V)
    (hβ : ∀ α ∈ β, α.EntriesNamed) :
    (rewriteAtoms rewriteEntriesAtom β).AllAtoms Atom.EntriesRewritten := by
  intro γ hγ α hα
  have hnamed := allAtoms_rewriteAtoms
    (fun α U ↦ run_rewriteEntriesAtom_mem_entriesNamed α U) β hβ γ hγ α hα
  have hrank := allAtoms_rank_eq_zero_rewriteAtoms Atom.entriesRank
    allAtoms_entriesRank_lt_rewriteEntriesAtom β
    (fun α _ ↦ by cases α <;> simp [Atom.entriesRank, Atom.treeSize]; omega) γ hγ α hα
  rcases α with _ | _ | _ | ⟨R, T, ℓ⟩ | _ | _ <;> (try cases T) <;>
    simp_all [Atom.entriesRank, Atom.EntriesNamed, Atom.EntriesRewritten, TWE.Tree.size]

end

end ToWE

end Linear

end TWE

end Accordion

end
