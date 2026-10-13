module

public import Accordion.TWE.Linear.ToWE.Properties.EliminateEntries

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open WordModel (withSets)

variable {Γ : Type} {V : TWE.Vars}

theorem rewriteSetDisequality_satPreserving [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] {U : TWE.Free V} (α : Atom Γ V) (hα : α.free ⊆ U) :
    SatPreserving U [α] ((rewriteSetDisequality α).run U).1 := by
  rcases α with _ | _ | _ | _ | ⟨_ | _, S₁, S₂⟩ | _
  all_goals try exact SatPreserving.of_free_subset hα
  obtain ⟨h₁, h₂⟩ : S₁.free ⊆ U ∧ S₂.free ⊆ U := TWE.Free.union_subset hα
  refine .of_atom fun m ↦ ?_
  let A : V.Name := Fresh.fresh U.name
  have hA : A ∉ U.name := Fresh.fresh_notMem _
  have hsat : ∀ m' : WordModel Γ V,
      Guess.sat m' ((rewriteSetDisequality (.set (.eq false S₁ S₂))).run U).1 ↔
        (m'.σName A ∈ S₁.eval m' ∧ m'.σName A ∉ S₂.eval m') ∨
          (m'.σName A ∉ S₁.eval m' ∧ m'.σName A ∈ S₂.eval m') := by
    intro m'
    change Guess.sat m' (A ∈̇ S₁ ∧ A ∉̇ S₂ ∨ A ∉̇ S₁ ∧ A ∈̇ S₂) ↔ _
    simp [Atom.sat, SetAtom.sat, TWE.Model.evalName, WordModel.toTWE]
  change _ ↔ S₁.eval m ≠ S₂.eval m
  constructor
  · rintro ⟨m', hm, hD⟩ hequal
    rw [SetTerm.eval_congr hm h₁, SetTerm.eval_congr hm h₂] at hequal
    have := (hsat m').1 hD
    rw [hequal] at this
    tauto
  · intro hne
    obtain ⟨a, ha⟩ := not_forall.1 (mt Finset.ext hne)
    have hm : m ≡[U] m.setName A a := WordModel.congr_setName hA
    have hσ : (m.setName A a).σName A = a := by simp
    refine ⟨_, hm, (hsat _).2 ?_⟩
    rw [← SetTerm.eval_congr hm h₁, ← SetTerm.eval_congr hm h₂, hσ]
    tauto

section Run

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem run_encodeSets (source : Conj Γ V) (W : TWE.Free V) :
    ((encodeSets source).run W).1 =
      ((⋀ α ∈ source.filter (·.set?.isNone), (α : Guess (Conj Γ V))) ∧
        ⌜setEncodingFormula (TWE.Name.toWord (.var (Fresh.fresh W.name)))
          (fun x i ↦ TWE.Name.toWord (.var (((freshSequences (source.sets.flatMap SetAtom.variables)
            (setWordBound source.sets)).run
              { W with name := insert (Fresh.fresh W.name) W.name }).1 x i)))
          source.sets⌝) :=
  rfl

end Run

section Encoding

variable [Ord Γ]

variable [DecidableEq Γ] (m : WordModel Γ V) (sentinel : V.Name)

theorem mem_encodedSet {c a : Γ} {names : List (TWE.Name Γ V)} :
    a ∈ encodedSet m c names ↔ a ≠ c ∧ ∃ t ∈ names, m.toTWE.evalName t = a := by
  simp [encodedSet]

theorem sat_setMembershipFormula (a : TWE.Name Γ V) (names : List (TWE.Name Γ V)) :
    m.toWE ⊨ setMembershipFormula (TWE.Name.toWord (.var sentinel)) (TWE.Name.toWord a)
        (names.map TWE.Name.toWord) ↔
      m.toTWE.evalName a ∈ encodedSet m (m.σName sentinel) names := by
  simp only [setMembershipFormula, sat_any, List.mem_map, exists_exists_and_eq_and,
    Formula.sat, WE.Model.sat_wordEq_iff, Name.evalWord_toWord, evalName_toTWE_var, List.cons.injEq,
    and_true,
    mem_encodedSet]
  constructor
  · rintro ⟨t, ht, hne, heq⟩
    exact ⟨heq ▸ hne, t, ht, heq.symm⟩
  · rintro ⟨hne, t, ht, heq⟩
    exact ⟨t, ht, heq ▸ hne, heq.symm⟩

theorem sat_setSubsetFormula (names names' : List (TWE.Name Γ V)) :
    m.toWE ⊨ setSubsetFormula (TWE.Name.toWord (.var sentinel)) (names.map TWE.Name.toWord)
        (names'.map TWE.Name.toWord) ↔
      encodedSet m (m.σName sentinel) names ⊆ encodedSet m (m.σName sentinel) names' := by
  simp only [setSubsetFormula, sat_all, List.forall_mem_map, Formula.sat, WE.Model.sat_wordEq_iff,
    Name.evalWord_toWord, evalName_toTWE_var, List.cons.injEq, and_true, sat_setMembershipFormula,
    or_iff_not_imp_left]
  refine ⟨fun h a ha ↦ ?_, fun h t ht hne ↦ h ((mem_encodedSet m).2 ⟨hne, t, ht, rfl⟩)⟩
  obtain ⟨hne, t, ht, rfl⟩ := (mem_encodedSet m).1 ha
  exact h t ht hne

variable (N : V.Set → Nat → V.Name) (width : Nat)

theorem eval_eq_encodedSet_encodingNames (c : Γ) (S : SetTerm Γ V)
    (hvals : ∀ x ∈ S.variables, m.σSet x = encodedSet m c
      ((List.range width).map fun i ↦ .var (N x i)))
    (hnames : ∀ a ∈ S.names, m.toTWE.evalName a ≠ c) :
    encodedSet m c (S.encodingNames N width) = S.eval m := by
  induction S with
  | var x =>
      have := hvals x (List.mem_singleton_self x)
      simpa [SetTerm.encodingNames, SetTerm.names, SetTerm.variables, SetTerm.eval] using this.symm
  | empty =>
      simp [encodedSet, SetTerm.encodingNames, SetTerm.names, SetTerm.variables, SetTerm.eval]
  | insert a S ih =>
      simp only [SetTerm.names, List.forall_mem_cons] at hnames
      rw [SetTerm.eval, ← ih (by simpa [SetTerm.variables] using hvals) hnames.2]
      simp only [encodedSet, SetTerm.encodingNames, SetTerm.names, SetTerm.variables,
        List.cons_append, List.map_cons, List.toFinset_cons]
      rw [Finset.erase_insert_of_ne hnames.1]

theorem sat_setAtomEncodingFormula (α : SetAtom Γ V)
    (hvals : ∀ x ∈ α.variables, m.σSet x = encodedSet m (m.σName sentinel)
      ((List.range width).map fun i ↦ .var (N x i)))
    (hnames : ∀ a ∈ α.names, m.toTWE.evalName a ≠ m.σName sentinel) :
    m.toWE ⊨ setAtomEncodingFormula (TWE.Name.toWord (.var sentinel))
        (fun x i ↦ TWE.Name.toWord (.var (N x i))) width α ↔
      α.sat m := by
  have hwords : ∀ S : SetTerm Γ V,
      S.encodingWords (fun x i ↦ TWE.Name.toWord (.var (N x i))) width =
      (S.encodingNames N width).map TWE.Name.toWord := fun S ↦ by
    simp [SetTerm.encodingWords, SetTerm.encodingNames, List.map_flatMap, Function.comp_def]
  have hS := eval_eq_encodedSet_encodingNames m N width (m.σName sentinel)
  rcases α with ⟨_ | _, S, S'⟩ | ⟨_ | _, a, S⟩ <;>
    simp only [SetAtom.variables, SetAtom.names, List.mem_append, List.mem_cons, or_imp,
      forall_and, forall_eq] at hvals hnames <;>
    simp only [setAtomEncodingFormula, SetAtom.sat, hwords, Bool.false_eq_true, ite_false,
      ite_true, Formula.sat, sat_setSubsetFormula, sat_setMembershipFormula,
      ← Finset.Subset.antisymm_iff]
  · rw [hS S hvals.1 hnames.1, hS S' hvals.2 hnames.2]
  · rw [hS S hvals.1 hnames.1, hS S' hvals.2 hnames.2]
  · rw [← hS S hvals hnames.2, ← sat_setMembershipFormula m sentinel]
    simp only [setMembershipFormula, sat_all, sat_any, Formula.sat,
      WE.Model.sat_wordEq_iff, not_exists, not_and]
    exact forall₂_congr fun _ _ ↦ by tauto
  · rw [hS S hvals hnames.2]

end Encoding

section Names

variable [TWE.Vars.Comparable V] {U : TWE.Free V}

theorem SetTerm.free_subset_of_mem_names {S : SetTerm Γ V} (hS : S.free ⊆ U) :
    ∀ a ∈ S.names, a.free ⊆ U := by
  induction S with
  | var x => simp [SetTerm.names]
  | empty => simp [SetTerm.names]
  | insert a S ih =>
      obtain ⟨ha, hS⟩ := TWE.Free.union_subset hS
      simpa [SetTerm.names] using ⟨ha, ih hS⟩

theorem SetAtom.free_subset_of_mem_names {α : SetAtom Γ V} (hα : α.free ⊆ U) :
    ∀ a ∈ α.names, a.free ⊆ U := by
  rcases α with ⟨_, S, S'⟩ | ⟨_, a, S⟩
  · obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset hα
    simpa [SetAtom.names, or_imp, forall_and] using
      ⟨SetTerm.free_subset_of_mem_names h₁, SetTerm.free_subset_of_mem_names h₂⟩
  · obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset hα
    simpa [SetAtom.names] using ⟨h₁, SetTerm.free_subset_of_mem_names h₂⟩

end Names

theorem exists_finset_card_le_setWordBound [Ord Γ] [DecidableEq Γ] [Nonempty Γ] (m : WordModel Γ V)
    (atoms : List (SetAtom Γ V)) (hsat : ∀ α ∈ atoms, α.sat m) :
    ∃ U : Finset Γ, U.card ≤ setWordBound atoms ∧
      (∀ a ∈ atoms.flatMap SetAtom.names, m.toTWE.evalName a ∈ U) ∧
      ∀ α ∈ atoms, α.sat (withSets m fun x ↦ m.σSet x ∩ U) := by
  have : ∀ α ∈ atoms.filter SetAtom.isDisequality, ∃ w : Γ, ∀ S S', α = .eq false S S' →
      (w ∈ S.eval m ↔ w ∉ S'.eval m) := by
    intro α hα
    obtain ⟨hα, hdis⟩ := List.mem_filter.1 hα
    rcases α with ⟨_ | _, S, S'⟩ | _ <;> simp [SetAtom.isDisequality] at hdis
    have hne : S.eval m ≠ S'.eval m := by
      simpa [SetAtom.sat] using hsat _ hα
    obtain ⟨w, hw⟩ := not_forall.1 (mt Finset.ext hne)
    exact ⟨w, by rintro _ _ ⟨⟩; tauto⟩
  choose! w hw using this
  let U := ((atoms.flatMap SetAtom.names).map m.toTWE.evalName).toFinset ∪
    ((atoms.filter SetAtom.isDisequality).map w).toFinset
  have hnames : ∀ a ∈ atoms.flatMap SetAtom.names, m.toTWE.evalName a ∈ U := fun a ha ↦
    Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map_of_mem ha))
  refine ⟨U, (Finset.card_union_le _ _).trans (Nat.add_le_add
    ((List.toFinset_card_le _).trans (by simp)) ((List.toFinset_card_le _).trans (by simp))),
    hnames, fun α hα ↦ ?_⟩
  have hname := evalName_toTWE_withSets m fun x ↦ m.σSet x ∩ U
  have hrestrict : ∀ S : SetTerm Γ V, (∀ a ∈ S.names, m.toTWE.evalName a ∈ U) →
      S.eval (withSets m fun x ↦ m.σSet x ∩ U) = S.eval m ∩ U := by
    intro S hS
    induction S with
    | var x => rfl
    | empty => simp [SetTerm.eval]
    | insert a S ih =>
        simp only [SetTerm.names, List.forall_mem_cons] at hS
        rw [SetTerm.eval, SetTerm.eval, ih hS.2, hname]
        ext b
        by_cases hb : b = m.toTWE.evalName a <;> simp [hb, hS.1]
  have hα' := hsat α hα
  have hαnames : ∀ a ∈ α.names, m.toTWE.evalName a ∈ U := fun a ha ↦
    hnames a (List.mem_flatMap.2 ⟨α, hα, ha⟩)
  rcases α with ⟨_ | _, S, S'⟩ | ⟨_ | _, a, S⟩ <;>
    simp only [SetAtom.names, List.mem_append, List.mem_cons, or_imp, forall_and,
      forall_eq] at hαnames <;>
    simp only [SetAtom.sat, Bool.false_eq_true, ite_false, ite_true, hname] at hα' ⊢
  · rw [hrestrict S hαnames.1, hrestrict S' hαnames.2]
    have hwU : w (.eq false S S') ∈ U := Finset.mem_union_right _
      (List.mem_toFinset.2 (List.mem_map_of_mem (List.mem_filter.2 ⟨hα, rfl⟩)))
    have := hw _ (List.mem_filter.2 ⟨hα, rfl⟩) S S' rfl
    intro h
    have := Finset.ext_iff.1 h (w (.eq false S S'))
    simp only [Finset.mem_inter, hwU, and_true] at this
    tauto
  · rw [hrestrict S hαnames.1, hrestrict S' hαnames.2, hα']
  · rw [hrestrict S hαnames.2]
    simp [hα']
  · rw [hrestrict S hαnames.2]
    exact Finset.mem_inter.2 ⟨hα', hαnames.1⟩

theorem exists_σName_encoding [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (σName : V.Name → Γ) (W : TWE.Free V) (width : Nat) (setVars : List V.Set)
    (sets : V.Set → Finset Γ) (c : Γ) (hc : ∀ x, c ∉ sets x)
    (hcard : ∀ x, (sets x).card ≤ width) :
    ∃ f : V.Name → Γ, (∀ y ∈ W.name, f y = σName y) ∧ f (Fresh.fresh W.name) = c ∧
      ∀ x ∈ setVars,
        ((List.range width).map fun i ↦ f (((freshSequences setVars width).run
          { W with name := insert (Fresh.fresh W.name) W.name }).1 x i)).toFinset.erase c =
            sets x ∧
        ∀ j < width, ∀ i < j,
          f (((freshSequences setVars width).run
            { W with name := insert (Fresh.fresh W.name) W.name }).1 x i) = c ∨
          f (((freshSequences setVars width).run
            { W with name := insert (Fresh.fresh W.name) W.name }).1 x j) = c ∨
          f (((freshSequences setVars width).run
            { W with name := insert (Fresh.fresh W.name) W.name }).1 x i) ≠
            f (((freshSequences setVars width).run
              { W with name := insert (Fresh.fresh W.name) W.name }).1 x j) := by
  classical
  obtain ⟨names, hnodup, hfresh, hN⟩ := exists_nodup_names_freshSequences setVars width
    { W with name := insert (Fresh.fresh W.name) W.name }
  generalize ((freshSequences setVars width).run
    { W with name := insert (Fresh.fresh W.name) W.name }).1 = N at hN ⊢
  generalize hsentinel : (Fresh.fresh W.name : V.Name) = sentinel at hfresh ⊢
  have hsentinelW : sentinel ∉ W.name := hsentinel ▸ Fresh.fresh_notMem _
  let seq := fun x ↦ (sets x).toList
  let f : V.Name → Γ := fun y ↦
    if y = sentinel then c
    else if y ∈ names then
      match setVars[names.idxOf y / width]? with
      | some x => (seq x).getD (names.idxOf y % width) c
      | none => c
    else σName y
  have hseq : ∀ x ∈ setVars, ∀ i < width, f (N x i) = (seq x)[i]?.getD c := by
    intro x hx i hi
    obtain ⟨hk, hNxi⟩ := hN x hx i hi
    have hmem : names[setVars.idxOf x * width + i] ∈ names := List.getElem_mem hk
    have hne : names[setVars.idxOf x * width + i] ≠ sentinel := fun h ↦
      hfresh _ hmem (h ▸ Finset.mem_insert_self _ _)
    have hdiv : (setVars.idxOf x * width + i) / width = setVars.idxOf x := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
    have hmod : (setVars.idxOf x * width + i) % width = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [hNxi, f, ite_eq_right hne, ite_eq_left hmem, hnodup.idxOf_getElem, hdiv, hmod,
      List.getElem?_idxOf hx]
    exact List.getD_eq_getElem?_getD
  refine ⟨f, fun y hy ↦ ?_, by simp [f], fun x hx ↦ ⟨?_, ?_⟩⟩
  · have h₁ : y ≠ sentinel := fun h ↦ hsentinelW (h ▸ hy)
    have h₂ : y ∉ names := fun h ↦ hfresh y h (Finset.mem_insert_of_mem hy)
    simp [f, h₁, h₂]
  · ext a
    simp only [Finset.mem_erase, List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨hac, i, hi, rfl⟩
      rw [hseq x hx i hi] at hac ⊢
      have hlt : i < (seq x).length := by
        by_contra h
        simp [List.getElem?_eq_none (by omega : (seq x).length ≤ i)] at hac
      simpa [List.getElem?_eq_getElem hlt, seq] using
        Finset.mem_toList.1 (List.getElem_mem (l := (sets x).toList) hlt)
    · intro ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 ha)
      have hiw : i < width := by
        have := hcard x
        rw [Finset.length_toList] at hi
        omega
      refine ⟨fun h ↦ hc x (h ▸ ha), i, hiw, ?_⟩
      rw [hseq x hx i hiw]
      simp [seq, List.getElem?_eq_getElem hi]
  · intro j hj i hij
    rw [hseq x hx i (by omega), hseq x hx j hj]
    by_cases hj' : j < (seq x).length
    · right; right
      rw [List.getElem?_eq_getElem hj', List.getElem?_eq_getElem (by omega)]
      exact fun h ↦ (Nat.ne_of_lt hij) ((Finset.nodup_toList _).getElem_inj_iff.1 h)
    · exact Or.inr (Or.inl (by simp [List.getElem?_eq_none (by omega : (seq x).length ≤ j)]))

/-- `Infinite Γ` supplies a value for the sentinel `#` that no set of the model contains. -/
theorem run_encodeSets_equisat [Infinite Γ] [Ord Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (β : Conj Γ V)
    (hβ : ∀ α ∈ β, α.EntriesEliminated) {W : TWE.Free V} (hW : β.free ⊆ W) :
    Guess.SAT ((encodeSets β).run W).1 ↔ β.SAT := by
  have hrest : ∀ α ∈ β.filter (·.set?.isNone), α ∈ β := fun α hα ↦ (List.mem_filter.1 hα).1
  let sentinel : V.Name := Fresh.fresh W.name
  let N : V.Set → Nat → V.Name := ((freshSequences (β.sets.flatMap SetAtom.variables)
    (setWordBound β.sets)).run { W with name := insert sentinel W.name }).1
  have hrun : ((encodeSets β).run W).1 =
      ((⋀ α ∈ β.filter (·.set?.isNone), (α : Guess (Conj Γ V))) ∧
        ⌜setEncodingFormula (TWE.Name.toWord (.var sentinel))
          (fun x i ↦ TWE.Name.toWord (.var (N x i)))
          β.sets⌝) := run_encodeSets β W
  simp only [hrun, Guess.SAT, Conj.SAT, Guess.sat_and, Guess.sat_all,
    InjectAtom.inject_guess, Guess.sat_atom]
  constructor
  · rintro ⟨m, hkept, henc⟩
    simp only [Atom.sat, setEncodingFormula, Formula.sat, sat_all, WE.Model.sat_wordEq_iff,
      Name.evalWord_toWord, evalName_toTWE_var, List.cons.injEq, and_true] at henc
    obtain ⟨hnames, -, hencoded⟩ := henc
    let enc := fun x ↦ encodedSet m (m.σName sentinel)
      ((List.range (setWordBound β.sets)).map fun i ↦ .var (N x i))
    refine ⟨withSets m enc, fun α hα ↦ ?_⟩
    have hEE := hβ α hα
    rcases α with F | ⟨_ | _, ℓ, h⟩ | _ | _ | a | _ <;> simp [Atom.EntriesEliminated] at hEE
    · exact hkept _ (List.mem_filter.2 ⟨hα, rfl⟩)
    · exact hkept _ (List.mem_filter.2 ⟨hα, rfl⟩)
    · exact (sat_setAtomEncodingFormula (withSets m enc) sentinel N _ a (fun x _ ↦ rfl)
        fun b hb h ↦ hnames b (List.mem_flatMap.2 ⟨a, Conj.mem_sets.2 hα, hb⟩)
          ((evalName_toTWE_withSets m enc b).symm.trans h).symm).1
        (hencoded a (Conj.mem_sets.2 hα))
  · rintro ⟨m, hsat⟩
    have hatoms : ∀ α ∈ β.sets, α.free ⊆ W ∧ α.sat m := fun α hα ↦
      ⟨Free.Subset.trans (Atom.free_subset_of_mem (Conj.mem_sets.1 hα)) hW,
        hsat _ (Conj.mem_sets.1 hα)⟩
    obtain ⟨U, hU, hUnames, hUsat⟩ :=
      exists_finset_card_le_setWordBound m β.sets fun α hα ↦ (hatoms α hα).2
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset U
    obtain ⟨f, hfW, hfc, hseqs⟩ := exists_σName_encoding m.σName W
      (setWordBound β.sets) (β.sets.flatMap SetAtom.variables) (fun x ↦ m.σSet x ∩ U) c
      (fun x hx ↦ hc (Finset.mem_inter.1 hx).2)
      (fun x ↦ (Finset.card_le_card Finset.inter_subset_right).trans hU)
    let m' : WordModel Γ V := { m with σName := f }
    have hm : m ≡[W] m' :=
      ⟨fun y hy ↦ (hfW y (Finset.mem_coe.1 hy)).symm, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
        fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    have hσ : m'.σName sentinel = c := hfc
    have hnames : ∀ a ∈ β.sets.flatMap SetAtom.names, m'.toTWE.evalName a ≠ c := by
      intro a ha
      obtain ⟨α, hα, ha'⟩ := List.mem_flatMap.1 ha
      rw [← TWE.Model.evalName_congr hm.toTWE
        (SetAtom.free_subset_of_mem_names (hatoms α hα).1 a ha')]
      exact fun h ↦ hc (h ▸ hUnames a ha)
    refine ⟨m', fun α hα ↦ (Atom.sat_congr hm (Free.Subset.trans
      (Atom.free_subset_of_mem (hrest α hα)) hW)).1 (hsat α (hrest α hα)), ?_⟩
    simp only [Atom.sat, setEncodingFormula, Formula.sat, sat_all, WE.Model.sat_wordEq_iff,
      Name.evalWord_toWord, evalName_toTWE_var, List.cons.injEq, and_true, List.mem_range, hσ]
    refine ⟨fun a ha h ↦ hnames a ha h.symm, fun x hx j hj i hi ↦ (hseqs x hx).2 j hj i hi,
      fun α hα ↦ ?_⟩
    let m'' := withSets m' fun x ↦ m.σSet x ∩ U
    refine (sat_setAtomEncodingFormula m'' sentinel N (setWordBound β.sets) α (fun x hx ↦ ?_)
      fun a ha ↦ ?_).2 ?_
    · have h := (hseqs x (List.mem_flatMap.2 ⟨α, hα, hx⟩)).1
      change m.σSet x ∩ U = ((List.map (fun i ↦ TWE.Name.var (N x i))
        (List.range (setWordBound β.sets))).map m''.toTWE.evalName).toFinset.erase
          (m''.σName sentinel)
      rw [List.map_map, show m''.σName sentinel = c from hfc]
      exact h.symm
    · rw [evalName_toTWE_withSets, show m''.σName sentinel = c from hfc]
      exact hnames a (List.mem_flatMap.2 ⟨α, hα, ha⟩)
    · have hm'' : withSets m (fun x ↦ m.σSet x ∩ U) ≡[W] m'' :=
        ⟨hm.1, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
      exact (SetAtom.sat_congr hm'' (hatoms α hα).1).1 (hUsat α hα)

theorem rewriteAtoms_rewriteSetDisequality_mem_entriesEliminated [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] (β : Conj Γ V) (hβ : ∀ α ∈ β, α.EntriesEliminated) :
    (rewriteAtoms rewriteSetDisequality β).AllAtoms Atom.EntriesEliminated := by
  refine allAtoms_rewriteAtoms (fun α U hα ↦ ?_) β hβ
  rcases α with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | _
  all_goals try exact Guess.AllAtoms.atom hα
  simp only [rewriteSetDisequality, FreshM.run_bind, run_freshName, FreshM.run_pure]
  all_atoms <;> trivial

theorem run_encodeSets_mem_setsEncoded [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (β : Conj Γ V)
    (hβ : ∀ α ∈ β, α.EntriesEliminated) (W : TWE.Free V) :
    Guess.AllAtoms Atom.SetsEncoded ((encodeSets β).run W).1 := by
  rw [run_encodeSets]
  refine Guess.AllAtoms.and (Guess.AllAtoms.all fun α hα ↦ Guess.AllAtoms.inject ?_)
    (Guess.AllAtoms.inject trivial)
  obtain ⟨hα, hnone⟩ := List.mem_filter.1 hα
  have := hβ α hα
  rcases α with _ | ⟨T, _, _⟩ | _ | _ | _ | _ <;> (try cases T) <;>
    simp_all [Atom.EntriesEliminated, Atom.SetsEncoded, Atom.set?]

end ToWE

end Linear

end TWE

end Accordion

end
