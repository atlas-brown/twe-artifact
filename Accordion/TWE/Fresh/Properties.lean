module

public import Accordion.TWE.Fresh
public import Accordion.TWE.Properties

@[expose] public section

namespace Accordion

namespace Fresh

variable {α : Type} [Fresh α] {s t : Finset α} {a : α}

theorem ne_fresh_of_mem (h : a ∈ s) : a ≠ fresh s :=
  fun e => fresh_notMem s (e ▸ h)

theorem fresh_notMem_of_subset (h : t ⊆ s) : fresh s ∉ t :=
  fun ht => fresh_notMem s (h ht)

end Fresh

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

namespace Free

theorem subset_iff {U U' : Free V} :
    U ⊆ U' ↔ U.name ⊆ U'.name ∧ U.comp ⊆ U'.comp ∧ U.path ⊆ U'.path ∧ U.loc ⊆ U'.loc ∧
      U.set ⊆ U'.set ∧ U.tree ⊆ U'.tree := Iff.rfl

@[simp] theorem name_empty : (∅ : Free V).name = ∅ := rfl
@[simp] theorem comp_empty : (∅ : Free V).comp = ∅ := rfl
@[simp] theorem path_empty : (∅ : Free V).path = ∅ := rfl
@[simp] theorem loc_empty : (∅ : Free V).loc = ∅ := rfl
@[simp] theorem set_empty : (∅ : Free V).set = ∅ := rfl
@[simp] theorem tree_empty : (∅ : Free V).tree = ∅ := rfl

theorem empty_subset (U : Free V) : ∅ ⊆ U :=
  ⟨Finset.empty_subset _, Finset.empty_subset _, Finset.empty_subset _, Finset.empty_subset _,
    Finset.empty_subset _, Finset.empty_subset _⟩

theorem Subset.refl (U : Free V) : U ⊆ U :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _,
    Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩

theorem Subset.trans {U U' U'' : Free V} (h : U ⊆ U') (h' : U' ⊆ U'') : U ⊆ U'' :=
  ⟨Finset.Subset.trans h.1 h'.1, Finset.Subset.trans h.2.1 h'.2.1,
    Finset.Subset.trans h.2.2.1 h'.2.2.1, Finset.Subset.trans h.2.2.2.1 h'.2.2.2.1,
    Finset.Subset.trans h.2.2.2.2.1 h'.2.2.2.2.1,
    Finset.Subset.trans h.2.2.2.2.2 h'.2.2.2.2.2⟩

variable [TWE.Vars.Comparable V]

theorem subset_union_left {U v : Free V} : U ⊆ U ∪ v :=
  ⟨Finset.subset_union_left, Finset.subset_union_left, Finset.subset_union_left,
    Finset.subset_union_left, Finset.subset_union_left, Finset.subset_union_left⟩

theorem subset_union_right {U v : Free V} : v ⊆ U ∪ v :=
  ⟨Finset.subset_union_right, Finset.subset_union_right, Finset.subset_union_right,
    Finset.subset_union_right, Finset.subset_union_right, Finset.subset_union_right⟩

@[simp] theorem name_union (U U' : Free V) : (U ∪ U').name = U.name ∪ U'.name := rfl
@[simp] theorem comp_union (U U' : Free V) : (U ∪ U').comp = U.comp ∪ U'.comp := rfl
@[simp] theorem path_union (U U' : Free V) : (U ∪ U').path = U.path ∪ U'.path := rfl
@[simp] theorem loc_union (U U' : Free V) : (U ∪ U').loc = U.loc ∪ U'.loc := rfl
@[simp] theorem set_union (U U' : Free V) : (U ∪ U').set = U.set ∪ U'.set := rfl
@[simp] theorem tree_union (U U' : Free V) : (U ∪ U').tree = U.tree ∪ U'.tree := rfl

theorem union_subset_iff {U v w : Free V} : U ∪ v ⊆ w ↔ U ⊆ w ∧ v ⊆ w :=
  ⟨fun h => ⟨Subset.trans subset_union_left h, Subset.trans subset_union_right h⟩, fun ⟨h, h'⟩ =>
    ⟨Finset.union_subset h.1 h'.1, Finset.union_subset h.2.1 h'.2.1,
      Finset.union_subset h.2.2.1 h'.2.2.1, Finset.union_subset h.2.2.2.1 h'.2.2.2.1,
      Finset.union_subset h.2.2.2.2.1 h'.2.2.2.2.1,
      Finset.union_subset h.2.2.2.2.2 h'.2.2.2.2.2⟩⟩

theorem union_subset {U v w : Free V} (h : U ∪ v ⊆ w) : U ⊆ w ∧ v ⊆ w :=
  union_subset_iff.1 h

end Free

section

variable [TWE.Vars.Comparable V]

theorem Name.free_comp_path (A : Name Γ V) : A.free.comp = ∅ ∧ A.free.path = ∅ := by
  cases A <;> exact ⟨rfl, rfl⟩

theorem Tree.free_comp_path (T : Tree V) : T.free.comp = ∅ ∧ T.free.path = ∅ := by
  induction T <;> simp_all [Tree.free]

theorem Set.free_comp_path (S : Set Γ V) : S.free.comp = ∅ ∧ S.free.path = ∅ := by
  induction S <;> simp_all [Set.free, Name.free_comp_path, Tree.free_comp_path]

end

namespace Model

theorem EqOn.refl (m : Model Γ V) (U : Free V) : m ≡[U] m :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem EqOn.trans {m m' m'' : Model Γ V} {U : Free V} (h : m ≡[U] m') (h' : m' ≡[U] m'') :
    m ≡[U] m'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.1.trans h'.2.2.2.2.1,
    h.2.2.2.2.2.trans h'.2.2.2.2.2⟩

theorem EqOn.mono {m m' : Model Γ V} {U U' : Free V} (h : m ≡[U'] m') (hu : U ⊆ U') :
    m ≡[U] m' :=
  ⟨h.1.mono (Finset.coe_subset.mpr hu.1), h.2.1.mono (Finset.coe_subset.mpr hu.2.1),
    h.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.1),
    h.2.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.2.1),
    h.2.2.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.2.2.1),
    h.2.2.2.2.2.mono (Finset.coe_subset.mpr hu.2.2.2.2.2)⟩

variable [TWE.Vars.Comparable V] {m m' : Model Γ V} {U : Free V}

theorem evalName_congr (h : m ≡[U] m') {a : Name Γ V} (ha : a.free ⊆ U) :
    m.evalName a = m'.evalName a := by
  cases a with
  | name => rfl
  | var x => exact h.1 (Finset.mem_coe.mpr (ha.1 (Finset.mem_singleton_self x)))

theorem evalComponent_congr (h : m ≡[U] m') {b : Component Γ V}
    (hb : b.free ⊆ U) : m.evalComponent b = m'.evalComponent b := by
  cases b with
  | name a => exact congrArg _ (evalName_congr h hb)
  | var x => exact h.2.1 (Finset.mem_coe.mpr (hb.2.1 (Finset.mem_singleton_self x)))
  | _ => rfl

theorem evalPath_congr (h : m ≡[U] m') {p : Path Γ V}
    (hp : p.free ⊆ U) : m.evalPath p = m'.evalPath p := by
  induction p with
  | nil => rfl
  | init b => exact congrArg _ (evalComponent_congr h hp)
  | join p q ihp ihq =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset hp
      simp only [evalPath, ihp h₁, ihq h₂]
  | loc l => exact h.2.2.2.1 (Finset.mem_coe.mpr (hp.2.2.2.1 (Finset.mem_singleton_self l)))
  | var x => exact h.2.2.1 (Finset.mem_coe.mpr (hp.2.2.1 (Finset.mem_singleton_self x)))
  | norm p ih => exact congrArg _ (ih hp)

theorem congr_setName {x : V.Name} {a : Γ} (hx : x ∉ U.name) : m ≡[U] m[x ↦ a] := by
  refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [setName, this]

theorem congr_setComp {x : V.Comp} {b : Accordion.Component Γ} (hx : x ∉ U.comp) :
    m ≡[U] m[x ↦ b] := by
  refine ⟨fun _ _ => rfl, fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [setComp, this]

theorem congr_setPath {x : V.Path} {p : Accordion.Path Γ} (hx : x ∉ U.path) :
    m ≡[U] m[x ↦ p] := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [setPath, this]

theorem congr_setLoc {l : V.Loc} {p : Accordion.Path Γ} (hl : l ∉ U.loc) :
    m ≡[U] m[l ↦ p] := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun y hy => ?_, fun _ _ => rfl,
    fun _ _ => rfl⟩
  have : y ≠ l := by rintro rfl; exact hl (Finset.mem_coe.mp hy)
  simp [setLoc, this]

theorem congr_setSet {x : V.Set} {s : Finset Γ} (hx : x ∉ U.set) : m ≡[U] m[x ↦ s] := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun y hy => ?_,
    fun _ _ => rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [setSet, this]

variable [Ord Γ]

theorem evalTree_congr (h : m ≡[U] m') {t : Tree V} (ht : t.free ⊆ U) :
    m.evalTree t = m'.evalTree t := by
  induction t with
  | var x => exact congrArg _ (h.2.2.2.2.2
      (Finset.mem_coe.mpr (ht.2.2.2.2.2 (Finset.mem_singleton_self x))))
  | file | emptyDirc | abst => rfl
  | select t l ih =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset ht
      have hl := h.2.2.2.1 (Finset.mem_coe.mpr (h₂.2.2.2.1 (Finset.mem_singleton_self l)))
      simp only [evalTree, ih h₁, hl]
  | update t l t' ih ih' =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset ht
      obtain ⟨h₁, h₃⟩ := Free.union_subset h₁
      have hl := h.2.2.2.1 (Finset.mem_coe.mpr (h₃.2.2.2.1 (Finset.mem_singleton_self l)))
      simp only [evalTree, ih h₁, ih' h₂, hl]

theorem evalNameSet_congr [DecidableEq Γ] (h : m ≡[U] m')
    {s : Set Γ V} (hs : s.free ⊆ U) :
    m.evalNameSet s = m'.evalNameSet s := by
  induction s with
  | var r => exact congrArg _ (h.2.2.2.2.1
      (Finset.mem_coe.mpr (hs.2.2.2.2.1 (Finset.mem_singleton_self r))))
  | empty => rfl
  | insert a s ih =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset hs
      simp only [evalNameSet, ih h₂, evalName_congr h h₁]
  | entries t => simp only [evalNameSet, evalTree_congr h hs]

theorem sat_congr [DecidableEq Γ] (h : m ≡[U] m') {φ : Formula Γ V} (hφ : φ.free ⊆ U) :
    (m ⊨ φ) ↔ (m' ⊨ φ) := by
  induction φ with
  | top | bot => exact Iff.rfl
  | conj φ ψ ihφ ihψ =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
      exact and_congr (ihφ h₁) (ihψ h₂)
  | disj φ ψ ihφ ihψ =>
      obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
      exact or_congr (ihφ h₁) (ihψ h₂)
  | neg φ ih => exact not_congr (ih hφ)
  | atom a =>
      change m.satAtom a ↔ m'.satAtom a
      cases a with
      | pathEq p q =>
          obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
          simp only [satAtom, evalPath_congr h h₁, evalPath_congr h h₂]
      | pathIsLin p => simp only [satAtom, evalPath_congr h hφ]
      | treeWalk p t l =>
          obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
          obtain ⟨h₃, h₄⟩ := Free.union_subset h₁
          have hl := h.2.2.2.1 (Finset.mem_coe.mpr (h₂.2.2.2.1 (Finset.mem_singleton_self l)))
          simp only [satAtom, evalTree_congr h h₃, evalPath_congr h h₄, hl]
      | treeShape t s => simp only [satAtom, evalTree_congr h hφ]
      | setEq s s' =>
          obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
          simp only [satAtom, evalNameSet_congr h h₁, evalNameSet_congr h h₂]
      | setMem a s =>
          obtain ⟨h₁, h₂⟩ := Free.union_subset hφ
          simp only [satAtom, evalNameSet_congr h h₂, evalName_congr h h₁]

end Model

@[simp] theorem FreshM.run_pure {α : Type} (a : α) (U : TWE.Free V) :
    (pure a : FreshM V α).run U = (a, U) :=
  rfl

@[simp] theorem FreshM.run_bind {α β : Type} (x : FreshM V α) (f : α → FreshM V β)
    (U : TWE.Free V) : (x >>= f).run U = (f (x.run U).1).run (x.run U).2 := rfl

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

@[simp] theorem run_freshName (U : TWE.Free V) :
    (freshName : FreshM V V.Name).run U =
      (Fresh.fresh U.name, { U with name := insert (Fresh.fresh U.name) U.name }) := rfl

@[simp] theorem run_freshPath (U : TWE.Free V) :
    (freshPath : FreshM V V.Path).run U =
      (Fresh.fresh U.path, { U with path := insert (Fresh.fresh U.path) U.path }) := rfl

@[simp] theorem run_freshSet (U : TWE.Free V) :
    (freshSet : FreshM V V.Set).run U =
      (Fresh.fresh U.set, { U with set := insert (Fresh.fresh U.set) U.set }) := rfl

theorem subset_freshPath (U : TWE.Free V) : U ⊆ ((freshPath : FreshM V V.Path).run U).2 :=
  ⟨subset_rfl, subset_rfl, Finset.subset_insert _ _, subset_rfl, subset_rfl, subset_rfl⟩

theorem subset_freshSet (U : TWE.Free V) : U ⊆ ((freshSet : FreshM V V.Set).run U).2 :=
  ⟨subset_rfl, subset_rfl, subset_rfl, subset_rfl, Finset.subset_insert _ _, subset_rfl⟩

end TWE

end Accordion

end
