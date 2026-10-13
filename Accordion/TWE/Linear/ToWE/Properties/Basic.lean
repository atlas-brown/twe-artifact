module

public import Accordion.TWE.Linear.ToWE.Properties.Defs
public import Accordion.TWE.Linear.Properties
public import Accordion.Formula.Properties
public import Accordion.WE.Properties

@[expose] public section

namespace Accordion

namespace TWE

open Linear.ToWE (WordModel)

variable {Γ : Type} {V : TWE.Vars}

theorem Name.evalWord_toWord [Ord Γ] (m : WordModel Γ V) (a : TWE.Name Γ V) :
    m.toWE.evalWord (TWE.Name.toWord a) = [m.toTWE.evalName a] := by
  cases a <;> rfl

theorem Tree.free_subset_of_mem_updates [TWE.Vars.Comparable V] {T u : TWE.Tree V}
    (h : u ∈ T.updates) : u.free ⊆ T.free := by
  induction T with
  | select T l ih => exact Free.Subset.trans (ih h) Free.subset_union_left
  | update T l T' ih ih' =>
      simp only [TWE.Tree.updates, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Free.Subset.refl _
      · exact Free.Subset.trans (ih h)
          (Free.Subset.trans Free.subset_union_left Free.subset_union_left)
      · exact Free.Subset.trans (ih' h) Free.subset_union_right
  | _ => simp [TWE.Tree.updates] at h

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open FileTree.Focus (follow shapeFollow entriesFollow)

@[simp] theorem InjectAtom.inject_atom (α : Atom Γ V) : (InjectAtom.inject α : Atom Γ V) = α :=
  rfl

@[simp] theorem InjectAtom.inject_guess (α : Atom Γ V) :
    (InjectAtom.inject α : Guess (Conj Γ V)) = pure [α] := rfl

@[simp] theorem BigConnectives.bigConj_guess (Ds : List (Guess (Conj Γ V))) :
    BigConnectives.bigConj Ds = Guess.bigConj Ds := rfl

@[simp] theorem BigConnectives.bigDisj_guess (Ds : List (Guess (Conj Γ V))) :
    BigConnectives.bigDisj Ds = Guess.bigDisj Ds := rfl

theorem Guess.mem_and {D E : Guess (Conj Γ V)} {γ : Conj Γ V} :
    γ ∈ (D ∧ E) ↔ ∃ γ₁ ∈ D, ∃ γ₂ ∈ E, γ = γ₁ ++ γ₂ := by
  simp only [Guess.and, Guess.mem_flatMap, Guess.mem_map']
  exact ⟨fun ⟨γ₁, h₁, γ₂, h₂, h⟩ ↦ ⟨γ₁, h₁, γ₂, h₂, h.symm⟩,
    fun ⟨γ₁, h₁, γ₂, h₂, h⟩ ↦ ⟨γ₁, h₁, γ₂, h₂, h.symm⟩⟩

theorem Guess.mem_all {X : Type} {xs : List X} {F : X → Guess (Conj Γ V)} {γ : Conj Γ V}
    (h : γ ∈ ⋀ x ∈ xs, F x) :
    (∀ x ∈ xs, ∃ δ ∈ F x, δ ⊆ γ) ∧ ∀ a ∈ γ, ∃ x ∈ xs, ∃ δ ∈ F x, a ∈ δ := by
  induction xs generalizing γ with
  | nil =>
      obtain rfl : γ = [] := by simpa [BigConnectives.all, Guess.bigConj] using h
      simp
  | cons x xs ih =>
      obtain ⟨γ₁, h₁, γ₂, h₂, rfl⟩ := Guess.mem_and.1 (show γ ∈ (F x ∧ ⋀ y ∈ xs, F y) from h)
      obtain ⟨ih₁, ih₂⟩ := ih h₂
      refine ⟨?_, fun a ha ↦ ?_⟩
      · simp only [List.forall_mem_cons]
        exact ⟨⟨γ₁, h₁, List.subset_append_left _ _⟩, fun y hy ↦
          (ih₁ y hy).imp fun δ ⟨hδ, hsub⟩ ↦
            ⟨hδ, List.Subset.trans hsub (List.subset_append_right _ _)⟩⟩
      · rcases List.mem_append.1 ha with ha | ha
        · exact ⟨x, List.mem_cons_self, γ₁, h₁, ha⟩
        · obtain ⟨y, hy, δ, hδ, ha⟩ := ih₂ a ha
          exact ⟨y, List.mem_cons_of_mem _ hy, δ, hδ, ha⟩

theorem Conj.mem_words {β : Conj Γ V} {F : WordFormula Γ V} : F ∈ β.words ↔ Atom.word F ∈ β := by
  refine ⟨fun hF ↦ ?_, fun hF ↦ List.mem_filterMap.2 ⟨_, hF, rfl⟩⟩
  obtain ⟨α, hα, hF⟩ := List.mem_filterMap.1 hF
  rcases α with _ | _ | _ | _ | _ | _ <;> simp [Atom.word?] at hF
  exact hF ▸ hα

theorem Conj.mem_baseShapes {β : Conj Γ V} {s : BaseShapeAssertion Γ V} :
    s ∈ β.baseShapes ↔ s.atom ∈ β := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ List.mem_filterMap.2 ⟨_, hs, rfl⟩⟩
  obtain ⟨α, hα, hs⟩ := List.mem_filterMap.1 hs
  rcases α with _ | ⟨_ | _, _, _⟩ | _ | _ | _ | _ <;> simp [Atom.baseShape?] at hs
  exact hs ▸ hα

theorem Conj.mem_baseEntries {β : Conj Γ V} {e : BaseEntryObservation Γ V} :
    e ∈ β.baseEntries ↔ e.atom ∈ β := by
  refine ⟨fun he ↦ ?_, fun he ↦ List.mem_filterMap.2 ⟨_, he, rfl⟩⟩
  obtain ⟨α, hα, he⟩ := List.mem_filterMap.1 he
  rcases α with _ | _ | _ | ⟨_, _ | _, _⟩ | _ | _ <;> simp [Atom.baseEntries?] at he
  exact he ▸ hα

theorem Conj.mem_sets {β : Conj Γ V} {a : SetAtom Γ V} : a ∈ β.sets ↔ Atom.set a ∈ β := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ List.mem_filterMap.2 ⟨_, ha, rfl⟩⟩
  obtain ⟨α, hα, ha⟩ := List.mem_filterMap.1 ha
  rcases α with _ | _ | _ | _ | _ | _ <;> simp [Atom.set?] at ha
  exact ha ▸ hα

namespace WordModel

section

variable [Ord Γ] (m : WordModel Γ V)

@[simp] theorem σName_setName [DecidableEq V.Name] (x y : V.Name) (a : Γ) :
    (m.setName x a).σName y = if y = x then a else m.σName y := rfl
@[simp] theorem σComp_setComp [DecidableEq V.Comp] (x y : V.Comp) (a : Γ) :
    (m.setComp x a).σComp y = if y = x then a else m.σComp y := rfl
@[simp] theorem σPath_setPath [DecidableEq V.Path] (x y : V.Path) (w : WE.GroundWord Γ) :
    (m.setPath x w).σPath y = if y = x then w else m.σPath y := rfl
@[simp] theorem σLoc_setLoc [DecidableEq V.Loc] (x y : V.Loc) (w : WE.GroundWord Γ) :
    (m.setLoc x w).σLoc y = if y = x then w else m.σLoc y := rfl
@[simp] theorem σSet_setSet [DecidableEq V.Set] (x y : V.Set) (s : Finset Γ) :
    (m.setSet x s).σSet y = if y = x then s else m.σSet y := rfl

@[simp] theorem setName_frame [DecidableEq V.Name] (x : V.Name) (a : Γ) :
    (m.setName x a).σComp = m.σComp ∧ (m.setName x a).σPath = m.σPath ∧
      (m.setName x a).σLoc = m.σLoc ∧ (m.setName x a).σSet = m.σSet ∧
      (m.setName x a).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setComp_frame [DecidableEq V.Comp] (x : V.Comp) (a : Γ) :
    (m.setComp x a).σName = m.σName ∧ (m.setComp x a).σPath = m.σPath ∧
      (m.setComp x a).σLoc = m.σLoc ∧ (m.setComp x a).σSet = m.σSet ∧
      (m.setComp x a).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setPath_frame [DecidableEq V.Path] (x : V.Path) (w : WE.GroundWord Γ) :
    (m.setPath x w).σName = m.σName ∧ (m.setPath x w).σComp = m.σComp ∧
      (m.setPath x w).σLoc = m.σLoc ∧ (m.setPath x w).σSet = m.σSet ∧
      (m.setPath x w).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setLoc_frame [DecidableEq V.Loc] (x : V.Loc) (w : WE.GroundWord Γ) :
    (m.setLoc x w).σName = m.σName ∧ (m.setLoc x w).σComp = m.σComp ∧
      (m.setLoc x w).σPath = m.σPath ∧ (m.setLoc x w).σSet = m.σSet ∧
      (m.setLoc x w).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩
@[simp] theorem setSet_frame [DecidableEq V.Set] (x : V.Set) (s : Finset Γ) :
    (m.setSet x s).σName = m.σName ∧ (m.setSet x s).σComp = m.σComp ∧
      (m.setSet x s).σPath = m.σPath ∧ (m.setSet x s).σLoc = m.σLoc ∧
      (m.setSet x s).θ = m.θ := ⟨rfl, rfl, rfl, rfl, rfl⟩

end

variable [Ord Γ] {m m' m'' : WordModel Γ V} {U U' : TWE.Free V}

theorem EqOn.refl (m : WordModel Γ V) (U : TWE.Free V) : m ≡[U] m :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem EqOn.symm (h : m ≡[U] m') : m' ≡[U] m :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩

theorem EqOn.trans (h : m ≡[U] m') (h' : m' ≡[U] m'') : m ≡[U] m'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.1.trans h'.2.2.2.2.1,
    h.2.2.2.2.2.trans h'.2.2.2.2.2⟩

theorem EqOn.mono (h : m ≡[U'] m') (hu : U ⊆ U') : m ≡[U] m' :=
  ⟨h.1.mono (Finset.coe_subset.mpr hu.1), h.2.1.mono (Finset.coe_subset.mpr hu.2.1),
    h.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.1),
    h.2.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.2.1),
    h.2.2.2.2.1.mono (Finset.coe_subset.mpr hu.2.2.2.2.1),
    h.2.2.2.2.2.mono (Finset.coe_subset.mpr hu.2.2.2.2.2)⟩

theorem EqOn.toTWE (h : m ≡[U] m') : TWE.Model.EqOn m.toTWE m'.toTWE U :=
  ⟨h.1, fun _ hx ↦ congrArg Accordion.Component.name (h.2.1 hx),
    fun _ hx ↦ congrArg Path.descend (h.2.2.1 hx),
    fun _ hx ↦ congrArg Path.descend (h.2.2.2.1 hx), h.2.2.2.2.1,
    fun _ hx ↦ congrArg Subtype.val (h.2.2.2.2.2 hx)⟩

theorem EqOn.σLoc_eq (hm : m ≡[U] m') {l : V.Loc} (hl : l ∈ U.loc) : m.σLoc l = m'.σLoc l :=
  hm.2.2.2.1 (Finset.mem_coe.2 hl)

theorem EqOn.σSet_eq (hm : m ≡[U] m') {R : V.Set} (hR : R ∈ U.set) : m.σSet R = m'.σSet R :=
  hm.2.2.2.2.1 (Finset.mem_coe.2 hR)

theorem congr_setName [DecidableEq V.Name] {x : V.Name} {a : Γ} (hx : x ∉ U.name) :
    m ≡[U] m.setName x a := by
  refine ⟨fun y hy ↦ ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
    fun _ _ ↦ rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [this]

theorem congr_setComp [DecidableEq V.Comp] {x : V.Comp} {a : Γ} (hx : x ∉ U.comp) :
    m ≡[U] m.setComp x a := by
  refine ⟨fun _ _ ↦ rfl, fun y hy ↦ ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
    fun _ _ ↦ rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [this]

theorem congr_setPath [DecidableEq V.Path] {x : V.Path} {w : WE.GroundWord Γ}
    (hx : x ∉ U.path) : m ≡[U] m.setPath x w := by
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun y hy ↦ ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
    fun _ _ ↦ rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [this]

theorem congr_setLoc [DecidableEq V.Loc] {l : V.Loc} {w : WE.GroundWord Γ} (hl : l ∉ U.loc) :
    m ≡[U] m.setLoc l w := by
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun y hy ↦ ?_, fun _ _ ↦ rfl,
    fun _ _ ↦ rfl⟩
  have : y ≠ l := by rintro rfl; exact hl (Finset.mem_coe.mp hy)
  simp [this]

theorem congr_setSet [DecidableEq V.Set] {x : V.Set} {s : Finset Γ} (hx : x ∉ U.set) :
    m ≡[U] m.setSet x s := by
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun y hy ↦ ?_,
    fun _ _ ↦ rfl⟩
  have : y ≠ x := by rintro rfl; exact hx (Finset.mem_coe.mp hy)
  simp [this]

end WordModel

section Sat

variable [Ord Γ] [DecidableEq Γ] {m : WordModel Γ V}

@[simp] theorem Conj.sat_nil : Conj.sat m ([] : Conj Γ V) := by
  simp [Conj.sat]

@[simp] theorem Conj.sat_cons (α : Atom Γ V) (β : Conj Γ V) :
    Conj.sat m (α :: β) ↔ α.sat m ∧ Conj.sat m β := by
  simp [Conj.sat]

@[simp] theorem Conj.sat_append (β γ : Conj Γ V) :
    Conj.sat m (β ++ γ) ↔ Conj.sat m β ∧ Conj.sat m γ := by
  simp [Conj.sat, or_imp, forall_and]

@[simp] theorem Guess.sat_pure (β : Conj Γ V) :
    Guess.sat m (pure β : Guess (Conj Γ V)) ↔ Conj.sat m β := by
  simp [Guess.sat]

@[simp] theorem Guess.sat_append (D E : Guess (Conj Γ V)) :
    Guess.sat m (D ++ E) ↔ Guess.sat m D ∨ Guess.sat m E := by
  simp [Guess.sat, or_and_right, exists_or]

@[simp] theorem Guess.sat_or (D E : Guess (Conj Γ V)) :
    Guess.sat m (D ∨ E) ↔ Guess.sat m D ∨ Guess.sat m E :=
  Guess.sat_append D E

@[simp] theorem Guess.sat_and (D E : Guess (Conj Γ V)) :
    Guess.sat m (D ∧ E) ↔ Guess.sat m D ∧ Guess.sat m E := by
  simp only [Guess.and, Guess.sat, Guess.mem_flatMap, Guess.mem_map']
  constructor
  · rintro ⟨_, ⟨β, hβ, γ, hγ, rfl⟩, h⟩
    rw [Conj.sat_append] at h
    exact ⟨⟨β, hβ, h.1⟩, γ, hγ, h.2⟩
  · rintro ⟨⟨β, hβ, hβ'⟩, γ, hγ, hγ'⟩
    exact ⟨β ++ γ, ⟨β, hβ, γ, hγ, rfl⟩, (Conj.sat_append β γ).2 ⟨hβ', hγ'⟩⟩

@[simp] theorem Guess.sat_top : Guess.sat m (⊤ : Guess (Conj Γ V)) := by
  simp [Guess.sat]

@[simp] theorem Guess.sat_bot : ¬Guess.sat m (⊥ : Guess (Conj Γ V)) := by
  simp [Guess.sat]

@[simp] theorem Guess.sat_atom (α : Atom Γ V) :
    Guess.sat m (pure [α] : Guess (Conj Γ V)) ↔ α.sat m := by
  simp [Guess.sat]

@[simp] theorem Guess.sat_bigConj (Ds : List (Guess (Conj Γ V))) :
    Guess.sat m (Guess.bigConj Ds) ↔ ∀ D ∈ Ds, Guess.sat m D := by
  induction Ds <;> simp_all [Guess.bigConj]

@[simp] theorem Guess.sat_bigDisj (Ds : List (Guess (Conj Γ V))) :
    Guess.sat m (Guess.bigDisj Ds) ↔ ∃ D ∈ Ds, Guess.sat m D := by
  induction Ds <;> simp_all [Guess.bigDisj]

@[simp] theorem Guess.sat_all {β : Type} (xs : List β) (F : β → Guess (Conj Γ V)) :
    Guess.sat m (BigConnectives.all xs F) ↔ ∀ x ∈ xs, Guess.sat m (F x) := by
  simp [BigConnectives.all]

@[simp] theorem Guess.sat_any {β : Type} (xs : List β) (F : β → Guess (Conj Γ V)) :
    Guess.sat m (BigConnectives.any xs F) ↔ ∃ x ∈ xs, Guess.sat m (F x) := by
  simp [BigConnectives.any]

@[simp] theorem Guess.sat_flatMap {β : Type} (xs : Guess β) (F : β → Guess (Conj Γ V)) :
    Guess.sat m (xs.flatMap F) ↔ ∃ x ∈ xs, Guess.sat m (F x) := by
  simp only [Guess.sat, Guess.mem_flatMap]
  exact ⟨fun ⟨β, ⟨x, hx, hβ⟩, h⟩ ↦ ⟨x, hx, β, hβ, h⟩, fun ⟨x, hx, β, hβ, h⟩ ↦ ⟨β, ⟨x, hx, hβ⟩, h⟩⟩

theorem SetAtom.sat_withTrees (m : WordModel Γ V)
    (θ : V.Tree → { f : FileTree.Focus Γ // f.Canonical }) (a : SetAtom Γ V) :
    a.sat (m.withTrees θ) ↔ a.sat m := by
  have hname : ∀ x : TWE.Name Γ V, (m.withTrees θ).toTWE.evalName x = m.toTWE.evalName x := by
    rintro (_ | _) <;> rfl
  have hset : ∀ S : SetTerm Γ V, S.eval (m.withTrees θ) = S.eval m := by
    intro S
    induction S with
    | var x => rfl
    | empty => rfl
    | insert x S ih => simp only [SetTerm.eval, hname, ih]
  cases a <;> simp only [SetAtom.sat, hname, hset]

end Sat

section SAT

theorem flatMap_mem_fragment {P Q : Fragment Γ V} {f : Conj Γ V → Guess (Conj Γ V)}
    (hf : ∀ β : Conj Γ V, (∀ α ∈ β, P α) → (f β).AllAtoms Q)
    {D : Guess (Conj Γ V)} (hD : D ∈ P) : D.flatMap f ∈ Q := fun γ hγ ↦ by
  obtain ⟨β, hβ, hγ⟩ := Guess.mem_flatMap.1 hγ
  exact hf β (hD β hβ) γ hγ

variable [Ord Γ] [DecidableEq Γ]

theorem Guess.SAT_iff_exists (D : Guess (Conj Γ V)) : D.SAT ↔ ∃ β ∈ D, β.SAT := by
  simp only [Guess.SAT, Guess.sat, Conj.SAT]
  exact ⟨fun ⟨m, β, hβ, h⟩ ↦ ⟨β, hβ, m, h⟩, fun ⟨β, hβ, m, h⟩ ↦ ⟨m, β, hβ, h⟩⟩

theorem Guess.SAT_flatMap_iff {β : Type} (xs : Guess β) (f : β → Guess (Conj Γ V)) :
    Guess.SAT (xs.flatMap f) ↔ ∃ x ∈ xs, (f x).SAT := by
  simp only [Guess.SAT_iff_exists, Guess.mem_flatMap]
  exact ⟨fun ⟨γ, ⟨x, hx, hγ⟩, h⟩ ↦ ⟨x, hx, γ, hγ, h⟩, fun ⟨x, hx, γ, hγ, h⟩ ↦ ⟨γ, ⟨x, hx, hγ⟩, h⟩⟩

theorem Guess.flatMap_equisat {D : Guess (Conj Γ V)} {f : Conj Γ V → Guess (Conj Γ V)}
    (hf : ∀ β ∈ D, (f β).SAT ↔ β.SAT) : Guess.SAT (D.flatMap f) ↔ D.SAT := by
  rw [Guess.SAT_flatMap_iff, Guess.SAT_iff_exists D]
  exact exists_congr fun β ↦ and_congr_right (hf β)

theorem flatMap_equisat_of_mem {P : Fragment Γ V} {f : Conj Γ V → Guess (Conj Γ V)}
    (hf : ∀ β : Conj Γ V, (∀ α ∈ β, P α) → ((f β).SAT ↔ β.SAT)) {D : Guess (Conj Γ V)}
    (hD : D ∈ P) : Guess.SAT (D.flatMap f) ↔ D.SAT :=
  Guess.flatMap_equisat fun β hβ ↦ hf β (hD β hβ)

theorem Guess.updatesDefined_flatMap {D : Guess (Conj Γ V)} {f : Conj Γ V → Guess (Conj Γ V)}
    (hf : ∀ β ∈ D, (f β).UpdatesDefined) : Guess.UpdatesDefined (D.flatMap f) := fun γ hγ ↦ by
  obtain ⟨β, hβ, hγ⟩ := Guess.mem_flatMap.1 hγ
  exact hf β hβ γ hγ

end SAT

section Words

open scoped Accordion.Formula

variable {M A α : Type}

@[simp] theorem BigConnectives.bigConj_formula (Fs : List (Accordion.Formula A)) :
    BigConnectives.bigConj Fs = Accordion.Formula.bigConj Fs := rfl

@[simp] theorem BigConnectives.bigDisj_formula (Fs : List (Accordion.Formula A)) :
    BigConnectives.bigDisj Fs = Accordion.Formula.bigDisj Fs := rfl

@[simp] theorem sat_all [Sat M A] (m : M) (xs : List α) (F : α → Accordion.Formula A) :
    m ⊨ BigConnectives.all xs F ↔ ∀ x ∈ xs, m ⊨ F x := by
  simp [BigConnectives.all, Formula.sat_bigConj]

@[simp] theorem sat_any [Sat M A] (m : M) (xs : List α) (F : α → Accordion.Formula A) :
    m ⊨ BigConnectives.any xs F ↔ ∃ x ∈ xs, m ⊨ F x := by
  simp [BigConnectives.any, Formula.sat_bigDisj]

end Words

section Eval

variable [Ord Γ] (m : WordModel Γ V)

@[simp] theorem evalWord_loc (l : V.Loc) :
    m.toWE.evalWord (TWE.Path.toWord (.loc l)) = m.σLoc l := rfl

@[simp] theorem evalWord_pathVar (x : V.Path) :
    m.toWE.evalWord (TWE.Path.toWord (.var x)) = m.σPath x := rfl

@[simp] theorem evalWord_nameVar (x : V.Name) :
    m.toWE.evalWord (TWE.Name.toWord (.var x)) = [m.σName x] := rfl

@[simp] theorem evalWord_empty : m.toWE.evalWord (.empty : Word Γ V) = [] := rfl

@[simp] theorem WordModel.evalPath_append (P Q : TWE.Path Γ V) :
    WordModel.evalPath m (P ++ Q) = WordModel.evalPath m P ++ WordModel.evalPath m Q := rfl

@[simp] theorem σLoc_toTWE (ℓ : V.Loc) : m.toTWE.σLoc ℓ = (m.σLoc ℓ : Accordion.Path Γ) := rfl

@[simp] theorem evalName_toTWE_var (x : V.Name) : m.toTWE.evalName (.var x) = m.σName x := rfl

theorem evalName_toTWE_withSets (σSet : V.Set → Finset Γ) (a : TWE.Name Γ V) :
    (m.withSets σSet).toTWE.evalName a = m.toTWE.evalName a := by
  cases a <;> rfl

theorem observesShape_var_withTrees (θ : V.Tree → { f : FileTree.Focus Γ // f.Canonical })
    (x : V.Tree) (path : List Γ) (h : TWE.Shape) :
    ObservesShape (m.withTrees θ) (.var x) path h ↔ shapeFollow (θ x).1 path = some h := by
  simp [ObservesShape, WordModel.withTrees, TWE.Model.evalTree, WordModel.toTWE]

end Eval

end ToWE

end Linear

end TWE

namespace Guess

open TWE.Linear.ToWE
open scoped Accordion.Guess BigConnectives

variable {Γ : Type} {V : TWE.Vars}

namespace AllAtoms

variable {P : Atom Γ V → Prop}

theorem and {D E : Guess (Conj Γ V)} (hD : D.AllAtoms P) (hE : E.AllAtoms P) :
    (D ∧ E).AllAtoms P := by
  intro β hβ α hα
  simp only [Guess.and, Guess.mem_flatMap, Guess.mem_map'] at hβ
  obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := hβ
  exact (List.mem_append.1 hα).elim (hD β₁ h₁ α) (hE β₂ h₂ α)

theorem or {D E : Guess (Conj Γ V)} (hD : D.AllAtoms P) (hE : E.AllAtoms P) :
    (D ∨ E).AllAtoms P :=
  fun β hβ ↦ (Guess.mem_append.1 hβ).elim (hD β) (hE β)

theorem atom {α : Atom Γ V} (hα : P α) : Guess.AllAtoms P (pure [α]) := by
  simpa [Guess.AllAtoms] using hα

theorem inject {α : Atom Γ V} (hα : P α) : Guess.AllAtoms P (InjectAtom.inject α) :=
  atom hα

theorem conj {β : Conj Γ V} (hβ : ∀ α ∈ β, P α) : Guess.AllAtoms P (pure β) := by
  simpa [Guess.AllAtoms] using hβ

theorem top : Guess.AllAtoms P (⊤ : Guess (Conj Γ V)) := by
  simp [Guess.AllAtoms]

theorem bot : Guess.AllAtoms P (⊥ : Guess (Conj Γ V)) := by
  simp [Guess.AllAtoms]

theorem all {β : Type} {xs : List β} {F : β → Guess (Conj Γ V)}
    (h : ∀ x ∈ xs, (F x).AllAtoms P) : (BigConnectives.all xs F).AllAtoms P := by
  induction xs with
  | nil => exact top
  | cons x xs ih =>
      rw [List.forall_mem_cons] at h
      exact and h.1 (ih h.2)

theorem any {β : Type} {xs : List β} {F : β → Guess (Conj Γ V)}
    (h : ∀ x ∈ xs, (F x).AllAtoms P) : (BigConnectives.any xs F).AllAtoms P := by
  induction xs with
  | nil => exact bot
  | cons x xs ih =>
      rw [List.forall_mem_cons] at h
      exact or h.1 (ih h.2)

theorem flatMap {β : Type} {xs : Guess β} {F : β → Guess (Conj Γ V)}
    (h : ∀ x ∈ xs, (F x).AllAtoms P) : Guess.AllAtoms P (xs.flatMap F) := by
  intro γ hγ
  obtain ⟨x, hx, hγ⟩ := Guess.mem_flatMap.1 hγ
  exact h x hx γ hγ

theorem mono {Q : Atom Γ V → Prop} {D : Guess (Conj Γ V)} (hD : D.AllAtoms P)
    (hPQ : ∀ α, P α → Q α) : D.AllAtoms Q :=
  fun β hβ α hα ↦ hPQ α (hD β hβ α hα)

end AllAtoms

end Guess

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open FileTree.Focus (follow shapeFollow entriesFollow)
open Linear.ToWE (WordModel)

/-- Reduces `D.AllAtoms P` to `P α` for the atoms `α` of `D`, along the connectives of `D`. -/
scoped macro "all_atoms" : tactic => `(tactic| repeat' first
      | with_reducible apply Guess.AllAtoms.and
      | with_reducible apply Guess.AllAtoms.or
      | (with_reducible apply Guess.AllAtoms.any; intro _ _)
      | (with_reducible apply Guess.AllAtoms.all; intro _ _)
      | with_reducible apply Guess.AllAtoms.top
      | with_reducible apply Guess.AllAtoms.bot
      | with_reducible apply Guess.AllAtoms.inject
      | with_reducible apply Guess.AllAtoms.atom
      | split)

section Run

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem length_freshNames_and_nodup (n : Nat) (W : TWE.Free V) :
    ((freshNames n).run W).1.length = n ∧ ((freshNames n).run W).1.Nodup ∧
      ∀ A ∈ ((freshNames n).run W).1, A ∉ W.name := by
  induction n generalizing W with
  | zero => simp [freshNames]
  | succ n ih =>
      obtain ⟨hlen, hnodup, hfresh⟩ := ih { W with name := insert (Fresh.fresh W.name) W.name }
      simp only [freshNames, FreshM.run_bind, run_freshName, FreshM.run_pure]
      refine ⟨by simp [hlen],
        List.nodup_cons.2 ⟨fun h ↦ hfresh _ h (Finset.mem_insert_self _ _), hnodup⟩, ?_⟩
      intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact Fresh.fresh_notMem _
      · exact fun h ↦ hfresh B hB (Finset.mem_insert_of_mem h)

theorem exists_nodup_names_freshSequences {α : Type} [DecidableEq α] (xs : List α) (n : Nat)
    (W : TWE.Free V) :
    ∃ names : List V.Name, names.Nodup ∧ (∀ A ∈ names, A ∉ W.name) ∧
      ∀ x ∈ xs, ∀ i < n, ∃ h : xs.idxOf x * n + i < names.length,
        ((freshSequences xs n).run W).1 x i = names[xs.idxOf x * n + i] := by
  obtain ⟨hlen, hnodup, hfresh⟩ := length_freshNames_and_nodup (xs.length * n)
    { W with name := insert (Fresh.fresh W.name) W.name }
  refine ⟨_, hnodup, fun A hA h ↦ hfresh A hA (Finset.mem_insert_of_mem h), fun x hx i hi ↦ ?_⟩
  have hidx := Nat.mul_le_mul_right n (Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hx))
  rw [Nat.succ_mul] at hidx
  have hlt : xs.idxOf x * n + i < ((freshNames (xs.length * n)).run
      { W with name := insert (Fresh.fresh W.name) W.name }).1.length := by
    rw [hlen]
    omega
  refine ⟨hlt, ?_⟩
  change List.getD ((freshNames (xs.length * n)).run
    { W with name := insert (Fresh.fresh W.name) W.name }).1 _ _ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

end Run

section Free

variable [TWE.Vars.Comparable V]

@[simp] theorem Conj.free_nil : Conj.free ([] : Conj Γ V) = ∅ := rfl

@[simp] theorem Conj.free_cons (α : Atom Γ V) (β : Conj Γ V) :
    Conj.free (α :: β) = α.free ∪ Conj.free β := rfl

theorem Conj.free_subset_iff {β : Conj Γ V} {U : TWE.Free V} :
    β.free ⊆ U ↔ ∀ α ∈ β, α.free ⊆ U := by
  induction β with
  | nil => simp [TWE.Free.empty_subset]
  | cons α β ih => simp [TWE.Free.union_subset_iff, ih]

theorem Atom.free_subset_of_mem {α : Atom Γ V} {β : Conj Γ V} (h : α ∈ β) : α.free ⊆ β.free :=
  Conj.free_subset_iff.1 (TWE.Free.Subset.refl _) α h

theorem Atom.free_subset_of_mem_updates {α : Atom Γ V} {u : TWE.Tree V} (h : u ∈ α.updates) :
    u.free ⊆ α.free := by
  cases α with
  | shape T ℓ sh | undefined T ℓ =>
      exact Free.Subset.trans (Tree.free_subset_of_mem_updates h) Free.subset_union_left
  | entries R T ℓ =>
      exact Free.Subset.trans (Tree.free_subset_of_mem_updates h)
        (Free.Subset.trans Free.subset_union_right Free.subset_union_left)
  | _ => simp [Atom.updates] at h

end Free

/-- Proves that variables are in use (`_ ⊆ U`, `_ ∈ U.loc`, ...) from the hypotheses of that
form, by comparing the variables of each sort. -/
scoped macro "free_vars" : tactic => `(tactic| simp_all [TWE.Free.subset_iff, Atom.free,
      SetAtom.free, SetTerm.free, WordFormula.free, Word.free, TWE.Path.toWord, TWE.Name.toWord,
      TWE.Tree.free, TWE.Name.free, Finset.union_subset_iff, Finset.insert_subset_iff])

section Congr

variable [Ord Γ] [TWE.Vars.Comparable V] {m m' : WordModel Γ V} {U : TWE.Free V}

theorem evalWord_congr (h : m ≡[U] m') {w : Word Γ V} (hw : Word.free w ⊆ U) :
    m.toWE.evalWord w = m'.toWE.evalWord w := by
  induction w with
  | empty | letter a => rfl
  | letterVar x =>
      rcases x with x | x
      · exact congrArg ([·]) (h.1 (Finset.mem_coe.2 (hw.1 (Finset.mem_singleton_self x))))
      · exact congrArg ([·]) (h.2.1 (Finset.mem_coe.2 (hw.2.1 (Finset.mem_singleton_self x))))
  | var x =>
      rcases x with x | x
      · exact h.2.2.1 (Finset.mem_coe.2 (hw.2.2.1 (Finset.mem_singleton_self x)))
      · exact h.2.2.2.1 (Finset.mem_coe.2 (hw.2.2.2.1 (Finset.mem_singleton_self x)))
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := TWE.Free.union_subset hw
      exact congrArg₂ (· ++ ·) (ihu hu) (ihv hv)

theorem sat_wordFormula_congr (h : m ≡[U] m') {F : WordFormula Γ V}
    (hF : WordFormula.free F ⊆ U) : m.toWE ⊨ F ↔ m'.toWE ⊨ F := by
  induction F with
  | top | bot => rfl
  | atom a =>
      cases a with
      | wordEq u v =>
          obtain ⟨hu, hv⟩ := TWE.Free.union_subset hF
          exact Iff.of_eq (congrArg₂ (· = ·) (evalWord_congr h hu) (evalWord_congr h hv))
  | conj φ ψ ihφ ihψ =>
      obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset hF
      exact and_congr (ihφ h₁) (ihψ h₂)
  | disj φ ψ ihφ ihψ =>
      obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset hF
      exact or_congr (ihφ h₁) (ihψ h₂)
  | neg φ ih => exact not_congr (ih hF)

theorem WordModel.evalPath_congr (h : m ≡[U] m') {P : TWE.Path Γ V} (hP : P.free ⊆ U) :
    WordModel.evalPath m P = WordModel.evalPath m' P := by
  induction P with
  | nil => rfl
  | init b =>
      cases b with
      | name a =>
          cases a with
          | name a => rfl
          | var x => exact congrArg (fun a ↦ [a]) (h.1 (hP.1 (Finset.mem_singleton_self x)))
      | var x => exact congrArg (fun a ↦ [a]) (h.2.1 (hP.2.1 (Finset.mem_singleton_self x)))
      | _ => rfl
  | join p q ihp ihq =>
      exact congrArg₂ (· ++ ·) (ihp (Free.union_subset hP).1) (ihq (Free.union_subset hP).2)
  | loc l => exact h.2.2.2.1 (hP.2.2.2.1 (Finset.mem_singleton_self l))
  | var x => exact h.2.2.1 (hP.2.2.1 (Finset.mem_singleton_self x))
  | norm p ih => exact ih hP

theorem observesShape_congr {T : TWE.Tree V} (hm : m ≡[U] m') (hT : T.free ⊆ U) (w : List Γ)
    (h : TWE.Shape) : ObservesShape m T w h ↔ ObservesShape m' T w h := by
  simp only [ObservesShape, TWE.Model.evalTree_congr hm.toTWE hT]

theorem observesEntries_congr [DecidableEq Γ] {T : TWE.Tree V} (hm : m ≡[U] m') (hT : T.free ⊆ U)
    (w : List Γ) (N : Finset Γ) : ObservesEntries m T w N ↔ ObservesEntries m' T w N := by
  simp only [ObservesEntries, TWE.Model.evalTree_congr hm.toTWE hT]

theorem Atom.definedIn_congr (h : m ≡[U] m') {α : Atom Γ V} (hα : α.free ⊆ U) :
    α.DefinedIn m ↔ α.DefinedIn m' :=
  forall₂_congr fun _ hu ↦ by
    rw [TWE.Model.evalTree_congr h.toTWE
      (Free.Subset.trans (Atom.free_subset_of_mem_updates hu) hα)]

variable [DecidableEq Γ]

theorem SetTerm.eval_congr (h : m ≡[U] m') {S : SetTerm Γ V} (hS : S.free ⊆ U) :
    S.eval m = S.eval m' := by
  induction S with
  | var x => exact h.2.2.2.2.1 (Finset.mem_coe.2 (hS.2.2.2.2.1 (Finset.mem_singleton_self x)))
  | empty => rfl
  | insert a S ih =>
      obtain ⟨ha, hS⟩ := TWE.Free.union_subset hS
      simp only [SetTerm.eval, ih hS, TWE.Model.evalName_congr h.toTWE ha]

theorem SetAtom.sat_congr (h : m ≡[U] m') {a : SetAtom Γ V} (ha : a.free ⊆ U) :
    a.sat m ↔ a.sat m' := by
  cases a with
  | eq positive S S' =>
      obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset ha
      simp only [SetAtom.sat, SetTerm.eval_congr h h₁, SetTerm.eval_congr h h₂]
  | mem positive A S =>
      obtain ⟨h₁, h₂⟩ := TWE.Free.union_subset ha
      simp only [SetAtom.sat, SetTerm.eval_congr h h₂, TWE.Model.evalName_congr h.toTWE h₁]

theorem TWESetAtom.sat_congr (h : m ≡[U] m') {a : TWESetAtom Γ V} (ha : a.free ⊆ U) :
    a.sat m ↔ a.sat m' := by
  cases a with
  | eq positive S S' =>
      have := TWE.Model.sat_congr (φ := .atom (.setEq S S')) h.toTWE ha
      simp only [TWESetAtom.sat, this]
  | mem positive A S =>
      have := TWE.Model.sat_congr (φ := .atom (.setMem A S)) h.toTWE ha
      simp only [TWESetAtom.sat, this]

theorem Atom.sat_congr (h : m ≡[U] m') {α : Atom Γ V} (hα : α.free ⊆ U) :
    α.sat m ↔ α.sat m' := by
  cases α with
  | word F => exact sat_wordFormula_congr h hα
  | shape T ℓ sh =>
      obtain ⟨hT, hℓ⟩ := TWE.Free.union_subset hα
      simp only [Atom.sat, ObservesShape, evalWord_congr h hℓ,
        TWE.Model.evalTree_congr h.toTWE hT]
  | undefined T ℓ =>
      obtain ⟨hT, hℓ⟩ := TWE.Free.union_subset hα
      simp only [Atom.sat, ObservesShape, evalWord_congr h hℓ,
        TWE.Model.evalTree_congr h.toTWE hT]
  | entries R T ℓ =>
      obtain ⟨hRT, hℓ⟩ := TWE.Free.union_subset hα
      obtain ⟨hR, hT⟩ := TWE.Free.union_subset hRT
      have hR : m.σSet R = m'.σSet R :=
        h.2.2.2.2.1 (Finset.mem_coe.2 (hR.2.2.2.2.1 (Finset.mem_singleton_self R)))
      simp only [Atom.sat, ObservesEntries, evalWord_congr h hℓ,
        TWE.Model.evalTree_congr h.toTWE hT, hR]
  | set a => exact SetAtom.sat_congr h hα
  | tweSet a => exact TWESetAtom.sat_congr h hα

theorem Conj.sat_congr (h : m ≡[U] m') {β : Conj Γ V} (hβ : ∀ α ∈ β, α.free ⊆ U) :
    Conj.sat m β ↔ Conj.sat m' β :=
  forall₂_congr fun α hα ↦ Atom.sat_congr h (hβ α hα)

theorem Guess.sat_congr (h : m ≡[U] m') {D : Guess (Conj Γ V)} (hD : D.AllAtoms (·.free ⊆ U)) :
    Guess.sat m D ↔ Guess.sat m' D :=
  exists_congr fun β ↦ and_congr_right fun hβ ↦ Conj.sat_congr h (hD β hβ)

end Congr

section PrefixMacros

open scoped Accordion.Formula WE

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (P Q : Word Γ V) (U : TWE.Free V)

theorem subset_notPrefixFormula : U ⊆ ((P ⋠ Q).run U).2 := by
  simp only [notPrefixFormula, FreshM.run_bind, run_freshName, run_freshPath, FreshM.run_pure]
  refine ⟨?_, subset_rfl, ?_, subset_rfl, subset_rfl, subset_rfl⟩ <;> intro x hx <;> simp [hx]

theorem subset_notStrictPrefixFormula : U ⊆ ((P ⊀ Q).run U).2 :=
  subset_notPrefixFormula P Q U

theorem subset_pathIncomparableFormula : U ⊆ ((P ∥ Q).run U).2 :=
  Free.Subset.trans (subset_notPrefixFormula P Q U) (subset_notPrefixFormula Q P _)

variable {P Q U}

theorem free_notPrefixFormula_subset (hP : Word.free P ⊆ U) (hQ : Word.free Q ⊆ U) :
    WordFormula.free ((P ⋠ Q).run U).1 ⊆ ((P ⋠ Q).run U).2 := by
  have hP := Free.Subset.trans hP (subset_notPrefixFormula P Q U)
  have hQ := Free.Subset.trans hQ (subset_notPrefixFormula P Q U)
  simp only [notPrefixFormula, FreshM.run_bind, run_freshName, run_freshPath, FreshM.run_pure,
    WordFormula.free, WE.Word.append_eq, Word.free, TWE.Free.union_subset_iff] at hP hQ ⊢
  simp only [hP, hQ, true_and]
  simp [TWE.Name.toWord, TWE.Path.toWord, Word.free, TWE.Free.subset_iff]

theorem free_notStrictPrefixFormula_subset (hP : Word.free P ⊆ U) (hQ : Word.free Q ⊆ U) :
    WordFormula.free ((P ⊀ Q).run U).1 ⊆ ((P ⊀ Q).run U).2 :=
  TWE.Free.union_subset_iff.2
    ⟨TWE.Free.union_subset_iff.2 ⟨Free.Subset.trans hP (subset_notPrefixFormula P Q U),
      Free.Subset.trans hQ (subset_notPrefixFormula P Q U)⟩, free_notPrefixFormula_subset hP hQ⟩

end PrefixMacros

section SatFresh

variable [Ord Γ] [DecidableEq Γ] {m : WordModel Γ V} {U : TWE.Free V}
  {D E : Guess (Conj Γ V)}

theorem SatPreserving.satPreservingIn {β : Conj Γ V} (h : SatPreserving U β D)
    (M : WordModel Γ V → Prop) : SatPreservingIn M U β D :=
  fun m _ ↦ h m

theorem SatPreservingIn.of_atom {M : WordModel Γ V → Prop} {α : Atom Γ V}
    (h : ∀ m, M m → (D.satFresh m U ↔ α.sat m)) : SatPreservingIn M U [α] D := by
  simpa [SatPreservingIn] using h

theorem SatPreserving.of_atom {α : Atom Γ V} (h : ∀ m, D.satFresh m U ↔ α.sat m) :
    SatPreserving U [α] D := by
  simpa [SatPreserving] using h

theorem Guess.satFresh_of_sat (h : Guess.sat m D) : D.satFresh m U :=
  ⟨m, .refl m U, h⟩

@[simp] theorem Guess.satFresh_bot : ¬Guess.satFresh m U (⊥ : Guess (Conj Γ V)) := by
  simp [Guess.satFresh]

theorem Guess.satFresh_or :
    (D ∨ E).satFresh m U ↔ D.satFresh m U ∨ E.satFresh m U := by
  simp only [Guess.satFresh, Guess.sat_or, and_or_left, exists_or]

variable [TWE.Vars.Comparable V]

theorem Guess.satFresh_iff_of_free_subset (hD : D.AllAtoms (·.free ⊆ U)) :
    D.satFresh m U ↔ Guess.sat m D :=
  ⟨fun ⟨_, hm, h⟩ ↦ (Guess.sat_congr hm hD).2 h, Guess.satFresh_of_sat⟩

theorem Guess.satFresh_atom {α : Atom Γ V} (hα : α.free ⊆ U) :
    Guess.satFresh m U (pure [α]) ↔ α.sat m :=
  (Guess.satFresh_iff_of_free_subset (Guess.AllAtoms.atom hα)).trans (Guess.sat_atom α)

theorem Guess.satFresh_and_of_free_subset (hD : D.AllAtoms (·.free ⊆ U)) :
    (D ∧ E).satFresh m U ↔ Guess.sat m D ∧ E.satFresh m U := by
  simp only [Guess.satFresh, Guess.sat_and]
  exact ⟨fun ⟨m', hm, hD', hE⟩ ↦ ⟨(Guess.sat_congr hm hD).2 hD', m', hm, hE⟩,
    fun ⟨hD', m', hm, hE⟩ ↦ ⟨m', hm, (Guess.sat_congr hm hD).1 hD', hE⟩⟩

theorem SatPreserving.of_free_subset {α : Atom Γ V} (hα : α.free ⊆ U) :
    SatPreserving U [α] (pure [α]) :=
  .of_atom fun _ ↦ Guess.satFresh_atom hα

end SatFresh

theorem FreshM.run_mapM {α β : Type} (f : α → FreshM V β)
    (hf : ∀ x W, W ⊆ ((f x).run W).2) :
    ∀ (xs : List α) (W : TWE.Free V),
      (∀ y ∈ ((xs.mapM f).run W).1, ∃ x ∈ xs, ∃ W', W ⊆ W' ∧ y = ((f x).run W').1) ∧
      (∀ x ∈ xs, ∃ W', W ⊆ W' ∧ ((f x).run W').1 ∈ ((xs.mapM f).run W).1) ∧
      W ⊆ ((xs.mapM f).run W).2 := by
  intro xs
  induction xs with
  | nil => simp [TWE.Free.Subset.refl]
  | cons x xs ih =>
      intro W
      have hnext := hf x W
      obtain ⟨ih₁, ih₂, ih₃⟩ := ih ((f x).run W).2
      simp only [List.mapM_cons, FreshM.run_bind, FreshM.run_pure, List.mem_cons,
        forall_eq_or_imp, exists_eq_or_imp]
      refine ⟨⟨Or.inl ⟨W, Free.Subset.refl W, rfl⟩, fun y hy ↦ ?_⟩,
        ⟨⟨W, Free.Subset.refl W, Or.inl rfl⟩, fun x' hx' ↦ ?_⟩, Free.Subset.trans hnext ih₃⟩
      · obtain ⟨x', hx', W', hW', rfl⟩ := ih₁ y hy
        exact Or.inr ⟨x', hx', W', Free.Subset.trans hnext hW', rfl⟩
      · obtain ⟨W', hW', hmem⟩ := ih₂ x' hx'
        exact ⟨W', Free.Subset.trans hnext hW', Or.inr hmem⟩

theorem Guess.satFresh_mapM_iff [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V] {X F : Type}
    (toGuess : F → Guess (Conj Γ V)) (f : X → FreshM V F) (P : WordModel Γ V → X → Prop)
    {U₀ : TWE.Free V} (hrun : ∀ x W, W ⊆ ((f x).run W).2) {xs : List X}
    (hfree : ∀ x ∈ xs, ∀ W, U₀ ⊆ W →
      (toGuess ((f x).run W).1).AllAtoms (·.free ⊆ ((f x).run W).2))
    (hf : ∀ x ∈ xs, ∀ {U W} (m : WordModel Γ V), U₀ ⊆ U → U ⊆ W →
      ((toGuess ((f x).run W).1).satFresh m U ↔ P m x))
    {U W : TWE.Free V} (m : WordModel Γ V) (hU : U₀ ⊆ U) (hW : U ⊆ W) :
    Guess.satFresh m U (⋀ y ∈ ((xs.mapM f).run W).1, toGuess y) ↔ ∀ x ∈ xs, P m x := by
  induction xs generalizing U W m with
  | nil => exact iff_of_true (Guess.satFresh_of_sat (by simp)) (by simp)
  | cons x xs ih =>
      have hP : ∀ y ∈ x :: xs, ∀ m', m ≡[U] m' → (P m' y ↔ P m y) := by
        intro y hy m' hm
        rw [← hf y hy m hU (Free.Subset.refl U), ← hf y hy m' hU (Free.Subset.refl U)]
        exact ⟨fun ⟨m'', h, hs⟩ ↦ ⟨m'', hm.trans h, hs⟩,
          fun ⟨m'', h, hs⟩ ↦ ⟨m'', hm.symm.trans h, hs⟩⟩
      have hnext := hrun x W
      have hUW' : U ⊆ ((f x).run W).2 := Free.Subset.trans hW hnext
      have hhead := hfree x List.mem_cons_self W (Free.Subset.trans hU hW)
      have hx := hf x List.mem_cons_self m hU hW
      have ih' := fun m ↦ ih (fun x hx ↦ hfree x (List.mem_cons_of_mem _ hx))
        (fun x hx ↦ hf x (List.mem_cons_of_mem _ hx)) (U := ((f x).run W).2) (W := ((f x).run W).2)
        m (Free.Subset.trans hU hUW') (Free.Subset.refl _)
      simp only [Guess.satFresh, List.mapM_cons, FreshM.run_bind, FreshM.run_pure,
        Guess.sat_all, List.forall_mem_cons] at ih' hx ⊢
      constructor
      · rintro ⟨m', hm, hy, hys⟩
        exact ⟨hx.1 ⟨m', hm, hy⟩, fun z hz ↦ (hP z (List.mem_cons_of_mem _ hz) m' hm).1
          ((ih' m').1 ⟨m', .refl _ _, hys⟩ z hz)⟩
      · rintro ⟨hy, hys⟩
        obtain ⟨m₁, hm₁, hy⟩ := hx.2 hy
        obtain ⟨m₂, hm₂, hys⟩ := (ih' m₁).2 fun z hz ↦
          (hP z (List.mem_cons_of_mem _ hz) m₁ hm₁).2 (hys z hz)
        exact ⟨m₂, hm₁.trans (hm₂.mono hUW'), (Guess.sat_congr hm₂ hhead).1 hy, hys⟩

end ToWE

end Linear

end TWE

end Accordion

end
