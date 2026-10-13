module

public import Accordion.WhileFS.Symbolic.Soundness
public import Accordion.TWE.Fresh.Properties

@[expose] public section

namespace Accordion

open scoped TWE TWE.Model Accordion.Formula

variable {Γ X : Type} {V : TWE.Vars}

namespace TWE.Free

variable [TWE.Vars.Comparable V]

theorem union_def (U v : Free V) :
    U ∪ v = ⟨U.name ∪ v.name, U.comp ∪ v.comp, U.path ∪ v.path,
      U.loc ∪ v.loc, U.set ∪ v.set, U.tree ∪ v.tree⟩ := rfl

instance : Std.Commutative (α := Free V) (· ∪ ·) :=
  ⟨fun U v => by simp [union_def, Finset.union_comm]⟩

instance : Std.Associative (α := Free V) (· ∪ ·) :=
  ⟨fun U v w => by simp [union_def, Finset.union_assoc]⟩

theorem subset_fold {α : Type} [DecidableEq α] {s : Finset α} {f : α → Free V} {x : α}
    (hx : x ∈ s) : f x ⊆ s.fold (· ∪ ·) ∅ f := by
  induction s using Finset.induction with
  | empty => cases hx
  | insert a s ha ih =>
      rw [Finset.fold_insert ha]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact subset_union_left
      · exact Subset.trans (ih hx) subset_union_right

end TWE.Free

variable [TWE.Vars.Comparable V]

def SVal.free : SVal Γ V → TWE.Free V
  | .prop Φ => Φ.free
  | .path P => P.free
  | .tree T => T.free
  | .set S => S.free

section
variable [DecidableEq X]

def SStore.free (ρ : SStore Γ X V) : TWE.Free V :=
  ρ.keys.fold (· ∪ ·) ∅ (fun x => ((ρ.lookup x).map SVal.free).getD ∅)

def SState.free (ς : SState Γ X V) : TWE.Free V :=
  ς.store.free ∪ ς.tree.free ∪ ς.π.free

theorem SVal.free_subset_of_lookup {ρ : SStore Γ X V} {x : X} {v : SVal Γ V}
    (h : ρ.lookup x = some v) : v.free ⊆ ρ.free := by
  have hx : x ∈ ρ.keys := Finmap.mem_keys.mpr (Finmap.lookup_isSome.mp (by rw [h]; rfl))
  simpa [SStore.free, h] using
    TWE.Free.subset_fold (f := fun x => ((ρ.lookup x).map SVal.free).getD ∅) hx

end

variable [Ord Γ] [DecidableEq Γ] {m m' : TWE.Model Γ V} {U : TWE.Free V}

theorem SVal.instantiate_congr (h : m ≡[U] m') {Ŝ : SVal Γ V} (hŜ : Ŝ.free ⊆ U) :
    ⟦Ŝ⟧ m = ⟦Ŝ⟧ m' := by
  cases Ŝ with
  | prop Φ => simp [SVal.instantiate, decide_eq_decide.mpr (TWE.Model.sat_congr h hŜ)]
  | path P => simp [SVal.instantiate, TWE.Model.evalPath_congr h hŜ]
  | tree T => simp [SVal.instantiate, TWE.Model.evalTree_congr h hŜ]
  | set S => simp [SVal.instantiate, TWE.Model.evalNameSet_congr h hŜ]

section
variable [DecidableEq X]

theorem SStore.instantiate_congr (h : m ≡[U] m') {ρ : SStore Γ X V} (hρ : ρ.free ⊆ U) :
    ⟦ρ⟧ m = ⟦ρ⟧ m' := by
  funext x
  cases hx : ρ.lookup x with
  | none => simp [SStore.instantiate, hx]
  | some v =>
      simp [SStore.instantiate, hx,
        SVal.instantiate_congr h (TWE.Free.Subset.trans (SVal.free_subset_of_lookup hx) hρ)]

theorem SState.instantiate_congr (h : m ≡[U] m') {ς : SState Γ X V} (hς : ς.free ⊆ U) :
    ⟦ς⟧ m = ⟦ς⟧ m' := by
  obtain ⟨hst, hπ⟩ := TWE.Free.union_subset hς
  obtain ⟨hstore, htree⟩ := TWE.Free.union_subset hst
  simp [SState.instantiate, TWE.Model.evalTree_congr h htree,
    SStore.instantiate_congr h hstore]

end

section
omit [TWE.Vars.Comparable V]

theorem SVal.instantiate_eq_bool {Ŝ : SVal Γ V} {b : Bool}
    (h : ⟦Ŝ⟧ m = some (.bool b)) : ∃ Φ, Ŝ = .prop Φ ∧ decide (m ⊨ Φ) = b := by
  rcases Ŝ with Φ | P | T | S
  · cases h; exact ⟨Φ, rfl, rfl⟩
  · cases h
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_tree_iff.mp h
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_set_eq h

theorem SVal.instantiate_eq_path {Ŝ : SVal Γ V} {p : Accordion.Path Γ}
    (h : ⟦Ŝ⟧ m = some (.path p)) : ∃ P, Ŝ = .path P ∧ m.evalPath P = p := by
  rcases Ŝ with Φ | P | T | S
  · cases h
  · cases h; exact ⟨P, rfl, rfl⟩
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_tree_iff.mp h
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_set_eq h

theorem SVal.instantiate_eq_filetype {Ŝ : SVal Γ V} {y : FileType}
    (h : ⟦Ŝ⟧ m = some (.filetype y)) :
    ∃ T τ, Ŝ = .tree T ∧ m.evalTree T = some (.tree τ) ∧ τ.fileType = y := by
  rcases Ŝ with Φ | P | T | S
  · cases h
  · cases h
  · obtain ⟨τ, hT, ⟨⟩⟩ := TWE.Model.instantiate_tree_iff.mp h; exact ⟨T, τ, rfl, hT, rfl⟩
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_set_eq h

theorem SVal.instantiate_eq_directory {Ŝ : SVal Γ V} {Δ : Finset Γ}
    (h : ⟦Ŝ⟧ m = some (.directory Δ)) :
    ∃ S, Ŝ = .set S ∧ m.evalNameSet S = some Δ := by
  rcases Ŝ with Φ | P | T | S
  · cases h
  · cases h
  · obtain ⟨_, _, ⟨⟩⟩ := TWE.Model.instantiate_tree_iff.mp h
  · obtain ⟨_, hS, ⟨⟩⟩ := TWE.Model.instantiate_set_eq h; exact ⟨S, rfl, hS⟩

end

local macro "free_subset" : tactic =>
  `(tactic| repeat first
    | exact TWE.Free.Subset.refl _
    | exact TWE.Free.subset_union_right
    | refine TWE.Free.Subset.trans ?_ TWE.Free.subset_union_left)

/-- The first subderivation may invent variables, so the second is re-run against
the enlarged support `U ∪ Φ₁.free ∪ Ŝ₁.free` and its model transported back. -/
private theorem seval_complete_pair [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq X]
    {ρ : SStore Γ X V} {e₁ e₂ : Expr Γ X} {v₁ v₂ : Val Γ} {U : TWE.Free V}
    (ih₁ : ∀ {m : TWE.Model Γ V} {v : Val Γ} (U : TWE.Free V), ρ.free ⊆ U → m.WF →
      (e₁ ⇓[⟦ρ⟧ m] v) →
      ∃ Φ Ŝ m', (e₁ ⇓[ρ] Ŝ ∣ Φ) ∧ m'.WF ∧ (m ≡[U] m') ∧ (m' ⊨ Φ) ∧ ⟦Ŝ⟧ m' = some v)
    (ih₂ : ∀ {m : TWE.Model Γ V} {v : Val Γ} (U : TWE.Free V), ρ.free ⊆ U → m.WF →
      (e₂ ⇓[⟦ρ⟧ m] v) →
      ∃ Φ Ŝ m', (e₂ ⇓[ρ] Ŝ ∣ Φ) ∧ m'.WF ∧ (m ≡[U] m') ∧ (m' ⊨ Φ) ∧ ⟦Ŝ⟧ m' = some v)
    (hu : ρ.free ⊆ U) (hm : m.WF)
    (h₁ : e₁ ⇓[⟦ρ⟧ m] v₁) (h₂ : e₂ ⇓[⟦ρ⟧ m] v₂) :
    ∃ Φ₁ Ŝ₁ Φ₂ Ŝ₂ m', (e₁ ⇓[ρ] Ŝ₁ ∣ Φ₁) ∧ (e₂ ⇓[ρ] Ŝ₂ ∣ Φ₂) ∧ m'.WF ∧ (m ≡[U] m') ∧
      (m' ⊨ Φ₁) ∧ (m' ⊨ Φ₂) ∧
      ⟦Ŝ₁⟧ m' = some v₁ ∧ ⟦Ŝ₂⟧ m' = some v₂ := by
  obtain ⟨Φ₁, Ŝ₁, m₁, hs₁, hm₁, heq₁, hsat₁, hi₁⟩ := ih₁ U hu hm h₁
  obtain ⟨Φ₂, Ŝ₂, m₂, hs₂, hm₂, heq₂, hsat₂, hi₂⟩ :=
    ih₂ (U ∪ Φ₁.free ∪ Ŝ₁.free) (TWE.Free.Subset.trans hu (by free_subset)) hm₁
      (by rwa [SStore.instantiate_congr heq₁ hu] at h₂)
  exact ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m₂, hs₁, hs₂, hm₂, heq₁.trans (heq₂.mono (by free_subset)),
    (TWE.Model.sat_congr heq₂ (by free_subset)).mp hsat₁, hsat₂,
    (SVal.instantiate_congr heq₂ (by free_subset)).symm.trans hi₁, hi₂⟩

theorem seval_complete [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq X] [TWE.Vars.Unbounded V]
    {e : Expr Γ X} {v : Val Γ} {ρ : SStore Γ X V} (U : TWE.Free V)
    (hu : ρ.free ⊆ U) (hm : m.WF) (heval : e ⇓[⟦ρ⟧ m] v) :
    ∃ Φ Ŝ m', (e ⇓[ρ] Ŝ ∣ Φ) ∧ m'.WF ∧ (m ≡[U] m') ∧ (m' ⊨ Φ) ∧ ⟦Ŝ⟧ m' = some v := by
  induction e generalizing U v m with
  | var x =>
      cases heval with
      | var hx =>
          simp only [SStore.instantiate, Option.bind_eq_some_iff] at hx
          obtain ⟨Ŝ, hlk, hinst⟩ := hx
          exact ⟨.top, Ŝ, m, SEval.var hlk, hm, TWE.Model.EqOn.refl m U, trivial, hinst⟩
  | val w =>
      cases heval with
      | val =>
          exact ⟨.top, ⌜w⌝, m, SEval.val, hm, TWE.Model.EqOn.refl m U, trivial,
            TWE.Model.embed_instantiate m w⟩
  | eq e₁ e₂ ih₁ ih₂ =>
      cases heval with
      | @eqTrue _ _ w₁ _ h₁ h₂ hv =>
          subst hv
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm h₁ h₂
          cases w₁ with
          | bool b =>
              obtain ⟨Φ₁', rfl, hΦ₁⟩ := SVal.instantiate_eq_bool hi₁
              obtain ⟨Φ₂', rfl, hΦ₂⟩ := SVal.instantiate_eq_bool hi₂
              exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.boolEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
                cases b <;> simp_all [SVal.instantiate, TWE.Formula.iff]⟩
          | path p =>
              obtain ⟨P₁, rfl, hP₁⟩ := SVal.instantiate_eq_path hi₁
              obtain ⟨P₂, rfl, hP₂⟩ := SVal.instantiate_eq_path hi₂
              exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.pathEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
                simp [SVal.instantiate, TWE.Model.satAtom, hP₁, hP₂]⟩
          | filetype y =>
              obtain ⟨T₁, τ₁, rfl, hT₁, rfl⟩ := SVal.instantiate_eq_filetype hi₁
              obtain ⟨T₂, τ₂, rfl, hT₂, hy⟩ := SVal.instantiate_eq_filetype hi₂
              exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.fileTypeEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
                cases τ₁ <;> cases τ₂ <;> simp [SVal.instantiate, TWE.Model.satAtom, hT₁, hT₂,
                  FileTree.Focus.shape, FileTree.fileType] at hy ⊢⟩
          | directory Δ =>
              obtain ⟨S₁, rfl, hS₁⟩ := SVal.instantiate_eq_directory hi₁
              obtain ⟨S₂, rfl, hS₂⟩ := SVal.instantiate_eq_directory hi₂
              exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.dirstreamEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
                simp [SVal.instantiate, TWE.Model.satAtom, hS₁, hS₂]⟩
      | @eqFalseBool _ _ b₁ b₂ h₁ h₂ hne =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm h₁ h₂
          obtain ⟨Φ₁', rfl, hΦ₁⟩ := SVal.instantiate_eq_bool hi₁
          obtain ⟨Φ₂', rfl, hΦ₂⟩ := SVal.instantiate_eq_bool hi₂
          exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.boolEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            cases b₁ <;> cases b₂ <;> simp_all [SVal.instantiate, TWE.Formula.iff]⟩
      | @eqFalsePath _ _ p₁ p₂ h₁ h₂ hne =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm h₁ h₂
          obtain ⟨P₁, rfl, hP₁⟩ := SVal.instantiate_eq_path hi₁
          obtain ⟨P₂, rfl, hP₂⟩ := SVal.instantiate_eq_path hi₂
          exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.pathEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            simp [SVal.instantiate, TWE.Model.satAtom, hP₁, hP₂, hne]⟩
      | @eqFalseFileType _ _ y₁ y₂ h₁ h₂ hne =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm h₁ h₂
          obtain ⟨T₁, τ₁, rfl, hT₁, rfl⟩ := SVal.instantiate_eq_filetype hi₁
          obtain ⟨T₂, τ₂, rfl, hT₂, rfl⟩ := SVal.instantiate_eq_filetype hi₂
          exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.fileTypeEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            cases τ₁ <;> cases τ₂ <;> simp [SVal.instantiate, TWE.Model.satAtom, hT₁, hT₂,
              FileTree.Focus.shape, FileTree.fileType] at hne ⊢⟩
      | @eqFalseDirectory _ _ Δ₁ Δ₂ h₁ h₂ hne =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm h₁ h₂
          obtain ⟨S₁, rfl, hS₁⟩ := SVal.instantiate_eq_directory hi₁
          obtain ⟨S₂, rfl, hS₂⟩ := SVal.instantiate_eq_directory hi₂
          exact ⟨Φ₁ ⋏ Φ₂, _, m', SEval.dirstreamEq hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            simp [SVal.instantiate, TWE.Model.satAtom, hS₁, hS₂, hne]⟩
  | not e ih =>
      cases heval with
      | not hb =>
          obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := ih U hu hm hb
          obtain ⟨Φ', rfl, hΦ'⟩ := SVal.instantiate_eq_bool hi
          exact ⟨Φ, .prop (∼Φ'), m₁, SEval.not hs, hm₁, heq, hsat, by
            simp [SVal.instantiate, ← hΦ']
            exact decide_not⟩
  | and e₁ e₂ ih₁ ih₂ =>
      cases heval with
      | and hb₁ hb₂ =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm hb₁ hb₂
          obtain ⟨Φ₁', rfl, hΦ₁⟩ := SVal.instantiate_eq_bool hi₁
          obtain ⟨Φ₂', rfl, hΦ₂⟩ := SVal.instantiate_eq_bool hi₂
          exact ⟨Φ₁ ⋏ Φ₂, .prop (Φ₁' ⋏ Φ₂'), m', SEval.and hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            simp [SVal.instantiate, ← hΦ₁, ← hΦ₂]
            exact Bool.decide_and ..⟩
  | or e₁ e₂ ih₁ ih₂ =>
      cases heval with
      | or hb₁ hb₂ =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm hb₁ hb₂
          obtain ⟨Φ₁', rfl, hΦ₁⟩ := SVal.instantiate_eq_bool hi₁
          obtain ⟨Φ₂', rfl, hΦ₂⟩ := SVal.instantiate_eq_bool hi₂
          exact ⟨Φ₁ ⋏ Φ₂, .prop (Φ₁' ⋎ Φ₂'), m', SEval.or hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            simp [SVal.instantiate, ← hΦ₁, ← hΦ₂]
            exact Bool.decide_or ..⟩
  | join e₁ e₂ ih₁ ih₂ =>
      cases heval with
      | join hp₁ hp₂ =>
          obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m', hs₁, hs₂, hm', heq, hsat₁, hsat₂, hi₁, hi₂⟩ :=
            seval_complete_pair ih₁ ih₂ hu hm hp₁ hp₂
          obtain ⟨P₁, rfl, hP₁⟩ := SVal.instantiate_eq_path hi₁
          obtain ⟨P₂, rfl, hP₂⟩ := SVal.instantiate_eq_path hi₂
          exact ⟨Φ₁ ⋏ Φ₂, .path (.join P₁ P₂), m', SEval.join hs₁ hs₂, hm', heq, ⟨hsat₁, hsat₂⟩, by
            simp [SVal.instantiate, TWE.Model.evalPath, hP₁, hP₂]⟩
  | base e ih =>
      cases heval with
      | @base _ p hp =>
          obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := ih U hu hm hp
          obtain ⟨P, rfl, hP⟩ := SVal.instantiate_eq_path hi
          cases p with
          | nil =>
              exact ⟨Φ ⋏ (P ≐ .nil), .path .nil, m₁, SEval.baseEps hs, hm₁, heq,
                ⟨hsat, by simpa [TWE.Model.satAtom, TWE.Model.evalPath] using hP⟩, by
                  simp [SVal.instantiate, TWE.Model.evalPath, Accordion.Path.base]⟩
          | app q c =>
              obtain ⟨Z, hZ⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ P.free).path
              obtain ⟨YB, hYB⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ P.free).comp
              have ew := (TWE.Model.congr_setPath (m := m₁) (p := q) hZ).trans
                (TWE.Model.congr_setComp (b := c) hYB)
              have hPv := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP
              exact ⟨Φ ⋏ (P ≐ Z ++ YB), .path YB, (m₁[Z ↦ q])[YB ↦ c], SEval.baseCons Z YB hs, hm₁,
                heq.trans (ew.mono (by free_subset)),
                ⟨(TWE.Model.sat_congr ew (by free_subset)).mp hsat, by
                  simp [TWE.Model.satAtom, TWE.Model.evalPath, TWE.Model.evalComponent, hPv,
                    Accordion.Path.init, Accordion.Path.join]⟩, by
                  simp [SVal.instantiate, TWE.Model.evalPath, TWE.Model.evalComponent,
                    Accordion.Path.init, Accordion.Path.base]⟩
  | dir e ih =>
      cases heval with
      | @dir _ p hp =>
          obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := ih U hu hm hp
          obtain ⟨P, rfl, hP⟩ := SVal.instantiate_eq_path hi
          obtain ⟨Z, hZ⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ P.free).path
          obtain ⟨YB, hYB⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ P.free).comp
          cases p with
          | nil =>
              have ew := (TWE.Model.congr_setPath (m := m₁) (p := .nil) hZ).trans
                (TWE.Model.congr_setComp (b := .empty) hYB)
              have hPv := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP
              exact ⟨_, .path Z, (m₁[Z ↦ .nil])[YB ↦ .empty], SEval.dir Z YB hs, hm₁,
                heq.trans (ew.mono (by free_subset)),
                ⟨(TWE.Model.sat_congr ew (by free_subset)).mp hsat, Or.inr
                  ⟨by simp [TWE.Model.satAtom, TWE.Model.evalPath, hPv],
                    by simp [TWE.Model.satAtom, TWE.Model.evalPath]⟩⟩, by
                  simp [SVal.instantiate, TWE.Model.evalPath, Accordion.Path.dir]⟩
          | app q c =>
              have ew := (TWE.Model.congr_setPath (m := m₁) (p := q) hZ).trans
                (TWE.Model.congr_setComp (b := c) hYB)
              have hPv := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP
              exact ⟨_, .path Z, (m₁[Z ↦ q])[YB ↦ c], SEval.dir Z YB hs, hm₁,
                heq.trans (ew.mono (by free_subset)),
                ⟨(TWE.Model.sat_congr ew (by free_subset)).mp hsat, Or.inl (by
                  simp [TWE.Model.satAtom, TWE.Model.evalPath, TWE.Model.evalComponent, hPv,
                    Accordion.Path.init, Accordion.Path.join])⟩, by
                  simp [SVal.instantiate, TWE.Model.evalPath, Accordion.Path.dir]⟩
  | norm e ih =>
      cases heval with
      | norm hp =>
          obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := ih U hu hm hp
          obtain ⟨P, rfl, hP⟩ := SVal.instantiate_eq_path hi
          exact ⟨Φ, .path (.norm P), m₁, SEval.norm hs, hm₁, heq, hsat, by
            simp [SVal.instantiate, TWE.Model.evalPath, hP]⟩

section
variable [DecidableEq X]

theorem SStore.Valid.congr (h : m ≡[U] m') {ρ : SStore Γ X V} (hρ : ρ.free ⊆ U)
    (hv : ρ.Valid m) : ρ.Valid m' := by
  intro x w hx
  rw [← SVal.instantiate_congr h (TWE.Free.Subset.trans (SVal.free_subset_of_lookup hx) hρ)]
  exact hv x w hx

private theorem state_congr {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    {τ : FileTree Γ} (hu : (SState.mk ρ T π).free ⊆ U) (heq : m ≡[U] m')
    (hvalid : m ⊩ ρ) (hπ : m ⊨ π) (hT : m.evalTree T = some (.tree τ)) :
    (m' ⊩ ρ) ∧ (m' ⊨ π) ∧ m'.evalTree T = some (.tree τ) ∧ ⟦ρ⟧ m' = ⟦ρ⟧ m := by
  obtain ⟨hu₁, huπ⟩ := TWE.Free.union_subset hu
  obtain ⟨huρ, huT⟩ := TWE.Free.union_subset hu₁
  exact ⟨hvalid.congr heq huρ, (TWE.Model.sat_congr heq huπ).mp hπ,
    (TWE.Model.evalTree_congr heq huT).symm.trans hT, (SStore.instantiate_congr heq huρ).symm⟩

omit [TWE.Vars.Comparable V] in
theorem SState.instantiate_of_evalTree {ρ : SStore Γ X V} {T : TWE.Tree V}
    {π : TWE.Formula Γ V} {τ : FileTree Γ} (h : m.evalTree T = some (.tree τ)) :
    ⟦(⟨ρ, T, π⟩ : SState Γ X V)⟧ m = some ⟨⟦ρ⟧ m, τ⟩ := by
  simp [SState.instantiate, h]

omit [DecidableEq Γ] [DecidableEq X] in
theorem TWE.Model.WF.setLoc (hm : m.WF) (L : V.Loc) {p : Accordion.Path Γ} (hp : p.Linear) :
    (m[L ↦ p]).WF := by
  refine ⟨fun l => ?_, hm.2⟩
  by_cases hl : l = L
  · simpa [TWE.Model.setLoc, hl] using hp
  · simpa [TWE.Model.setLoc, hl] using hm.1 l

omit [TWE.Vars.Comparable V] [DecidableEq X] in
theorem walk_complete [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    {T : TWE.Tree V} {P : TWE.Path Γ V} {L : V.Loc}
    {τ : FileTree Γ} {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ}
    (hm : m.WF) (hT : m.evalTree T = some (.tree τ))
    (hres : FileTree.resolve (m.evalPath P) τ = some (C, f))
    (hL : m.σLoc L = C.path) :
    (m ⊨ (T ⊢ P ⇝ L)) ∧ FileTree.resolve (m.σLoc L) τ = some (C, f) ∧
      m.evalTree T[L] = some f := by
  have hresL : FileTree.resolve (m.σLoc L) τ = some (C, f) :=
    hL ▸ resolve_path (TWE.Model.evalTree_canonical hm hT) hres
  refine ⟨?_, hresL,
    by simp [TWE.Model.evalTree, FileTree.Focus.resolve, hT, hresL]⟩
  simp only [Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom, hT, hres]
  exact hL.symm

private theorem seval_complete_loc [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [TWE.Vars.Unbounded V]
    {ρ : SStore Γ X V} {T : TWE.Tree V} {e : Expr Γ X}
    {p : Accordion.Path Γ} {τ : FileTree Γ} {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ}
    (U : TWE.Free V) (huρ : ρ.free ⊆ U) (huT : T.free ⊆ U) (hm : m.WF)
    (hT : m.evalTree T = some (.tree τ))
    (hev : e ⇓[⟦ρ⟧ m] (.path p))
    (hres : FileTree.resolve p τ = some (C, f)) :
    ∃ Φ P L, ∃ m' : TWE.Model Γ V,
      (e ⇓[ρ] (.path P) ∣ Φ) ∧ m'.WF ∧ (m ≡[U] m') ∧ (m' ⊨ Φ) ∧ m'.σLoc L = C.path ∧
      (m' ⊨ T ⊢ P ⇝ L) ∧ FileTree.resolve (m'.σLoc L) τ = some (C, f) ∧
      m'.evalTree T[L] = some f := by
  obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
  obtain ⟨P, rfl, hP⟩ := SVal.instantiate_eq_path hi
  obtain ⟨L, hL⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ P.free).loc
  have ew := TWE.Model.congr_setLoc (m := m₁) (p := C.path) hL
  have heq' := heq.trans (ew.mono (by free_subset))
  have hm' := hm₁.setLoc L C.path_linear
  have hLv : (m₁[L ↦ C.path]).σLoc L = C.path := by simp
  have hPv := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP
  exact ⟨Φ, P, L, _, hs, hm', heq', (TWE.Model.sat_congr ew (by free_subset)).mp hsat, hLv,
    walk_complete hm' ((TWE.Model.evalTree_congr heq' huT).symm.trans hT) (hPv ▸ hres) hLv⟩

theorem sstep_complete [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [TWE.Vars.Unbounded V]
    {c c' : Command Γ X} {ς ς' : State Γ X}
    {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    {m : TWE.Model Γ V} (U : TWE.Free V)
    (hu : (SState.mk ρ T π).free ⊆ U)
    (hm : m.WF) (hvalid : m ⊩ ρ) (hπ : m ⊨ π)
    (hς : ⟦(⟨ρ, T, π⟩ : SState Γ X V)⟧ m = some ς)
    (hstep : (c, ς) ⟶ (c', ς')) :
    ∃ ρ' T' π' m',
      ((c, ⟨ρ, T, π⟩) ⇝ (c', ⟨ρ', T', π'⟩)) ∧
      m'.WF ∧ (m' ⊩ ρ') ∧ (m' ⊨ π') ∧ (m ≡[U] m') ∧
      ⟦(⟨ρ', T', π'⟩ : SState Γ X V)⟧ m' = some ς' := by
  obtain ⟨hu₁, -⟩ := TWE.Free.union_subset hu
  obtain ⟨huρ, huT⟩ := TWE.Free.union_subset hu₁
  induction hstep with
  | context _ ih =>
      obtain ⟨ρ', T', π', m', hs, rest⟩ := ih hς
      exact ⟨ρ', T', π', m', SStep.context hs, rest⟩
  | @assign x e v ρc τ hev =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
      obtain ⟨hv₁, hπ₁, hT₁, hρ₁⟩ := state_congr hu heq hvalid hπ hT
      exact ⟨ρ.set x Ŝ, T, π ⋏ Φ, m₁, SStep.assign hs rfl ⟨m₁, hm₁, hπ₁, hsat⟩, hm₁,
        SStore.valid_set hv₁ hi, ⟨hπ₁, hsat⟩, heq, by
        rw [SState.instantiate_of_evalTree hT₁, TWE.Model.instantiateStore_set hi, hρ₁]⟩
  | seq => exact ⟨ρ, T, π, m, SStep.seq, hm, hvalid, hπ, TWE.Model.EqOn.refl m U, hς⟩
  | @ifTrue e c₁ c₂ ρc τ hev =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
      obtain ⟨Φ', rfl, hΦ'⟩ := SVal.instantiate_eq_bool hi
      obtain ⟨hv₁, hπ₁, hT₁, hρ₁⟩ := state_congr hu heq hvalid hπ hT
      have hπ' : m₁ ⊨ π ⋏ Φ ⋏ Φ' := ⟨⟨hπ₁, hsat⟩, of_decide_eq_true hΦ'⟩
      exact ⟨ρ, T, _, m₁, SStep.ifTrue hs rfl ⟨m₁, hm₁, hπ'⟩, hm₁, hv₁, hπ', heq, by
        rw [SState.instantiate_of_evalTree hT₁, hρ₁]⟩
  | @ifFalse e c₁ c₂ ρc τ hev =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
      obtain ⟨Φ', rfl, hΦ'⟩ := SVal.instantiate_eq_bool hi
      obtain ⟨hv₁, hπ₁, hT₁, hρ₁⟩ := state_congr hu heq hvalid hπ hT
      have hπ' : m₁ ⊨ π ⋏ Φ ⋏ ∼Φ' := ⟨⟨hπ₁, hsat⟩, of_decide_eq_false hΦ'⟩
      exact ⟨ρ, T, _, m₁, SStep.ifFalse hs rfl ⟨m₁, hm₁, hπ'⟩, hm₁, hv₁, hπ', heq, by
        rw [SState.instantiate_of_evalTree hT₁, hρ₁]⟩
  | «while» => exact ⟨ρ, T, π, m, SStep.while, hm, hvalid, hπ, TWE.Model.EqOn.refl m U, hς⟩
  | @create e p ρc τ C τ' hev hres hfill | @mkdir e p ρc τ C τ' hev hres hfill
  | @unlink e p ρc τ C τ' hev hres hfill | @rmdir e p ρc τ C τ' hev hres hfill =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, P, L, m', hs, hm', heq, hΦ, -, hwalk, hresL, hsel⟩ :=
        seval_complete_loc U huρ huT hm hT hev hres
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq hvalid hπ hT
      have hπ' : m' ⊨ π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶ _ :=
        ⟨⟨hπ₁, hΦ⟩, hwalk, (TWE.Model.sat_treeShape hsel).mpr rfl⟩
      have hς' {T' g} π' (hg : m'.evalTree T' = some g) (hfill : C.fill g = some τ') :
          ⟦(⟨ρ, T[L ↦ T'], π'⟩ : SState Γ X V)⟧ m' = some ⟨⟦ρ⟧ m, τ'⟩ := by
        rw [SState.instantiate_of_evalTree
          ((TWE.Model.evalTree_update_iff hTv hresL).mpr ⟨g, hg, hfill⟩), hρ']
      first
      | exact ⟨ρ, _, _, m', SStep.create L hs rfl ⟨m', hm', hπ'⟩, hm', hv', hπ', heq,
          hς' _ rfl hfill⟩
      | exact ⟨ρ, _, _, m', SStep.mkdir L hs rfl ⟨m', hm', hπ'⟩, hm', hv', hπ', heq,
          hς' _ rfl hfill⟩
      | exact ⟨ρ, _, _, m', SStep.unlink L hs rfl ⟨m', hm', hπ'⟩, hm', hv', hπ', heq,
          hς' _ rfl hfill⟩
      | have hπ'' : m' ⊨ π ⋏ Φ ⋏ (T ⊢ P ⇝ L ∶ .dirc ⋏ TWE.Set.entries T[L] ≐ ∅) :=
          ⟨hπ'.1, hπ'.2, by
            simp [TWE.Model.satAtom, TWE.Model.evalNameSet, hsel, FileTree.Entries.dom]⟩
        exact ⟨ρ, _, _, m', SStep.rmdir L hs rfl ⟨m', hm', hπ''⟩, hm', hv', hπ'', heq,
          hς' _ rfl hfill⟩
  | @rename e₁ e₂ p₁ p₂ ρc τ C₁ τ₁ τmid C₂ τ' hev₁ hres₁ hfill₁ hev₂ hres₂ hfill₂ =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ₁, Ŝ₁, Φ₂, Ŝ₂, m₀, hs₁, hs₂, hm₀, heq₀, hsat₁, hsat₂, hi₁, hi₂⟩ :=
        seval_complete_pair seval_complete seval_complete huρ hm hev₁ hev₂
      obtain ⟨P₁, rfl, hP₁⟩ := SVal.instantiate_eq_path hi₁
      obtain ⟨P₂, rfl, hP₂⟩ := SVal.instantiate_eq_path hi₂
      obtain ⟨L₁, hL₁⟩ := Infinite.exists_notMem_finset
        (U ∪ Φ₁.free ∪ Φ₂.free ∪ P₁.free ∪ P₂.free).loc
      obtain ⟨L₂, hL₂⟩ := Infinite.exists_notMem_finset
        (insert L₁ (U ∪ Φ₁.free ∪ Φ₂.free ∪ P₁.free ∪ P₂.free).loc)
      rw [Finset.mem_insert, not_or] at hL₂
      have ew := (TWE.Model.congr_setLoc (m := m₀) (p := C₁.path) hL₁).trans
        (TWE.Model.congr_setLoc (p := C₂.path) hL₂.2)
      have heq := heq₀.trans (ew.mono (by free_subset))
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq hvalid hπ hT
      have hm' := (hm₀.setLoc L₁ C₁.path_linear).setLoc L₂ C₂.path_linear
      have hP₁v := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP₁
      have hP₂v := (TWE.Model.evalPath_congr ew (by free_subset)).symm.trans hP₂
      obtain ⟨hwalk₁, hresL₁, hsel₁⟩ := walk_complete (L := L₁) hm' hTv (hP₁v ▸ hres₁)
        (by simp [Ne.symm hL₂.1])
      have hmid := (TWE.Model.evalTree_update_iff (T' := .abst) hTv hresL₁).mpr ⟨_, rfl, hfill₁⟩
      obtain ⟨hwalk₂, hresL₂, hsel₂⟩ := walk_complete (L := L₂) hm' hmid (hP₂v ▸ hres₂)
        (by simp)
      have hπ' : (m₀[L₁ ↦ C₁.path])[L₂ ↦ C₂.path] ⊨ π ⋏ Φ₁ ⋏ Φ₂ ⋏
          (T ⊢ P₁ ⇝ L₁ ∶∼ .absent ⋏ T[L₁ ↦ .abst] ⊢ P₂ ⇝ L₂ ∶ .absent) :=
        ⟨⟨⟨hπ₁, (TWE.Model.sat_congr ew (by free_subset)).mp hsat₁⟩,
            (TWE.Model.sat_congr ew (by free_subset)).mp hsat₂⟩,
          ⟨hwalk₁, TWE.Model.not_sat_absent hsel₁⟩, hwalk₂,
          (TWE.Model.sat_treeShape hsel₂).mpr rfl⟩
      exact ⟨ρ, T[L₁ ↦ .abst][L₂ ↦ T[L₁]], _, _, SStep.rename L₁ L₂ hs₁ hs₂ rfl ⟨_, hm', hπ'⟩,
        hm', hv', hπ', heq, by
        rw [SState.instantiate_of_evalTree
          ((TWE.Model.evalTree_update_iff hmid hresL₂).mpr ⟨_, hsel₁, hfill₂⟩), hρ']⟩
  | @stat x e p ρc τ C τ' hev hres =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, P, L, m', hs, hm', heq, hΦ, -, hwalk, -, hsel⟩ :=
        seval_complete_loc U huρ huT hm hT hev hres
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq hvalid hπ hT
      have hInst := TWE.Model.instantiate_tree_iff.mpr ⟨τ', hsel, rfl⟩
      have hπ' : m' ⊨ π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶∼ .absent :=
        ⟨⟨hπ₁, hΦ⟩, hwalk, TWE.Model.not_sat_absent hsel⟩
      exact ⟨ρ.set x T[L], T, _, m', SStep.stat L hs rfl ⟨m', hm', hπ'⟩, hm',
        SStore.valid_set hv' hInst, hπ', heq, by
        rw [SState.instantiate_of_evalTree hTv, TWE.Model.instantiateStore_set hInst, hρ']⟩
  | @realpath x e p ρc τ C τ' hev hres =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, P, L, m₁, hs, hm₁, heq, hΦ, hLv, hwalk, -, hsel⟩ :=
        seval_complete_loc U huρ huT hm hT hev hres
      have hA : m₁ ⊨ T ⊢ P ⇝ L ∶∼ .absent := ⟨hwalk, TWE.Model.not_sat_absent hsel⟩
      obtain ⟨Q, hQ⟩ := Infinite.exists_notMem_finset
        (U ∪ Φ.free ∪ (T ⊢ P ⇝ L ∶∼ TWE.Shape.absent).free).path
      have ew := TWE.Model.congr_setPath (m := m₁) (p := C.path) hQ
      have heq' := heq.trans (ew.mono (by free_subset))
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq' hvalid hπ hT
      have hm' : (m₁[Q ↦ C.path]).WF := hm₁
      have hInst : ⟦(Q : TWE.Path Γ V)⟧ (m₁[Q ↦ C.path]) = some (.path C.path) := by
        simp [SVal.instantiate, TWE.Model.evalPath]
      have hπ' : m₁[Q ↦ C.path] ⊨ π ⋏ Φ ⋏
          (T ⊢ P ⇝ L ∶∼ .absent ⋏ (Q : TWE.Path Γ V) ≐ L ⋏ Lin (Q : TWE.Path Γ V)) :=
        ⟨⟨hπ₁, (TWE.Model.sat_congr ew (by free_subset)).mp hΦ⟩,
          ⟨(TWE.Model.sat_congr ew (by free_subset)).mp hA, by
            simp [TWE.Model.satAtom, TWE.Model.evalPath, hLv]⟩, by
            simpa [TWE.Model.satAtom, TWE.Model.evalPath] using C.path_linear⟩
      exact ⟨ρ.set x Q, T, _, m₁[Q ↦ C.path], SStep.realpath L Q hs rfl ⟨_, hm', hπ'⟩, hm',
        SStore.valid_set hv' hInst, hπ', heq', by
        rw [SState.instantiate_of_evalTree hTv, TWE.Model.instantiateStore_set hInst, hρ']⟩
  | @opendir x e p ρc τ C δ hev hres =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, P, L, m₁, hs, hm₁, heq, hΦ, -, hwalk, -, hsel⟩ :=
        seval_complete_loc U huρ huT hm hT hev hres
      have hA : m₁ ⊨ T ⊢ P ⇝ L ∶ .dirc := ⟨hwalk, (TWE.Model.sat_treeShape hsel).mpr rfl⟩
      obtain ⟨S, hS⟩ := Infinite.exists_notMem_finset
        (U ∪ Φ.free ∪ (T ⊢ P ⇝ L ∶ TWE.Shape.dirc).free ∪ T[L].free).set
      have ew := TWE.Model.congr_setSet (m := m₁) (s := FileTree.Entries.dom δ) hS
      have heq' := heq.trans (ew.mono (by free_subset))
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq' hvalid hπ hT
      have hm' : (m₁[S ↦ FileTree.Entries.dom δ]).WF := hm₁
      have hSv : (m₁[S ↦ FileTree.Entries.dom δ]).evalNameSet S =
          some (FileTree.Entries.dom δ) := by simp [TWE.Model.evalNameSet]
      have hEv : (m₁[S ↦ FileTree.Entries.dom δ]).evalNameSet (.entries T[L]) =
          some (FileTree.Entries.dom δ) :=
        (TWE.Model.evalNameSet_congr ew (by free_subset)).symm.trans (by
          simp [TWE.Model.evalNameSet, hsel])
      have hInst : ⟦(S : TWE.Set Γ V)⟧ (m₁[S ↦ FileTree.Entries.dom δ]) =
          some (.directory (FileTree.Entries.dom δ)) := by simp [SVal.instantiate, hSv]
      have hπ' : m₁[S ↦ FileTree.Entries.dom δ] ⊨ π ⋏ Φ ⋏
          (T ⊢ P ⇝ L ∶ .dirc ⋏ S ≐ .entries T[L]) :=
        ⟨⟨hπ₁, (TWE.Model.sat_congr ew (by free_subset)).mp hΦ⟩,
          (TWE.Model.sat_congr ew (by free_subset)).mp hA, by
            simp [TWE.Model.satAtom, hSv, hEv]⟩
      exact ⟨ρ.set x S, T, _, m₁[S ↦ FileTree.Entries.dom δ],
        SStep.opendir L S hs rfl ⟨_, hm', hπ'⟩, hm', SStore.valid_set hv' hInst, hπ', heq', by
        rw [SState.instantiate_of_evalTree hTv, TWE.Model.instantiateStore_set hInst, hρ']⟩
  | @readdirNil r x y e ρc τ hev =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
      obtain ⟨S, rfl, hS⟩ := SVal.instantiate_eq_directory hi
      obtain ⟨hv₁, hπ₁, hT₁, hρ₁⟩ := state_congr hu heq hvalid hπ hT
      have hInstR : ⟦(⊥ : TWE.Formula Γ V)⟧ m₁ = some (.bool false) := rfl
      have hπ' : m₁ ⊨ π ⋏ Φ ⋏ S ≐ ∅ :=
        ⟨⟨hπ₁, hsat⟩, by simp [TWE.Model.satAtom, TWE.Model.evalNameSet, hS]⟩
      exact ⟨(ρ.set r (⊥ : TWE.Formula Γ V)).set x S, T, _, m₁,
        SStep.readdirNil hs rfl ⟨m₁, hm₁, hπ'⟩, hm₁,
        SStore.valid_set (SStore.valid_set hv₁ hInstR) hi, hπ', heq, by
        rw [SState.instantiate_of_evalTree hT₁, TWE.Model.instantiateStore_set hi,
          TWE.Model.instantiateStore_set hInstR, hρ₁]⟩
  | @readdirCons r x y e ρc τ a Δ hev hmem =>
      obtain ⟨_, hT, ⟨⟩⟩ := TWE.Model.instantiateState_some hς
      obtain ⟨Φ, Ŝ, m₁, hs, hm₁, heq, hsat, hi⟩ := seval_complete U huρ hm hev
      obtain ⟨S, rfl, hS⟩ := SVal.instantiate_eq_directory hi
      obtain ⟨R, hR⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ S.free).set
      obtain ⟨XA, hXA⟩ := Infinite.exists_notMem_finset (U ∪ Φ.free ∪ S.free).name
      have ew := (TWE.Model.congr_setSet (m := m₁) (s := Δ.erase a) hR).trans
        (TWE.Model.congr_setName (a := a) hXA)
      have heq' := heq.trans (ew.mono (by free_subset))
      obtain ⟨hv', hπ₁, hTv, hρ'⟩ := state_congr hu heq' hvalid hπ hT
      have hm' : ((m₁[R ↦ Δ.erase a])[XA ↦ a]).WF := hm₁
      have hSv := (TWE.Model.evalNameSet_congr ew (by free_subset)).symm.trans hS
      have hInstR : ⟦(⊤ : TWE.Formula Γ V)⟧ ((m₁[R ↦ Δ.erase a])[XA ↦ a]) =
          some (.bool true) := rfl
      have hInstX : ⟦(R : TWE.Set Γ V)⟧ ((m₁[R ↦ Δ.erase a])[XA ↦ a]) =
          some (.directory (Δ.erase a)) := by simp [SVal.instantiate, TWE.Model.evalNameSet]
      have hInstY : ⟦(XA : TWE.Path Γ V)⟧ ((m₁[R ↦ Δ.erase a])[XA ↦ a]) =
          some (.path (Accordion.Path.init (.name a))) := by
        simp [SVal.instantiate, TWE.Model.evalPath, TWE.Model.evalComponent, TWE.Model.evalName]
      have hπ' : (m₁[R ↦ Δ.erase a])[XA ↦ a] ⊨ π ⋏ Φ ⋏ (S ≐ .insert XA R ⋏ ∼XA ∈̇ R) :=
        ⟨⟨hπ₁, (TWE.Model.sat_congr ew (by free_subset)).mp hsat⟩,
          by simp [TWE.Model.satAtom, TWE.Model.evalNameSet, TWE.Model.evalName, hSv,
            Finset.insert_erase hmem],
          by simp [TWE.Model.satAtom, TWE.Model.evalNameSet, TWE.Model.evalName]⟩
      exact ⟨((ρ.set r (⊤ : TWE.Formula Γ V)).set x R).set y (XA : TWE.Path Γ V), T, _,
        (m₁[R ↦ Δ.erase a])[XA ↦ a],
        SStep.readdirCons R XA hs rfl ⟨_, hm', hπ'⟩, hm',
        SStore.valid_set (SStore.valid_set (SStore.valid_set hv' hInstR) hInstX) hInstY,
        hπ', heq', by
        rw [SState.instantiate_of_evalTree hTv, TWE.Model.instantiateStore_set hInstY,
          TWE.Model.instantiateStore_set hInstX, TWE.Model.instantiateStore_set hInstR, hρ']⟩

theorem smultistep_complete_aux [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [TWE.Vars.Unbounded V]
    {c c' : Command Γ X} {ς ς' : State Γ X}
    {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    {m : TWE.Model Γ V} (U : TWE.Free V)
    (hu : (SState.mk ρ T π).free ⊆ U)
    (hm : m.WF) (hvalid : m ⊩ ρ) (hπ : m ⊨ π)
    (hς : ⟦(⟨ρ, T, π⟩ : SState Γ X V)⟧ m = some ς)
    (hstep : (c, ς) ⟶* (c', ς')) :
    ∃ ρ' T' π' m',
      ((c, ⟨ρ, T, π⟩) ⇝* (c', ⟨ρ', T', π'⟩)) ∧
      m'.WF ∧ (m' ⊩ ρ') ∧ (m' ⊨ π') ∧ (m ≡[U] m') ∧
      ⟦(⟨ρ', T', π'⟩ : SState Γ X V)⟧ m' = some ς' := by
  induction hstep with
  | refl => exact ⟨ρ, T, π, m, SMultistep.refl, hm, hvalid, hπ, TWE.Model.EqOn.refl m U, hς⟩
  | single hs =>
      obtain ⟨ρ', T', π', m', hs', rest⟩ := sstep_complete U hu hm hvalid hπ hς hs
      exact ⟨ρ', T', π', m', SMultistep.single hs', rest⟩
  | trans _ hs ih =>
      obtain ⟨ρ₁, T₁, π₁, m₁, hms, hm₁, hv₁, hπ₁, heq₁, hi₁⟩ := ih
      obtain ⟨ρ₂, T₂, π₂, m₂, hs', hm₂, hv₂, hπ₂, heq₂, hi₂⟩ :=
        sstep_complete (U ∪ (SState.mk ρ₁ T₁ π₁).free) TWE.Free.subset_union_right
          hm₁ hv₁ hπ₁ hi₁ hs
      exact ⟨ρ₂, T₂, π₂, m₂, SMultistep.trans hms hs', hm₂, hv₂, hπ₂,
        heq₁.trans (heq₂.mono TWE.Free.subset_union_left), hi₂⟩

theorem smultistep_complete [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [TWE.Vars.Unbounded V]
    {c c' : Command Γ X} {ς ς' : State Γ X} {sς : SState Γ X V} :
    m.WF → (m ⊫ sς) → ⟦sς⟧ m = some ς → ((c, ς) ⟶* (c', ς')) →
      ∃ sς', ((c, sς) ⇝* (c', sς')) ∧
        ∃ m' : TWE.Model Γ V, m'.WF ∧ (m' ⊫ sς') ∧
          ⟦sς⟧  m' = some ς  ∧
          ⟦sς'⟧ m' = some ς' := by
  obtain ⟨ρ, T, π⟩ := sς
  intro hm ⟨hπ, hvalid⟩ hς hstep
  obtain ⟨ρ', T', π', m', hms, hm', hv', hπ', heq, hi'⟩ :=
    smultistep_complete_aux (SState.mk ρ T π).free (TWE.Free.Subset.refl _) hm hvalid hπ hς hstep
  exact ⟨⟨ρ', T', π'⟩, hms, m', hm', ⟨hπ', hv'⟩,
    (SState.instantiate_congr heq (TWE.Free.Subset.refl _)).symm.trans hς, hi'⟩

end

end Accordion

end
