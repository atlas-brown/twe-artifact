module

public import Accordion.WhileFS.Symbolic
public import Accordion.FileTree.Properties
public import Accordion.FileTree.Zipper.Properties

@[expose] public section

namespace Accordion

open scoped TWE Accordion.Formula

variable {Γ X : Type} {V : TWE.Vars} [Ord Γ]

namespace TWE.Model

omit [Ord Γ] in
theorem evalComponent_embedComponent (m : TWE.Model Γ V) (q : Accordion.Component Γ) :
    m.evalComponent (⌜q⌝) = q := by
  cases q <;> rfl

omit [Ord Γ] in
theorem evalPath_embedPath (m : TWE.Model Γ V) (p : Accordion.Path Γ) : m.evalPath (⌜p⌝) = p := by
  induction p with
  | nil => rfl
  | app p q ih =>
      simp [embedPath, TWE.Model.evalPath, TWE.Model.evalComponent_embedComponent,
        Accordion.Path.init, Accordion.Path.join, ih]

private theorem evalNameSet_foldr_insert [DecidableEq Γ] (m : TWE.Model Γ V) (l : List Γ) :
    m.evalNameSet (l.foldr (fun a acc => TWE.Set.insert (.name a) acc) ∅)
      = some l.toFinset := by
  induction l with
  | nil => simp [TWE.Model.evalNameSet]
  | cons a tl ih =>
      simp only [TWE.Set.empty_eq] at ih
      simp [TWE.Model.evalNameSet, TWE.Model.evalName, ih]

theorem evalNameSet_embedNameSet [DecidableEq Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (m : TWE.Model Γ V) (Δ : Finset Γ) : m.evalNameSet (⌜Δ⌝) = some Δ := by
  rw [embedNameSet, evalNameSet_foldr_insert, Finset.sort_toFinset]

theorem embed_instantiate [DecidableEq Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (m : TWE.Model Γ V) (v : Val Γ) : ⟦(⌜v⌝)⟧ m = some v := by
  cases v with
  | bool b => cases b <;> rfl
  | path p => simp [embed, SVal.instantiate, TWE.Model.evalPath_embedPath]
  | filetype y =>
      cases y <;> simp [embed, SVal.instantiate, TWE.Model.evalTree, FileTree.Focus.shape]
  | directory Δ => simp [embed, SVal.instantiate, TWE.Model.evalNameSet_embedNameSet]

end TWE.Model

theorem resolve_path [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] {p : Path Γ} {τ : FileTree Γ}
    {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ} (hτ : τ.Canonical)
    (h : FileTree.resolve p τ = some (C, f)) : FileTree.resolve C.path τ = some (C, f) := by
  unfold FileTree.resolve at h ⊢
  obtain ⟨z, hz, ⟨⟩⟩ := Option.map_eq_some_iff.mp h
  simp [FileTree.Zipper.traverse_idem hτ p z hz]

omit [Ord Γ] in
theorem FileTree.Focus.eq_of_shape_absent {f : FileTree.Focus Γ} (h : f.shape = .absent) :
    f = .abst := by
  rcases f with (_ | _) | _ <;> simp_all [FileTree.Focus.shape]

omit [Ord Γ] in
theorem FileTree.Focus.eq_of_shape_file {f : FileTree.Focus Γ} (h : f.shape = .file) :
    f = .tree .file := by
  rcases f with (_ | _) | _ <;> simp_all [FileTree.Focus.shape]

omit [Ord Γ] in
theorem FileTree.Focus.eq_of_shape_dirc {f : FileTree.Focus Γ} (h : f.shape = .dirc) :
    ∃ δ, f = .tree (.dirc δ) := by
  rcases f with (_ | _) | _ <;> simp_all [FileTree.Focus.shape]

variable {m : TWE.Model Γ V}


theorem TWE.Model.evalTree_upd_pred {T : TWE.Tree V} {L : V.Loc}
    {T' : TWE.Tree V} {τ' : FileTree Γ} (h : m.evalTree T[L ↦ T'] = some (.tree τ')) :
    ∃ τ, m.evalTree T = some (.tree τ) := by
  rcases hT : m.evalTree T with _ | τ | _
  on_goal 2 => exact ⟨τ, rfl⟩
  all_goals simp [TWE.Model.evalTree, hT] at h

theorem TWE.Model.evalTree_update_iff {T T' : TWE.Tree V} {L : V.Loc}
    {τ τ' : FileTree Γ} {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ}
    (hT : m.evalTree T = some (.tree τ))
    (hres : FileTree.resolve (m.σLoc L) τ = some (C, f)) :
    m.evalTree T[L ↦ T'] = some (.tree τ') ↔
      ∃ g, m.evalTree T' = some g ∧ C.fill g = some τ' := by
  simp [TWE.Model.evalTree, hT, hres, Option.bind_eq_some_iff]

theorem TWE.Model.evalTree_canonical [Std.TransOrd Γ] (hm : m.WF) {T : TWE.Tree V}
    {f : FileTree.Focus Γ} (h : m.evalTree T = some f) : f.Canonical := by
  induction T generalizing f with
  | var V => cases h; exact hm.2 V
  | file => cases h; exact FileTree.Canonical.file
  | emptyDirc =>
      cases h
      exact FileTree.Canonical.dirc FileTree.Entries.canonical_empty
        (by simp [FileTree.Entries.empty, EmptyCollection.emptyCollection])
  | abst => cases h; trivial
  | select T L ihT =>
      simp only [TWE.Model.evalTree, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨τ | _, hT, ⟨C, f'⟩, hr, ⟨⟩⟩ := h
      · exact FileTree.resolve_canonical (ihT hT) hr
      · cases hL : m.σLoc L <;> simp [FileTree.Focus.resolve, hL] at hr
        obtain ⟨-, rfl⟩ := hr
        trivial
  | update T L T' ihT ihT' =>
      rcases f with τ' | _
      on_goal 2 => trivial
      obtain ⟨τ, hT⟩ := TWE.Model.evalTree_upd_pred h
      rcases hr : FileTree.resolve (m.σLoc L) τ with _ | ⟨C, f₀⟩
      · simp [TWE.Model.evalTree, hT, hr] at h
      · obtain ⟨g, hg, hfill⟩ := (TWE.Model.evalTree_update_iff hT hr).mp h
        exact FileTree.Ctx.fill_canonical (FileTree.resolve_ctx_canonical (ihT hT) hr) (ihT' hg)
          hfill

variable [DecidableEq Γ] [DecidableEq X]

theorem SStore.valid_set {ρ : SStore Γ X V} {x : X} {v : SVal Γ V}
    {v' : Val Γ} (hρ : ρ.Valid m) (hv : ⟦v⟧ m = some v') :
    (ρ[x ↦ v]).Valid m := by
  unfold SStore.Valid SStore.set
  intro y w h
  by_cases hxy : y = x
  · subst hxy
    rw [Finmap.lookup_insert] at h
    cases h
    simp [hv]
  · rw [Finmap.lookup_insert_of_ne _ hxy] at h
    exact hρ y w h

theorem TWE.Model.instantiateStore_set {ρ : SStore Γ X V} {x : X}
    {v : SVal Γ V} {v' : Val Γ} (hv : ⟦v⟧ m = some v') :
    ⟦ρ[x ↦ v]⟧ m = (⟦ρ⟧ m)[x ↦ v'] := by
  funext y
  by_cases hxy : y = x
  · subst hxy
    simp [SStore.instantiate, SStore.set, Store.set, hv]
  · simp [SStore.instantiate, SStore.set, Store.set, hxy, Finmap.lookup_insert_of_ne _ hxy]

theorem TWE.Model.sat_treeShape {T : TWE.Tree V}
    {H : TWE.Shape} {f : FileTree.Focus Γ} (hf : m.evalTree T = some f) :
    (m ⊨ T ∶ H) ↔ f.shape = H := by
  simp [TWE.Model.satAtom, hf]

theorem TWE.Model.not_sat_absent {T : TWE.Tree V}
    {τ : FileTree Γ} (h : m.evalTree T = some (.tree τ)) : ¬ (m ⊨ T ∶ .absent) := by
  cases τ <;> simp [TWE.Model.satAtom, h, FileTree.Focus.shape]

theorem TWE.Model.instantiate_tree_iff {T : TWE.Tree V} {v : Val Γ} :
    ⟦SVal.tree T⟧ m = some v ↔
      ∃ τ, m.evalTree T = some (.tree τ) ∧ .filetype τ.fileType = v := by
  rcases hf : m.evalTree T with _ | (_ | δ) | _ <;>
    simp [SVal.instantiate, hf, FileTree.Focus.shape, FileTree.fileType]

theorem TWE.Model.instantiate_set_eq {S : TWE.Set Γ V}
    {v : Val Γ} (h : ⟦SVal.set S⟧ m = some v) :
    ∃ Δ, m.evalNameSet S = some Δ ∧ .directory Δ = v :=
  Option.map_eq_some_iff.mp h

theorem TWE.Model.instantiateState_some {ς : SState Γ X V} {st : State Γ X}
    (h : ⟦ς⟧ m = some st) :
    ∃ τ, m.evalTree ς.tree = some (.tree τ) ∧ st = ⟨⟦ς.store⟧ m, τ⟩ := by
  unfold SState.instantiate at h
  split at h <;> cases h
  exact ⟨_, ‹_›, rfl⟩

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem SStep.pc_mono {c c' : Command Γ X} {s s' : SState Γ X V}
    (h : (c, s) ⇝ (c', s')) (hπ : m ⊨ s'.π) : m ⊨ s.π := by
  induction h with
  | context _ ih => exact ih hπ
  | seq | «while» => exact hπ
  | assign _ heq _ => subst heq; exact hπ.1
  | rename _ _ _ _ heq _ => subst heq; exact hπ.1.1.1
  | _ => subst_vars; exact hπ.1.1

theorem SMultistep.pc_mono {c c' : Command Γ X} {s s' : SState Γ X V}
    (h : (c, s) ⇝* (c', s')) (hπ : m ⊨ s'.π) : m ⊨ s.π := by
  induction h with
  | refl => exact hπ
  | single hs => exact SStep.pc_mono hs hπ
  | trans _ hs ih => exact ih (SStep.pc_mono hs hπ)

theorem SStep.evalTree_pred {c c' : Command Γ X} {s s' : SState Γ X V}
    (h : (c, s) ⇝ (c', s')) {τ' : FileTree Γ} (hτ' : m.evalTree s'.tree = some (.tree τ')) :
    ∃ τ, m.evalTree s.tree = some (.tree τ) := by
  induction h with
  | context _ ih => exact ih hτ'
  | create | mkdir | unlink | rmdir => exact TWE.Model.evalTree_upd_pred hτ'
  | rename => exact (TWE.Model.evalTree_upd_pred hτ').elim fun _ h => TWE.Model.evalTree_upd_pred h
  | _ => exact ⟨τ', hτ'⟩

theorem seval_sound {ρ : SStore Γ X V} {e : Expr Γ X} {Φ : TWE.Formula Γ V}
    {v : SVal Γ V} (h : (e ⇓[ρ] v ∣ Φ)) (hΦ : m ⊨ Φ)
    (hρ : ρ.Valid m) :
    ∃ v', ⟦v⟧ m = some v' ∧ (e ⇓[⟦ρ⟧ m] v') := by
  induction h with
  | var hx =>
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp (hρ _ _ hx)
      exact ⟨v', hv', Eval.var (by simp [SStore.instantiate, hx, hv'])⟩
  | val => exact ⟨_, TWE.Model.embed_instantiate m _, Eval.val⟩
  | @pathEq _ _ _ _ P₁ P₂ _ _ ih₁ ih₂ =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, ⟨⟩, h₂⟩ := ih₂ hΦ.2
      refine ⟨_, rfl, ?_⟩
      by_cases h : m.evalPath P₁ = m.evalPath P₂
      · simpa [TWE.Model.satAtom, h] using Eval.eqTrue h₁ h₂ (by rw [h])
      · simpa [TWE.Model.satAtom, h] using Eval.eqFalsePath h₁ h₂ h
  | @boolEq _ _ _ _ Φ₁' Φ₂' _ _ ih₁ ih₂ =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, ⟨⟩, h₂⟩ := ih₂ hΦ.2
      refine ⟨_, rfl, ?_⟩
      by_cases a : m ⊨ Φ₁' <;> by_cases b : m ⊨ Φ₂' <;>
        first
        | simpa [TWE.Formula.iff, a, b] using Eval.eqTrue h₁ h₂ (by simp [a, b])
        | simpa [TWE.Formula.iff, a, b] using Eval.eqFalseBool h₁ h₂ (by simp [a, b])
  | fileTypeEq _ _ ih₁ ih₂ =>
      obtain ⟨_, hv₁, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, hv₂, h₂⟩ := ih₂ hΦ.2
      obtain ⟨τ₁, hT₁, rfl⟩ := TWE.Model.instantiate_tree_iff.mp hv₁
      obtain ⟨τ₂, hT₂, rfl⟩ := TWE.Model.instantiate_tree_iff.mp hv₂
      refine ⟨_, rfl, ?_⟩
      cases τ₁ <;> cases τ₂ <;>
        first
        | simpa [TWE.Model.satAtom, hT₁, hT₂, FileTree.Focus.shape] using Eval.eqTrue h₁ h₂ rfl
        | simpa [TWE.Model.satAtom, hT₁, hT₂, FileTree.Focus.shape] using
            Eval.eqFalseFileType h₁ h₂ (by simp [FileTree.fileType])
  | dirstreamEq _ _ ih₁ ih₂ =>
      obtain ⟨_, hv₁, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, hv₂, h₂⟩ := ih₂ hΦ.2
      obtain ⟨Δ₁, hS₁, rfl⟩ := TWE.Model.instantiate_set_eq hv₁
      obtain ⟨Δ₂, hS₂, rfl⟩ := TWE.Model.instantiate_set_eq hv₂
      refine ⟨_, rfl, ?_⟩
      by_cases h : Δ₁ = Δ₂
      · simpa [TWE.Model.satAtom, hS₁, hS₂, h] using Eval.eqTrue h₁ h₂ (by rw [h])
      · simpa [TWE.Model.satAtom, hS₁, hS₂, h] using Eval.eqFalseDirectory h₁ h₂ h
  | not _ ih =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih hΦ
      exact ⟨_, rfl, decide_not (p := m ⊨ _) ▸ Eval.not h₁⟩
  | and _ _ ih₁ ih₂ =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, ⟨⟩, h₂⟩ := ih₂ hΦ.2
      exact ⟨_, rfl, Bool.decide_and (m ⊨ _) (m ⊨ _) ▸ Eval.and h₁ h₂⟩
  | or _ _ ih₁ ih₂ =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, ⟨⟩, h₂⟩ := ih₂ hΦ.2
      exact ⟨_, rfl, Bool.decide_or (m ⊨ _) (m ⊨ _) ▸ Eval.or h₁ h₂⟩
  | join _ _ ih₁ ih₂ =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih₁ hΦ.1
      obtain ⟨_, ⟨⟩, h₂⟩ := ih₂ hΦ.2
      exact ⟨_, rfl, Eval.join h₁ h₂⟩
  | @baseCons _ _ P Z YB _ ih =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih hΦ.1
      have heq : m.evalPath P = Path.app (m.σPath Z) (m.σComp YB) := by
        simpa [TWE.Model.satAtom, TWE.Model.evalPath, TWE.Model.evalComponent, Path.init,
          Path.join] using hΦ.2
      rw [heq] at h₁
      exact ⟨_, rfl, by
        simpa [Path.base, TWE.Model.evalPath, TWE.Model.evalComponent, Path.init] using
          Eval.base h₁⟩
  | @baseEps _ _ P _ ih =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih hΦ.1
      have heq : m.evalPath P = Path.nil := by
        simpa [TWE.Model.satAtom, TWE.Model.evalPath] using hΦ.2
      rw [heq] at h₁
      exact ⟨_, rfl, by simpa [Path.base, TWE.Model.evalPath] using Eval.base h₁⟩
  | @dir _ _ P Z YB _ ih =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih hΦ.1
      refine ⟨_, rfl, ?_⟩
      rcases hΦ.2 with hbr | ⟨hbr₁, hbr₂⟩
      · have heq : m.evalPath P = Path.app (m.σPath Z) (m.σComp YB) := by
          simpa [TWE.Model.satAtom, TWE.Model.evalPath, TWE.Model.evalComponent, Path.init,
            Path.join] using hbr
        rw [heq] at h₁
        simpa [Path.dir, TWE.Model.evalPath] using Eval.dir h₁
      · have heq : m.evalPath P = Path.nil := by
          simpa [TWE.Model.satAtom, TWE.Model.evalPath] using hbr₁
        have heqZ : m.σPath Z = Path.nil := by
          simpa [TWE.Model.satAtom, TWE.Model.evalPath] using hbr₂
        rw [heq] at h₁
        simpa [Path.dir, TWE.Model.evalPath, heqZ] using Eval.dir h₁
  | norm _ ih =>
      obtain ⟨_, ⟨⟩, h₁⟩ := ih hΦ
      exact ⟨_, rfl, Eval.norm h₁⟩

theorem seval_sound_path {ρ : SStore Γ X V} {e : Expr Γ X} {Φ : TWE.Formula Γ V}
    {P : TWE.Path Γ V} (h : (e ⇓[ρ] (.path P) ∣ Φ)) (hΦ : m ⊨ Φ) (hρ : ρ.Valid m) :
    e ⇓[⟦ρ⟧ m] .path (m.evalPath P) := by
  obtain ⟨_, ⟨⟩, h⟩ := seval_sound h hΦ hρ
  exact h

theorem walk_sound {P : TWE.Path Γ V} {L : V.Loc} {T : TWE.Tree V}
    {τ : FileTree Γ} (hm : m.WF) (hτ : m.evalTree T = some (.tree τ)) (h : m ⊨ T ⊢ P ⇝ L) :
    ∃ C f, FileTree.resolve (m.evalPath P) τ = some (C, f) ∧
      FileTree.resolve (m.σLoc L) τ = some (C, f) ∧ C.path = m.σLoc L ∧
      m.evalTree T[L] = some f := by
  simp only [Formula.sat, TWE.Model.sat_iff_satAtom, TWE.Model.satAtom, hτ] at h
  rcases hP : FileTree.resolve (m.evalPath P) τ with _ | ⟨C, f⟩
  · simp [hP] at h
  · simp only [hP] at h
    have hL : FileTree.resolve (m.σLoc L) τ = some (C, f) :=
      h ▸ resolve_path (TWE.Model.evalTree_canonical hm hτ) hP
    exact ⟨C, f, rfl, hL, h, by simp [TWE.Model.evalTree, FileTree.Focus.resolve, hτ, hL]⟩

theorem walkIn_sound {P : TWE.Path Γ V} {L : V.Loc} {T : TWE.Tree V} {H : TWE.Shape}
    {τ : FileTree Γ} (hm : m.WF) (hτ : m.evalTree T = some (.tree τ)) (h : m ⊨ T ⊢ P ⇝ L ∶ H) :
    ∃ C f, FileTree.resolve (m.evalPath P) τ = some (C, f) ∧
      FileTree.resolve (m.σLoc L) τ = some (C, f) ∧ m.evalTree T[L] = some f ∧ f.shape = H := by
  obtain ⟨C, f, hP, hL, -, hsel⟩ := walk_sound hm hτ h.1
  exact ⟨C, f, hP, hL, hsel, (TWE.Model.sat_treeShape hsel).mp h.2⟩

theorem walkNotIn_sound {P : TWE.Path Γ V} {L : V.Loc} {T : TWE.Tree V}
    {τ : FileTree Γ} (hm : m.WF) (hτ : m.evalTree T = some (.tree τ))
    (h : m ⊨ T ⊢ P ⇝ L ∶∼ .absent) :
    ∃ C τ₁, FileTree.resolve (m.evalPath P) τ = some (C, .tree τ₁) ∧ C.path = m.σLoc L ∧
      m.evalTree T[L] = some (.tree τ₁) := by
  obtain ⟨C, τ₁ | _, hP, -, hCL, hsel⟩ := walk_sound hm hτ h.1
  · exact ⟨C, τ₁, hP, hCL, hsel⟩
  · exact absurd ((TWE.Model.sat_treeShape hsel).mpr rfl) h.2

theorem sstep_sound_aux {c c' : Command Γ X} {s s' : SState Γ X V}
    (hm : m.WF) (h : (c, s) ⇝ (c', s')) (hπ : m ⊨ s'.π)
    (hρ : s.store.Valid m)
    {τ τ' : FileTree Γ} (hτ : m.evalTree s.tree = some (.tree τ))
    (hτ' : m.evalTree s'.tree = some (.tree τ')) :
    s'.store.Valid m ∧
      ((c, ⟨⟦s.store⟧ m, τ⟩) ⟶ (c', ⟨⟦s'.store⟧ m, τ'⟩)) := by
  induction h generalizing τ τ' with
  | context hstep ih => exact (ih hπ hρ hτ hτ').imp_right Step.context
  | assign hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨v', hv', hEval⟩ := seval_sound hev hπ.2 hρ
      rw [TWE.Model.instantiateStore_set hv']
      exact ⟨SStore.valid_set hρ hv', Step.assign hEval⟩
  | seq => cases hτ.symm.trans hτ'; exact ⟨hρ, Step.seq⟩
  | ifTrue hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨_, ⟨⟩, hEval⟩ := seval_sound hev hπ.1.2 hρ
      exact ⟨hρ, Step.ifTrue (decide_eq_true hπ.2 ▸ hEval)⟩
  | ifFalse hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨_, ⟨⟩, hEval⟩ := seval_sound hev hπ.1.2 hρ
      exact ⟨hρ, Step.ifFalse (decide_eq_false hπ.2 ▸ hEval)⟩
  | «while» => cases hτ.symm.trans hτ'; exact ⟨hρ, Step.while⟩
  | create L hev heq hsat =>
      subst heq
      obtain ⟨C, f, hres, hresL, -, hsh⟩ := walkIn_sound hm hτ hπ.2
      obtain rfl := FileTree.Focus.eq_of_shape_absent hsh
      obtain ⟨_, ⟨⟩, hfill⟩ := (TWE.Model.evalTree_update_iff hτ hresL).mp hτ'
      exact ⟨hρ, Step.create (seval_sound_path hev hπ.1.2 hρ) hres hfill⟩
  | mkdir L hev heq hsat =>
      subst heq
      obtain ⟨C, f, hres, hresL, -, hsh⟩ := walkIn_sound hm hτ hπ.2
      obtain rfl := FileTree.Focus.eq_of_shape_absent hsh
      obtain ⟨_, ⟨⟩, hfill⟩ := (TWE.Model.evalTree_update_iff hτ hresL).mp hτ'
      exact ⟨hρ, Step.mkdir (seval_sound_path hev hπ.1.2 hρ) hres hfill⟩
  | unlink L hev heq hsat =>
      subst heq
      obtain ⟨C, f, hres, hresL, -, hsh⟩ := walkIn_sound hm hτ hπ.2
      obtain rfl := FileTree.Focus.eq_of_shape_file hsh
      obtain ⟨_, ⟨⟩, hfill⟩ := (TWE.Model.evalTree_update_iff hτ hresL).mp hτ'
      exact ⟨hρ, Step.unlink (seval_sound_path hev hπ.1.2 hρ) hres hfill⟩
  | rmdir L hev heq hsat =>
      subst heq
      obtain ⟨C, f, hres, hresL, hsel, hsh⟩ := walkIn_sound hm hτ hπ.2.1
      obtain ⟨⟨l⟩, rfl⟩ := FileTree.Focus.eq_of_shape_dirc hsh
      obtain rfl : l = [] := by
        simpa [TWE.Model.satAtom, TWE.Model.evalNameSet, hsel, FileTree.Entries.dom] using hπ.2.2
      obtain ⟨_, ⟨⟩, hfill⟩ := (TWE.Model.evalTree_update_iff hτ hresL).mp hτ'
      exact ⟨hρ, Step.rmdir (seval_sound_path hev hπ.1.2 hρ) hres hfill⟩
  | rename L₁ L₂ hev₁ hev₂ heq hsat =>
      subst heq
      obtain ⟨C₁, τ₁, hres₁, hCL₁, hsel₁⟩ := walkNotIn_sound hm hτ hπ.2.1
      have hresL₁ := hCL₁ ▸ resolve_path (TWE.Model.evalTree_canonical hm hτ) hres₁
      obtain ⟨τmid, hmid⟩ := TWE.Model.evalTree_upd_pred hτ'
      obtain ⟨_, ⟨⟩, hfill₁⟩ := (TWE.Model.evalTree_update_iff hτ hresL₁).mp hmid
      obtain ⟨C₂, f₂, hres₂, hresL₂, -, hsh₂⟩ := walkIn_sound hm hmid hπ.2.2
      obtain rfl := FileTree.Focus.eq_of_shape_absent hsh₂
      obtain ⟨_, hg, hfill₂⟩ := (TWE.Model.evalTree_update_iff hmid hresL₂).mp hτ'
      cases hsel₁.symm.trans hg
      exact ⟨hρ, Step.rename (seval_sound_path hev₁ hπ.1.1.2 hρ) hres₁ hfill₁
        (seval_sound_path hev₂ hπ.1.2 hρ) hres₂ hfill₂⟩
  | stat L hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨C, τ₁, hres, -, hsel⟩ := walkNotIn_sound hm hτ hπ.2
      have hInst := TWE.Model.instantiate_tree_iff.mpr ⟨τ₁, hsel, rfl⟩
      rw [TWE.Model.instantiateStore_set hInst]
      exact ⟨SStore.valid_set hρ hInst, Step.stat (seval_sound_path hev hπ.1.2 hρ) hres⟩
  | realpath L Q hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨C, τ₁, hres, hCL, -⟩ := walkNotIn_sound hm hτ hπ.2.1.1
      have hInst : ⟦(Q : TWE.Path Γ V)⟧ m = some (.path C.path) := by
        have h : m.σPath Q = m.σLoc L := by
          simpa [TWE.Model.satAtom, TWE.Model.evalPath] using hπ.2.1.2
        simp [SVal.instantiate, TWE.Model.evalPath, h, hCL]
      rw [TWE.Model.instantiateStore_set hInst]
      exact ⟨SStore.valid_set hρ hInst, Step.realpath (seval_sound_path hev hπ.1.2 hρ) hres⟩
  | opendir L S hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨C, f, hres, -, hsel, hsh⟩ := walkIn_sound hm hτ hπ.2.1
      obtain ⟨δ, rfl⟩ := FileTree.Focus.eq_of_shape_dirc hsh
      have hInst : ⟦(S : TWE.Set Γ V)⟧ m = some (.directory (FileTree.Entries.dom δ)) := by
        have h : m.σSet S = FileTree.Entries.dom δ := by
          simpa [TWE.Model.satAtom, TWE.Model.evalNameSet, hsel] using hπ.2.2
        simp [SVal.instantiate, TWE.Model.evalNameSet, h]
      rw [TWE.Model.instantiateStore_set hInst]
      exact ⟨SStore.valid_set hρ hInst, Step.opendir (seval_sound_path hev hπ.1.2 hρ) hres⟩
  | readdirNil hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨_, hv', hEval⟩ := seval_sound hev hπ.1.2 hρ
      obtain ⟨Δ, hS, rfl⟩ := TWE.Model.instantiate_set_eq hv'
      obtain rfl : Δ = ∅ := by
        simpa [TWE.Model.satAtom, TWE.Model.evalNameSet, hS] using hπ.2
      have hInstR : ⟦(⊥ : TWE.Formula Γ V)⟧ m = some (.bool false) := rfl
      rw [TWE.Model.instantiateStore_set hv', TWE.Model.instantiateStore_set hInstR]
      exact ⟨SStore.valid_set (SStore.valid_set hρ hInstR) hv', Step.readdirNil hEval⟩
  | readdirCons R XA hev heq hsat =>
      subst heq
      cases hτ.symm.trans hτ'
      obtain ⟨_, hv', hEval⟩ := seval_sound hev hπ.1.2 hρ
      obtain ⟨Δ, hS, rfl⟩ := TWE.Model.instantiate_set_eq hv'
      obtain rfl : Δ = insert (m.σName XA) (m.σSet R) := by
        simpa [TWE.Model.satAtom, TWE.Model.evalNameSet, TWE.Model.evalName, hS] using hπ.2.1
      have hnotMem : m.σName XA ∉ m.σSet R := by
        simpa [TWE.Model.satAtom, TWE.Model.evalNameSet, TWE.Model.evalName] using hπ.2.2
      have hInstR : ⟦(⊤ : TWE.Formula Γ V)⟧ m = some (.bool true) := rfl
      have hInstX : ⟦(R : TWE.Set Γ V)⟧ m = some (.directory (m.σSet R)) := by
        simp [SVal.instantiate, TWE.Model.evalNameSet]
      have hInstY : ⟦(XA : TWE.Path Γ V)⟧ m = some (.path (Path.init (.name (m.σName XA)))) := by
        simp [SVal.instantiate, TWE.Model.evalPath, TWE.Model.evalComponent, TWE.Model.evalName,
          Path.init]
      rw [TWE.Model.instantiateStore_set hInstY, TWE.Model.instantiateStore_set hInstX,
        TWE.Model.instantiateStore_set hInstR, ← Finset.erase_insert hnotMem]
      exact ⟨SStore.valid_set (SStore.valid_set (SStore.valid_set hρ hInstR) hInstX) hInstY,
        Step.readdirCons hEval (Finset.mem_insert_self _ _)⟩

theorem smultistep_sound_aux {c c' : Command Γ X} {s s' : SState Γ X V}
    (hm : m.WF) (h : (c, s) ⇝* (c', s')) (hπ : m ⊨ s'.π)
    (hρ : s.store.Valid m)
    {τ τ' : FileTree Γ} (hτ : m.evalTree s.tree = some (.tree τ))
    (hτ' : m.evalTree s'.tree = some (.tree τ')) :
    s'.store.Valid m ∧
      ((c, ⟨⟦s.store⟧ m, τ⟩) ⟶* (c', ⟨⟦s'.store⟧ m, τ'⟩)) := by
  induction h generalizing τ τ' with
  | refl => cases hτ.symm.trans hτ'; exact ⟨hρ, Multistep.refl⟩
  | single hstep => exact (sstep_sound_aux hm hstep hπ hρ hτ hτ').imp_right Multistep.single
  | trans hpre hlast ih =>
      obtain ⟨τ'', hτ''⟩ := SStep.evalTree_pred hlast hτ'
      obtain ⟨hρ'', hmulti⟩ := ih (SStep.pc_mono hlast hπ) hτ hτ''
      exact (sstep_sound_aux hm hlast hπ hρ'' hτ'' hτ').imp_right (Multistep.trans hmulti)

theorem smultistep_sound
    {c c' : Command Γ X} {ς ς' : State Γ X} {sς sς' : SState Γ X V} :
    ((c, sς) ⇝* (c', sς')) → m.WF → (m ⊫ sς) → (m ⊨ sς'.π) →
      ⟦sς⟧  m = some ς  →
      ⟦sς'⟧ m = some ς' →
      ((c, ς) ⟶* (c', ς')) := by
  intro h hm ⟨_, hρ⟩ hπ hς hς'
  obtain ⟨τ, hτ, rfl⟩ := TWE.Model.instantiateState_some hς
  obtain ⟨τ', hτ', rfl⟩ := TWE.Model.instantiateState_some hς'
  exact (smultistep_sound_aux hm h hπ hρ hτ hτ').2

end Accordion

end
