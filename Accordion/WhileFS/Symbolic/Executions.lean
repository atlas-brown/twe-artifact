module

public import Accordion.WhileFS.Symbolic.Adequacy
public import Accordion.WhileFS.Symbolic.Executions.Defs
public import Accordion.WhileFS.Notation

@[expose] public section

namespace Accordion

open scoped TWE Accordion.Formula

variable {Γ X : Type} {V : TWE.Vars} [Ord Γ] [DecidableEq Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

namespace TWE.Model

variable {m : TWE.Model Γ V} {T U : TWE.Tree V} {P Q : TWE.Path Γ V} {L L' : V.Loc}

omit [DecidableEq Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] in
theorem wf_ofTree [Inhabited Γ] {τ : FileTree Γ} (hτ : τ.Canonical) (loc : V.Loc → List Γ) :
    (ofTree τ loc).WF :=
  ⟨fun _ => Accordion.Path.linear_descend _, fun _ => hτ⟩

omit [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] in
theorem exists_evalTree_of_sat_treeWalk (h : m ⊨ T ⊢ P ⇝ L) :
    ∃ τ, m.evalTree T = some (.tree τ) := by
  simp only [Formula.sat, sat_iff_satAtom, satAtom] at h
  split at h
  · exact ⟨_, ‹_›⟩
  · exact h.elim

/-- After a node is created at the end of a walk, nothing the walk went through is absent. -/
theorem not_sat_absent_update_of_sat_absent (hm : m.WF) {r : Accordion.Path Γ}
    {c : Accordion.Component Γ}
    (hP : m.evalPath P = m.evalPath Q ++ .app r c) (h : m ⊨ T ⊢ P ⇝ L ∶ .absent) :
    ¬m ⊨ T[L ↦ U] ⊢ Q ⇝ L' ∶ .absent := by
  intro h'
  obtain ⟨τ, hτ⟩ := exists_evalTree_of_sat_treeWalk h.1
  obtain ⟨D, f, hP', hL, -, hf⟩ := walkIn_sound hm hτ h
  obtain rfl := FileTree.Focus.eq_of_shape_absent hf
  obtain ⟨τ', hτ'⟩ := exists_evalTree_of_sat_treeWalk h'.1
  obtain ⟨g, -, hfill⟩ := (evalTree_update_iff hτ hL).1 hτ'
  obtain ⟨D', f', hQ', -, -, hf'⟩ := walkIn_sound hm hτ' h'
  obtain rfl := FileTree.Focus.eq_of_shape_absent hf'
  obtain ⟨C, δ, hQ⟩ := FileTree.exists_resolve_dirc_of_resolve_join_app (hP ▸ hP')
  have hC : C.path = D'.path :=
    (FileTree.path_eq_norm_of_resolve hQ).trans (FileTree.path_eq_norm_of_resolve hQ').symm
  have a := resolve_path (evalTree_canonical hm hτ) hQ
  have b := resolve_path (evalTree_canonical hm hτ') hQ'
  rw [← Accordion.Path.descend_names_of_linear (hm.1 L)] at hL
  rw [← Accordion.Path.descend_names_of_linear C.path_linear] at a
  rw [← hC, ← Accordion.Path.descend_names_of_linear C.path_linear] at b
  exact FileTree.resolve_descend_ne_abst_of_fill hL hfill a b

theorem not_sat_absent_update_embedPath_of_sat_absent (hm : m.WF) {p q : Accordion.Path Γ}
    [hqp : q.IsStrictPrefix p] (h : m ⊨ T ⊢ ⌜p⌝ ⇝ L ∶ .absent) :
    ¬m ⊨ T[L ↦ U] ⊢ ⌜q⌝ ⇝ L' ∶ .absent := by
  obtain ⟨r, c, rfl⟩ := hqp.exists_eq_join_app
  exact not_sat_absent_update_of_sat_absent hm (r := r) (c := c)
    (by simp only [evalPath_embedPath]) h

grind_pattern not_sat_absent_update_embedPath_of_sat_absent =>
  m ⊨ T ⊢ ⌜p⌝ ⇝ L ∶ .absent, m ⊨ T[L ↦ U] ⊢ ⌜q⌝ ⇝ L' ∶ .absent

end TWE.Model

variable [DecidableEq X]

omit [DecidableEq Γ] in
theorem SEval.val_inv {ρ : SStore Γ X V} {v : Val Γ} {Φ : TWE.Formula Γ V} {w : SVal Γ V}
    (h : .val v ⇓[ρ] w ∣ Φ) : Φ = ⊤ ∧ w = embed v := by
  cases h
  exact ⟨rfl, rfl⟩

namespace SStep

variable {a b c' : Command Γ X} {e : Expr Γ X} {s s' : SState Γ X V}

theorem not_skip : ¬(.skip, s) ⇝ (c', s') := by
  intro h
  generalize hc : Command.skip = c at h
  induction h with
  | @context E _ _ _ _ _ ih =>
      cases E with
      | hole => exact ih hc
      | seq => cases hc
  | _ => cases hc

theorem seq_inv (h : (.seq a b, s) ⇝ (c', s')) :
    (a = .skip ∧ c' = b ∧ s' = s) ∨ ∃ a', c' = .seq a' b ∧ ((a, s) ⇝ (a', s')) := by
  generalize hc : Command.seq a b = c at h
  induction h with
  | @context E _ _ _ _ h ih =>
      cases E with
      | hole => exact ih hc
      | seq => cases hc; exact .inr ⟨_, rfl, .context h⟩
  | seq => cases hc; exact .inl ⟨rfl, rfl, rfl⟩
  | _ => cases hc

theorem create_inv (h : (.create e, s) ⇝ (c', s')) :
    ∃ (L : V.Loc) (P : TWE.Path Γ V) (Φ : TWE.Formula Γ V), (e ⇓[s.store] (.path P) ∣ Φ) ∧
      c' = .skip ∧ s' = ⟨s.store, s.tree[L ↦ .file], s.π ⋏ Φ ⋏ s.tree ⊢ P ⇝ L ∶ .absent⟩ := by
  generalize hc : Command.create e = c at h
  induction h with
  | @context E _ _ _ _ _ ih =>
      cases E with
      | hole => exact ih hc
      | seq => cases hc
  | create L hev hπ => cases hc; exact ⟨L, _, _, hev, rfl, by rw [hπ]⟩
  | _ => cases hc

theorem mkdir_inv (h : (.mkdir e, s) ⇝ (c', s')) :
    ∃ (L : V.Loc) (P : TWE.Path Γ V) (Φ : TWE.Formula Γ V), (e ⇓[s.store] (.path P) ∣ Φ) ∧
      c' = .skip ∧
        s' = ⟨s.store, s.tree[L ↦ .emptyDirc], s.π ⋏ Φ ⋏ s.tree ⊢ P ⇝ L ∶ .absent⟩ := by
  generalize hc : Command.mkdir e = c at h
  induction h with
  | @context E _ _ _ _ _ ih =>
      cases E with
      | hole => exact ih hc
      | seq => cases hc
  | mkdir L hev hπ => cases hc; exact ⟨L, _, _, hev, rfl, by rw [hπ]⟩
  | _ => cases hc

end SStep

namespace SMultistep

variable {a b c c' : Command Γ X} {e : Expr Γ X} {p : Path Γ} {s s' : SState Γ X V}

theorem cases_head (h : (c, s) ⇝* (c', s')) :
    (c' = c ∧ s' = s) ∨ ∃ c₁ s₁, ((c, s) ⇝ (c₁, s₁)) ∧ ((c₁, s₁) ⇝* (c', s')) := by
  induction h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | single h => exact .inr ⟨_, _, h, .refl⟩
  | trans _ hs ih =>
      rcases ih with ⟨rfl, rfl⟩ | ⟨c₁, s₁, h₁, hm⟩
      · exact .inr ⟨_, _, hs, .refl⟩
      · exact .inr ⟨c₁, s₁, h₁, .trans hm hs⟩

theorem skip_inv (h : (.skip, s) ⇝* (c', s')) : c' = .skip ∧ s' = s := by
  rcases h.cases_head with h | ⟨_, _, h, -⟩
  · exact h
  · exact absurd h SStep.not_skip

theorem seq_inv (h : (.seq a b, s) ⇝* (c', s')) :
    (∃ a', c' = .seq a' b ∧ ((a, s) ⇝* (a', s'))) ∨
      ∃ s'', ((a, s) ⇝* (.skip, s'')) ∧ ((b, s'') ⇝* (c', s')) := by
  generalize hc : Command.seq a b = c at h
  induction h with
  | refl => subst hc; exact .inl ⟨a, rfl, .refl⟩
  | single hs =>
      subst hc
      rcases hs.seq_inv with ⟨rfl, rfl, rfl⟩ | ⟨a', rfl, ha⟩
      · exact .inr ⟨_, .refl, .refl⟩
      · exact .inl ⟨a', rfl, .single ha⟩
  | trans _ hs ih =>
      rcases ih with ⟨a', rfl, ha⟩ | ⟨s'', ha, hb⟩
      · rcases hs.seq_inv with ⟨rfl, rfl, rfl⟩ | ⟨a'', rfl, hs'⟩
        · exact .inr ⟨_, ha, .refl⟩
        · exact .inl ⟨a'', rfl, .trans ha hs'⟩
      · exact .inr ⟨s'', ha, .trans hb hs⟩

@[grind →]
theorem seq_skip_inv {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    (h : (.seq a b, (⟨ρ, T, π⟩ : SState Γ X V)) ⇝* (.skip, s')) :
    ∃ ρ' T' π', ((a, (⟨ρ, T, π⟩ : SState Γ X V)) ⇝* (.skip, ⟨ρ', T', π'⟩)) ∧
      ((b, (⟨ρ', T', π'⟩ : SState Γ X V)) ⇝* (.skip, s')) := by
  rcases h.seq_inv with ⟨_, h, -⟩ | ⟨⟨_, _, _⟩, h⟩
  · cases h
  · exact ⟨_, _, _, h⟩

theorem create_skip_inv (h : (.create e, s) ⇝* (.skip, s')) :
    ∃ (L : V.Loc) (P : TWE.Path Γ V) (Φ : TWE.Formula Γ V), (e ⇓[s.store] (.path P) ∣ Φ) ∧
      s' = ⟨s.store, s.tree[L ↦ .file], s.π ⋏ Φ ⋏ s.tree ⊢ P ⇝ L ∶ .absent⟩ := by
  rcases h.cases_head with ⟨h, -⟩ | ⟨_, _, h, hm⟩
  · cases h
  · obtain ⟨L, P, Φ, hev, rfl, rfl⟩ := h.create_inv
    obtain ⟨-, rfl⟩ := hm.skip_inv
    exact ⟨L, P, Φ, hev, rfl⟩

theorem mkdir_skip_inv (h : (.mkdir e, s) ⇝* (.skip, s')) :
    ∃ (L : V.Loc) (P : TWE.Path Γ V) (Φ : TWE.Formula Γ V), (e ⇓[s.store] (.path P) ∣ Φ) ∧
      s' = ⟨s.store, s.tree[L ↦ .emptyDirc], s.π ⋏ Φ ⋏ s.tree ⊢ P ⇝ L ∶ .absent⟩ := by
  rcases h.cases_head with ⟨h, -⟩ | ⟨_, _, h, hm⟩
  · cases h
  · obtain ⟨L, P, Φ, hev, rfl, rfl⟩ := h.mkdir_inv
    obtain ⟨-, rfl⟩ := hm.skip_inv
    exact ⟨L, P, Φ, hev, rfl⟩

@[grind →]
theorem create_path_skip_inv {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    (h : (.create (.val (.path p)), (⟨ρ, T, π⟩ : SState Γ X V)) ⇝* (.skip, s')) :
    ∃ L : V.Loc, s' = ⟨ρ, T[L ↦ .file], π ⋏ ⊤ ⋏ T ⊢ ⌜p⌝ ⇝ L ∶ .absent⟩ := by
  obtain ⟨L, P, Φ, hev, rfl⟩ := h.create_skip_inv
  obtain ⟨rfl, ⟨⟩⟩ := SEval.val_inv hev
  exact ⟨L, rfl⟩

@[grind →]
theorem mkdir_path_skip_inv {ρ : SStore Γ X V} {T : TWE.Tree V} {π : TWE.Formula Γ V}
    (h : (.mkdir (.val (.path p)), (⟨ρ, T, π⟩ : SState Γ X V)) ⇝* (.skip, s')) :
    ∃ L : V.Loc, s' = ⟨ρ, T[L ↦ .emptyDirc], π ⋏ ⊤ ⋏ T ⊢ ⌜p⌝ ⇝ L ∶ .absent⟩ := by
  obtain ⟨L, P, Φ, hev, rfl⟩ := h.mkdir_skip_inv
  obtain ⟨rfl, ⟨⟩⟩ := SEval.val_inv hev
  exact ⟨L, rfl⟩

end SMultistep

namespace WhileFS.Symbolic

variable {c c' : Command Γ X} {m : TWE.Model Γ V} {τ τ' : FileTree Γ}

attribute [grind =] SState.init

omit [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] in
@[simp] theorem _root_.Accordion.SStore.instantiate_empty :
    ⟦(∅ : SStore Γ X V)⟧ m = ∅ := rfl

/-- Soundness for an execution from `SState.init`: the store hypotheses of `soundness` are discharged. -/
theorem soundness_init {T T' : TWE.Tree V} {ρ' : SStore Γ X V} {π : TWE.Formula Γ V}
    (h : (c, SState.init T) ⇝* (c', ⟨ρ', T', π⟩)) (hm : m.WF) (hπ : m ⊨ π)
    (hτ : m.evalTree T = some (.tree τ)) (hτ' : m.evalTree T' = some (.tree τ')) :
    (c, ⟨∅, τ⟩) ⟶* (c', ⟨⟦ρ'⟧ m, τ'⟩) :=
  soundness h hm ⟨trivial, nofun⟩ hπ (SState.instantiate_of_evalTree hτ)
    (SState.instantiate_of_evalTree hτ')

/-- Completeness for an execution from the empty store: the model of `completeness` is constructed. -/
theorem completeness_init [TWE.Vars.Comparable V] [TWE.Vars.Unbounded V] [Inhabited Γ]
    (x : V.Tree) (hτ : τ.Canonical) {ς' : State Γ X} (h : (c, ⟨∅, τ⟩) ⟶* (c', ς')) :
    ∃ sς' : SState Γ X V, ((c, SState.init (.var x)) ⇝* (c', sς')) ∧
      ∃ m : TWE.Model Γ V, m.WF ∧ (m ⊨ sς'.π) ∧ ⟦sς'⟧ m = some ς' :=
  let ⟨sς', hrun, m, hm, hsat, _, hς'⟩ :=
    completeness (m := .ofTree τ fun _ => []) (sς := SState.init (.var x))
      (TWE.Model.wf_ofTree hτ _) ⟨trivial, nofun⟩ rfl h
  ⟨sς', hrun, m, hm, hsat.1, hς'⟩

end WhileFS.Symbolic

end Accordion

end
