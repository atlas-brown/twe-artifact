module

public import Accordion.FileTree.Zipper
public import Accordion.FileTree.Properties
public import Accordion.FileTree.Entries.Properties

@[expose] public section

namespace Accordion

namespace FileTree

variable {Γ : Type}

theorem Frames.push_path (w : Frames Γ) (δ : Entries Γ (FileTree Γ)) (a : Γ) :
    (Frames.push w δ a).ctx.path = w.ctx.path ++ (a : Path Γ) := by
  simp [Frames.ctx, Ctx.path_compose_node]

variable [Ord Γ]

private theorem Zipper.path_ctx_frames_up (z : Zipper Γ) :
    z.up.frames.ctx.path = z.frames.ctx.path.dir := by
  cases z with
  | mk frames focus =>
      cases frames with
      | nil => cases focus <;> rfl
      | push w δ a =>
          cases focus <;>
            simp [Zipper.up, Frames.push_path, Path.append_eq, Path.join, Path.init, Path.dir]

private theorem Zipper.path_ctx_frames_of_traverse {τ : FileTree Γ} {p : Path Γ} {z : Zipper Γ}
    (h : Zipper.traverse p (Zipper.zip τ) = some z) : z.frames.ctx.path = p.norm := by
  induction p generalizing z with
  | nil =>
      cases h
      rfl
  | app p q ih =>
      simp only [Zipper.traverse, Option.bind_eq_some_iff] at h
      obtain ⟨z₀, hz₀, hm⟩ := h
      have hz₀path := ih hz₀
      rcases hf : z₀.focus with (- | δ) | - <;> simp only [Zipper.move, hf, reduceCtorEq] at hm
      cases q with
      | name a =>
          simp only [Zipper.down, hf] at hm
          split at hm <;> cases hm <;>
            exact (Frames.push_path _ _ _).trans (congrArg (Path.app · _) hz₀path)
      | parent =>
          cases hm
          exact (Zipper.path_ctx_frames_up z₀).trans (congrArg Path.dir hz₀path)
      | _ =>
          cases hm
          exact hz₀path

theorem path_eq_norm_of_resolve {τ : FileTree Γ} {p : Path Γ} {C : Ctx Γ} {f : Focus Γ}
    (h : resolve p τ = some (C, f)) : C.path = p.norm := by
  obtain ⟨z, hz, heq⟩ := Option.map_eq_some_iff.1 h
  cases heq
  exact Zipper.path_ctx_frames_of_traverse hz

theorem Zipper.traverse_join (p q : Path Γ) (z : Zipper Γ) :
    Zipper.traverse (p ++ q) z = (Zipper.traverse p z).bind (Zipper.traverse q) := by
  induction q with
  | nil => simp [Path.append_eq, Path.join, Zipper.traverse]
  | app q c ih =>
      simp only [Path.append_eq] at ih ⊢
      simp [Path.join, Zipper.traverse, ih, Option.bind_assoc]

theorem Zipper.traverse_descend_cons (a : Γ) (w : List Γ) (z : Zipper Γ) :
    Zipper.traverse (Path.descend (a :: w)) z =
      (z.down a).bind (Zipper.traverse (Path.descend w)) := by
  rw [Path.descend, Zipper.traverse_join]
  rcases z with ⟨frames, (_ | _) | _⟩ <;> rfl

theorem exists_resolve_app_parent_app_name {τ : FileTree Γ} {p : Path Γ} {C : Ctx Γ}
    {δ : Entries Γ (FileTree Γ)} (h : resolve p τ = some (C, .tree (.dirc δ))) (a : Γ) :
    ∃ r, resolve (.app (.app p ‥) (.name a)) τ = some r := by
  unfold resolve at h ⊢
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨frames, focus⟩, hz, heq⟩ := h
  obtain rfl : focus = .tree (.dirc δ) := congrArg Prod.snd heq
  cases frames <;>
    simp [Zipper.traverse, hz, Zipper.move, Zipper.up, Zipper.down] <;> split <;> simp

theorem Zipper.zip_canonical {τ : FileTree Γ} (hτ : τ.Canonical) :
    (Zipper.zip τ).Canonical := ⟨trivial, hτ⟩

theorem Zipper.down_canonical {z : Zipper Γ} (hz : z.Canonical) {a : Γ}
    {z' : Zipper Γ} (h : z.down a = some z') : z'.Canonical := by
  obtain ⟨hctx, hfocus⟩ := hz
  rcases hfoc : z.focus with τ | -
  · rcases τ with - | δ
    · simp [Zipper.down, hfoc] at h
    · simp only [Zipper.down, hfoc] at h
      rw [hfoc] at hfocus
      rcases hδ : δ[a]? with _ | τa
      · simp only [hδ] at h
        injection h with h
        subst h
        refine ⟨?_, trivial⟩
        simp only [Frames.ctx]
        exact (Ctx.canonical_compose_node _ _ _).mpr ⟨hctx, hfocus⟩
      · simp only [hδ] at h
        injection h with h
        subst h
        refine ⟨?_, canonical_of_lookup hfocus hδ⟩
        simp only [Frames.ctx]
        exact (Ctx.canonical_compose_node _ _ _).mpr
          ⟨hctx, canonical_erase_dirc hfocus⟩
  · simp [Zipper.down, hfoc] at h

theorem Zipper.up_canonical [Std.TransOrd Γ] {z : Zipper Γ} (hz : z.Canonical) :
    z.up.Canonical := by
  obtain ⟨frames, focus⟩ := z
  obtain ⟨hctx, hfocus⟩ := hz
  cases frames with
  | nil => exact ⟨hctx, hfocus⟩
  | push w δ a =>
      simp only [Frames.ctx] at hctx
      obtain ⟨hw, hδ⟩ := (Ctx.canonical_compose_node _ _ _).mp hctx
      cases focus with
      | tree τ =>
          simp only [Zipper.up]
          exact ⟨hw, canonical_insert_dirc hδ hfocus⟩
      | abst =>
          simp only [Zipper.up]
          exact ⟨hw, hδ⟩

theorem Zipper.traverse_canonical [Std.TransOrd Γ] {τ : FileTree Γ} (hτ : τ.Canonical) :
    ∀ (p : Path Γ) (z : Zipper Γ), Zipper.traverse p (Zipper.zip τ) = some z → z.Canonical := by
  intro p
  induction p with
  | nil =>
      intro z hz
      simp only [Zipper.traverse, Option.some.injEq] at hz
      exact hz ▸ Zipper.zip_canonical hτ
  | app p q ih =>
      intro z hz
      simp only [Zipper.traverse, Option.bind_eq_some_iff] at hz
      obtain ⟨z0, hz0, hstep⟩ := hz
      have hz0c := ih z0 hz0
      rcases hfoc : z0.focus with τ0 | -
      · rcases τ0 with - | δ
        · simp [Zipper.move, hfoc] at hstep
        · cases q with
          | name a =>
              simp only [Zipper.move, hfoc] at hstep
              exact Zipper.down_canonical hz0c hstep
          | parent =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              exact hstep ▸ Zipper.up_canonical hz0c
          | self =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              exact hstep ▸ hz0c
          | empty =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              exact hstep ▸ hz0c
      · simp [Zipper.move, hfoc] at hstep

theorem Zipper.traverse_idem [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] {τ : FileTree Γ}
    (hτ : τ.Canonical) :
    ∀ (p : Path Γ) (z : Zipper Γ), Zipper.traverse p (Zipper.zip τ) = some z →
      Zipper.traverse z.frames.ctx.path (Zipper.zip τ) = some z := by
  intro p
  induction p with
  | nil =>
      intro z hz
      simp only [Zipper.traverse, Option.some.injEq] at hz
      subst hz
      simp [Zipper.zip, Frames.ctx, Ctx.path, Zipper.traverse]
  | app p q ih =>
      intro z hz
      simp only [Zipper.traverse, Option.bind_eq_some_iff] at hz
      obtain ⟨z0, hz0, hstep⟩ := hz
      have hz0path := ih z0 hz0
      rcases hfoc : z0.focus with τ0 | -
      · rcases τ0 with - | δ
        · simp [Zipper.move, hfoc] at hstep
        · cases q with
          | name a =>
              simp only [Zipper.move, Zipper.down, hfoc] at hstep
              rcases hδ : δ[a]? with _ | τa
              · simp only [hδ, Option.some.injEq] at hstep
                subst hstep
                simp only [Frames.push_path, Path.append_eq, Path.init, Path.join,
                  Zipper.traverse, Option.bind_eq_some_iff]
                exact ⟨z0, hz0path, by simp only [Zipper.move, Zipper.down, hfoc, hδ]⟩
              · simp only [hδ, Option.some.injEq] at hstep
                subst hstep
                simp only [Frames.push_path, Path.append_eq, Path.init, Path.join,
                  Zipper.traverse, Option.bind_eq_some_iff]
                exact ⟨z0, hz0path, by simp only [Zipper.move, Zipper.down, hfoc, hδ]⟩
          | parent =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              cases hz0frames : z0.frames with
              | nil =>
                  have hz0up : z0.up = z0 := by
                    simp only [Zipper.up, hz0frames]
                    rw [← hz0frames]
                  rw [← hstep, hz0up]
                  exact hz0path
              | push w δw a =>
                  have hz0up : z0.up = ⟨w, .tree (.dirc (δw.insert a (.dirc δ)))⟩ := by
                    simp [Zipper.up, hz0frames, hfoc]
                  have hz0pathEq :
                      z0.frames.ctx.path = Path.join w.ctx.path (Path.init (.name a)) := by
                    rw [hz0frames]; exact Frames.push_path w δw a
                  rw [hz0pathEq] at hz0path
                  simp only [Path.init, Path.join, Zipper.traverse, Option.bind_eq_some_iff]
                    at hz0path
                  obtain ⟨zw, hzw, hstepzw⟩ := hz0path
                  rcases hfoczw : zw.focus with τw | -
                  · rcases τw with - | δw'
                    · simp [Zipper.move, hfoczw] at hstepzw
                    · simp only [Zipper.move, Zipper.down, hfoczw] at hstepzw
                      rcases hδw' : δw'[a]? with _ | τaw
                      · simp only [hδw', Option.some.injEq] at hstepzw
                        subst hstepzw
                        simp at hfoc
                      · simp only [hδw', Option.some.injEq] at hstepzw
                        subst hstepzw
                        simp only at hz0frames hfoc
                        injection hz0frames with hzwframes hδeq
                        injection hfoc with hτaw
                        have hzwcanon := Zipper.traverse_canonical hτ w.ctx.path zw hzw
                        have hδw'canon : δw'.Canonical := by
                          simp only [Zipper.Canonical, Focus.Canonical, hfoczw] at hzwcanon
                          obtain ⟨-, hfc⟩ := hzwcanon
                          cases hfc with
                          | dirc hc _ => exact hc
                        have hins : (δw'.erase a).insert a τaw = δw' :=
                          Entries.insert_erase hδw'canon hδw'
                        rw [hδeq, hτaw] at hins
                        rw [← hstep, hz0up, hins, ← hzwframes, ← hfoczw]
                        show Zipper.traverse zw.frames.ctx.path (Zipper.zip τ) = some zw
                        rw [hzwframes]
                        exact hzw
                  · simp [Zipper.move, hfoczw] at hstepzw
          | self =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              rw [← hstep]
              exact hz0path
          | empty =>
              simp only [Zipper.move, hfoc] at hstep
              injection hstep with hstep
              rw [← hstep]
              exact hz0path
      · simp [Zipper.move, hfoc] at hstep

theorem resolve_eq_of_norm_eq [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] {τ : FileTree Γ}
    (hτ : τ.Canonical) {p q : Path Γ} {r r' : Ctx Γ × Focus Γ}
    (hp : resolve p τ = some r) (hq : resolve q τ = some r') (h : p.norm = q.norm) : r = r' := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.1 hq
  have e := Zipper.traverse_idem hτ p z hz
  rw [Zipper.path_ctx_frames_of_traverse hz, h, ← Zipper.path_ctx_frames_of_traverse hz',
    Zipper.traverse_idem hτ q z' hz'] at e
  cases e
  rfl

theorem resolve_canonical [Std.TransOrd Γ] {p : Path Γ} {τ : FileTree Γ}
    {C : Ctx Γ} {f : Focus Γ}
    (hτ : τ.Canonical) (h : resolve p τ = some (C, f)) : f.Canonical := by
  unfold resolve at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨z, hz, heq⟩ := h
  have hzc := Zipper.traverse_canonical hτ p z hz
  rw [Prod.mk.injEq] at heq
  exact heq.2 ▸ hzc.2

theorem resolve_ctx_canonical [Std.TransOrd Γ] {p : Path Γ} {τ : FileTree Γ}
    {C : Ctx Γ} {f : Focus Γ}
    (hτ : τ.Canonical) (h : resolve p τ = some (C, f)) : C.Canonical := by
  unfold resolve at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨z, hz, heq⟩ := h
  have hzc := Zipper.traverse_canonical hτ p z hz
  rw [Prod.mk.injEq] at heq
  exact heq.1 ▸ hzc.1

theorem exists_resolve_dirc_of_resolve_app {τ : FileTree Γ} {p : Path Γ} {c : Component Γ}
    {r : Ctx Γ × Focus Γ} (h : resolve (.app p c) τ = some r) :
    ∃ C δ, resolve p τ = some (C, .tree (.dirc δ)) := by
  obtain ⟨z, hz, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨⟨frames, focus⟩, hz', hmove⟩ := Option.bind_eq_some_iff.1 hz
  rcases focus with (_ | δ) | _ <;> simp [Zipper.move] at hmove
  exact ⟨frames.ctx, δ, by simp [resolve, hz']⟩

/-- A walk that continues past `p` finds a directory at `p`. -/
theorem exists_resolve_dirc_of_resolve_join_app {τ : FileTree Γ} {p q : Path Γ}
    {c : Component Γ} {r : Ctx Γ × Focus Γ} (h : resolve (p ++ .app q c) τ = some r) :
    ∃ C δ, resolve p τ = some (C, .tree (.dirc δ)) := by
  induction q generalizing c r with
  | nil => exact exists_resolve_dirc_of_resolve_app h
  | app q c' ih =>
      obtain ⟨C, δ, h'⟩ := exists_resolve_dirc_of_resolve_app (p := p.join (.app q c')) (c := c) h
      exact ih h'

theorem Zipper.map_traverse_descend (w : List Γ) (z : Zipper Γ) :
    (Zipper.traverse (Path.descend w) z).map (fun z' => (z'.frames.ctx, z'.focus)) =
      ((Zipper.traverse (Path.descend w) ⟨.nil, z.focus⟩).map
        fun z' => (z'.frames.ctx, z'.focus)).map fun r => (z.frames.ctx.compose r.1, r.2) := by
  induction w generalizing z with
  | nil => simp [Path.descend, Zipper.traverse, Frames.ctx]
  | cons a w ih =>
      rw [Zipper.traverse_descend_cons, Zipper.traverse_descend_cons]
      rcases z with ⟨frames, (_ | δ) | _⟩
      · rfl
      · cases h : δ[a]? <;> simp only [Zipper.down, h, Option.bind_some] <;>
          rw [ih ⟨.push frames _ a, _⟩, ih ⟨.push .nil _ a, _⟩] <;>
          simp [Option.map_map, Function.comp_def, Frames.ctx, Ctx.compose, Ctx.compose_assoc]
      · rfl

theorem resolve_descend_cons (a : Γ) (w : List Γ) (δ : Entries Γ (FileTree Γ)) :
    resolve (Path.descend (a :: w)) (.dirc δ) =
      match δ[a]? with
      | some τ => (resolve (Path.descend w) τ).map fun r => (.node (δ.erase a) a r.1, r.2)
      | none => if w = [] then some (.node δ a .hole, .abst) else none := by
  rw [resolve, Zipper.traverse_descend_cons]
  cases h : δ[a]? with
  | some τ =>
      simp only [Zipper.zip, Zipper.down, h, Option.bind_some]
      rw [Zipper.map_traverse_descend]
      simp [resolve, Zipper.zip, Option.map_map, Function.comp_def, Frames.ctx, Ctx.compose]
  | none =>
      cases w with
      | nil => simp [Zipper.zip, Zipper.down, h, Path.descend, Zipper.traverse, Frames.ctx,
          Ctx.compose]
      | cons b w => simp [Zipper.zip, Zipper.down, h, Zipper.traverse_descend_cons]

private theorem resolve_descend_cons_ne_abst {δ δ' : Entries Γ (FileTree Γ)} {b : Γ}
    {w : List Γ} {τ : FileTree Γ} {C D : Ctx Γ} (h : δ'[b]? = δ[b]?)
    (hw : resolve (Path.descend (b :: w)) (.dirc δ) = some (C, .tree τ)) :
    resolve (Path.descend (b :: w)) (.dirc δ') ≠ some (D, .abst) := by
  rw [resolve_descend_cons] at hw ⊢
  rw [h]
  cases hb : δ[b]? with
  | none => simp [hb] at hw
  | some τ₁ =>
      simp only [hb] at hw ⊢
      obtain ⟨⟨C₁, f⟩, h₁, ⟨⟩⟩ := Option.map_eq_some_iff.1 hw
      simp [h₁]

/-- Filling an absent node leaves no existing node absent. -/
theorem resolve_descend_ne_abst_of_fill [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    {τ τ' τ₁ : FileTree Γ} {f : Focus Γ} {v w : List Γ} {C D D' : Ctx Γ}
    (hv : resolve (Path.descend v) τ = some (D, .abst)) (hfill : D.fill f = some τ')
    (hw : resolve (Path.descend w) τ = some (C, .tree τ₁)) :
    resolve (Path.descend w) τ' ≠ some (D', .abst) := by
  induction v generalizing τ τ' τ₁ w C D D' with
  | nil => simp [Path.descend, resolve, Zipper.traverse, Zipper.zip] at hv
  | cons a v ih =>
      rcases w with _ | ⟨b, w⟩
      · simp [Path.descend, resolve, Zipper.traverse, Zipper.zip]
      rcases τ with _ | δ
      · simp [resolve, Zipper.traverse_descend_cons, Zipper.zip, Zipper.down] at hv
      have hne : ∀ {δ' : Entries Γ (FileTree Γ)}, (b ≠ a → δ'[b]? = δ[b]?) → b ≠ a →
          resolve (Path.descend (b :: w)) (.dirc δ') ≠ some (D', .abst) :=
        fun h hb => resolve_descend_cons_ne_abst (h hb) hw
      have hcmp : b ≠ a → compare a b ≠ .eq := fun hb h => hb (Entries.compare_eq_iff.1 h).symm
      rw [resolve_descend_cons] at hv
      cases ha : δ[a]? with
      | none =>
          obtain rfl | hb := eq_or_ne b a
          · simp [resolve_descend_cons, ha] at hw
          simp only [ha, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hv
          obtain ⟨-, rfl, -⟩ := hv
          rcases f with τ₂ | _ <;> cases hfill
          · exact hne (fun hb => Entries.lookup_insert_ne _ _ _ _ (hcmp hb)) hb
          · exact hne (fun _ => rfl) hb
      | some τ₀ =>
          simp only [ha] at hv
          obtain ⟨⟨D₁, _⟩, hv₁, ⟨⟩⟩ := Option.map_eq_some_iff.1 hv
          cases hf : D₁.fill f with
          | none =>
              rcases D₁ with _ | _
              · cases Path.descend_injective (a₂ := [])
                  ((Path.norm_descend v).symm.trans (path_eq_norm_of_resolve hv₁).symm)
                simp [Path.descend, resolve, Zipper.traverse, Zipper.zip] at hv₁
              · simp only [Ctx.fill] at hf
                split at hf <;> cases hf
          | some τ₂ =>
              simp only [Ctx.fill, hf, Option.some.injEq] at hfill
              subst hfill
              obtain rfl | hb := eq_or_ne b a
              · rw [resolve_descend_cons, ha] at hw
                obtain ⟨⟨C₁, _⟩, hw₁, ⟨⟩⟩ := Option.map_eq_some_iff.1 hw
                rw [resolve_descend_cons, Entries.getElem?_eq_lookup, Entries.lookup_insert_self]
                intro h
                obtain ⟨⟨D₁', _⟩, h₁, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
                exact ih hv₁ hf hw₁ h₁
              · exact hne (fun hb => (Entries.lookup_insert_ne _ _ _ _ (hcmp hb)).trans
                  (Entries.lookup_erase_ne _ _ _ (hcmp hb))) hb

end FileTree

end Accordion

end
