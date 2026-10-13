module

public import Accordion.TWE.Linear.ToWE.Properties.RewriteAtoms
public import Accordion.FileTree.Zipper.Properties
public import Accordion.Path.Measures

@[expose] public section

namespace Accordion

namespace TWE

open Linear.ToWE (WordModel WordModel.evalPath)
open scoped Linear.ToWE.BigConnectives

variable {Γ : Type} {V : TWE.Vars}

namespace Model

variable [Ord Γ] (m : TWE.Model Γ V)

theorem evalTree_select_eq_some_iff (τ : TWE.Tree V) (l : V.Loc) (f : FileTree.Focus Γ) :
    m.evalTree (.select τ l) = some f ↔
      ∃ g C, m.evalTree τ = some g ∧ g.resolve (m.σLoc l) = some (C, f) := by
  simp [TWE.Model.evalTree, Option.bind_eq_some_iff]

theorem evalTree_update_eq_some_iff (τ replacement : TWE.Tree V) (l : V.Loc)
    (updated : FileTree Γ) :
    m.evalTree (.update τ l replacement) = some (.tree updated) ↔
      ∃ base C oldFocus newFocus,
        m.evalTree τ = some (.tree base) ∧
        FileTree.resolve (m.σLoc l) base = some (C, oldFocus) ∧
        m.evalTree replacement = some newFocus ∧
        C.fill newFocus = some updated := by
  simp only [TWE.Model.evalTree]
  rcases m.evalTree τ with _ | _ | _ <;> simp [Option.bind_eq_some_iff]

theorem evalTree_update_ne_abst (τ replacement : TWE.Tree V) (l : V.Loc) :
    m.evalTree (.update τ l replacement) ≠ some .abst := by
  simp only [TWE.Model.evalTree]
  rcases m.evalTree τ with _ | _ | _ <;> simp [Option.bind_eq_some_iff]

theorem isSome_evalTree_update_iff (T T' : TWE.Tree V) (l : V.Loc) :
    (m.evalTree (.update T l T')).isSome ↔
      ∃ updated, m.evalTree (.update T l T') = some (.tree updated) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ by simp [h]⟩
  obtain ⟨_ | _, hf⟩ := Option.isSome_iff_exists.1 h
  · exact ⟨_, hf⟩
  · exact absurd hf (evalTree_update_ne_abst m T T' l)

end Model

namespace Path

@[simp] theorem all_hasLinearConstants_subterms (p : TWE.Path Γ V) :
    p.subterms.all TWE.Path.hasLinearConstants = p.hasLinearConstants := by
  induction p with
  | join p q ihp ihq =>
      simp only [TWE.Path.subterms, List.all_cons, List.all_append, ihp, ihq,
        TWE.Path.hasLinearConstants]
      cases p.hasLinearConstants <;> cases q.hasLinearConstants <;> rfl
  | norm p ih => simp [TWE.Path.subterms, ih, TWE.Path.hasLinearConstants]
  | _ => simp [TWE.Path.subterms]

@[simp] theorem hasLinearConstants_join (p q : TWE.Path Γ V) :
    (TWE.Path.join p q).hasLinearConstants = (p.hasLinearConstants && q.hasLinearConstants) :=
  rfl

@[simp] theorem hasLinearConstants_append (p q : TWE.Path Γ V) :
    (p ++ q).hasLinearConstants = (p.hasLinearConstants && q.hasLinearConstants) := rfl

@[simp] theorem hasLinearConstants_nil : (TWE.Path.nil : TWE.Path Γ V).hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_loc (l : V.Loc) :
    (TWE.Path.loc l : TWE.Path Γ V).hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_var (x : V.Path) :
    (TWE.Path.var x : TWE.Path Γ V).hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_name (a : TWE.Name Γ V) :
    (TWE.Path.init (.name a) : TWE.Path Γ V).hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_compVar (x : V.Comp) :
    (TWE.Path.init (.var x) : TWE.Path Γ V).hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_norm (p : TWE.Path Γ V) :
    (TWE.Path.norm p).hasLinearConstants = p.hasLinearConstants := rfl

theorem hasLinearConstants_of_linear [Ord Γ] (m : TWE.Model Γ V) {p : TWE.Path Γ V}
    (h : ∀ q ∈ p.subterms, (m.evalPath q).Linear) : p.hasLinearConstants := by
  induction p with
  | init c =>
      have := h _ (mem_subterms_self _)
      cases c <;> simp_all [TWE.Model.evalPath, TWE.Model.evalComponent, Accordion.Path.init,
        Accordion.Path.Linear, TWE.Path.hasLinearConstants]
  | join p q ihp ihq =>
      simp only [TWE.Path.hasLinearConstants, Bool.and_eq_true]
      exact ⟨ihp fun r hr ↦ h r (by simp [TWE.Path.subterms, hr]),
        ihq fun r hr ↦ h r (by simp [TWE.Path.subterms, hr])⟩
  | norm p ih => exact ih fun r hr ↦ h r (by simp [TWE.Path.subterms, hr])
  | _ => rfl

theorem evalWord_toWord [Ord Γ] (m : WordModel Γ V) (p : TWE.Path Γ V) :
    m.toWE.evalWord (TWE.Path.toWord p) = WordModel.evalPath m p := by
  induction p with
  | init b => rcases b with _ | _ | _ | (_ | _) | _ <;> rfl
  | join p q ihp ihq => simp [TWE.Path.toWord, WordModel.evalPath, ihp, ihq]
  | norm p ih => simpa [TWE.Path.toWord, WordModel.evalPath] using ih
  | _ => rfl

end Path

namespace Formula

@[simp] theorem hasLinearConstants_top :
    TWE.Formula.hasLinearConstants (Accordion.Formula.top : TWE.Formula Γ V) := rfl

@[simp] theorem hasLinearConstants_bot :
    TWE.Formula.hasLinearConstants (Accordion.Formula.bot : TWE.Formula Γ V) := rfl

@[simp] theorem hasLinearConstants_conj (φ ψ : TWE.Formula Γ V) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.conj φ ψ) =
      (φ.hasLinearConstants && ψ.hasLinearConstants) := by
  simp [TWE.Formula.hasLinearConstants, TWE.Formula.paths]

@[simp] theorem hasLinearConstants_disj (φ ψ : TWE.Formula Γ V) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.disj φ ψ) =
      (φ.hasLinearConstants && ψ.hasLinearConstants) := by
  simp [TWE.Formula.hasLinearConstants, TWE.Formula.paths]

@[simp] theorem hasLinearConstants_neg (φ : TWE.Formula Γ V) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.neg φ) = φ.hasLinearConstants := rfl

@[simp] theorem hasLinearConstants_atom (a : TWE.Atom Γ V) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.atom a : TWE.Formula Γ V) =
      match a with
      | .pathEq P Q => P.hasLinearConstants && Q.hasLinearConstants
      | .pathIsLin P | .treeWalk P _ _ => P.hasLinearConstants
      | .treeShape _ _ | .setEq _ _ | .setMem _ _ => true := by
  cases a <;> simp [TWE.Formula.hasLinearConstants, TWE.Formula.paths]

@[simp] theorem hasLinearConstants_bigConj (Fs : List (TWE.Formula Γ V)) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.bigConj Fs) =
      Fs.all TWE.Formula.hasLinearConstants := by
  induction Fs <;> simp_all [Accordion.Formula.bigConj]

@[simp] theorem hasLinearConstants_bigDisj (Fs : List (TWE.Formula Γ V)) :
    TWE.Formula.hasLinearConstants (Accordion.Formula.bigDisj Fs) =
      Fs.all TWE.Formula.hasLinearConstants := by
  induction Fs <;> simp_all [Accordion.Formula.bigDisj]

@[simp] theorem hasLinearConstants_all {α : Type} (xs : List α) (F : α → TWE.Formula Γ V) :
    (⋀ x ∈ xs, F x : TWE.Formula Γ V).hasLinearConstants =
      xs.all fun x ↦ (F x).hasLinearConstants := by
  change TWE.Formula.hasLinearConstants (Accordion.Formula.bigConj (xs.map F)) = _
  simp [List.all_map, Function.comp_def]

@[simp] theorem hasLinearConstants_any {α : Type} (xs : List α) (F : α → TWE.Formula Γ V) :
    (⋁ x ∈ xs, F x : TWE.Formula Γ V).hasLinearConstants =
      xs.all fun x ↦ (F x).hasLinearConstants := by
  change TWE.Formula.hasLinearConstants (Accordion.Formula.bigDisj (xs.map F)) = _
  simp [List.all_map, Function.comp_def]

theorem hasLinearConstants_of_mem_paths {φ : TWE.Formula Γ V} (hφ : φ.hasLinearConstants)
    {p : TWE.Path Γ V} (hp : p ∈ φ.paths) : p.hasLinearConstants :=
  List.all_eq_true.1 hφ p hp

theorem hasLinearConstants_of_linearAt [Ord Γ] {m : TWE.Model Γ V} {φ : TWE.Formula Γ V}
    (h : m.LinearAt φ) : φ.hasLinearConstants :=
  List.all_eq_true.2 fun _ hp ↦
    Path.hasLinearConstants_of_linear m fun q hq ↦ h q (mem_paths_of_mem_subterms hp hq)

theorem hasLinearConstants_of_SAT [Ord Γ] [DecidableEq Γ] {φ : TWE.Formula Γ V}
    (h : TWE.Linear.Formula.SAT φ) : φ.hasLinearConstants :=
  let ⟨⟨_, _, hlin⟩, _⟩ := h
  hasLinearConstants_of_linearAt hlin

end Formula

end TWE

namespace FileTree

variable {Γ : Type}

theorem Ctx.plug_hole [Ord Γ] (f : Focus Γ) : Ctx.plug .hole f = f := by
  cases f <;> rfl

theorem Ctx.plug_node [Ord Γ] (δ : Entries Γ (FileTree Γ)) (a : Γ) (C : Ctx Γ) (f : Focus Γ) :
    (Ctx.node δ a C).plug f = .tree (.dirc (δ.plug a (C.plug f))) := by
  simp only [Ctx.plug, Ctx.fill]
  cases C.fill f <;> rfl

theorem Entries.lookup_plug_self [Ord Γ] [Std.LawfulEqOrd Γ] (δ : Entries Γ (FileTree Γ)) (a : Γ)
    (f : Focus Γ) (ha : δ.lookup a = none) :
    (δ.plug a f).lookup a =
      match f with
      | .tree τ => some τ
      | .abst => none := by
  cases f with
  | tree τ => exact Entries.lookup_insert_self δ a τ
  | abst => exact ha

theorem Entries.lookup_plug_ne [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (δ : Entries Γ (FileTree Γ)) (a b : Γ) (f : Focus Γ) (hab : a ≠ b) :
    (δ.plug a f).lookup b = δ.lookup b := by
  cases f with
  | abst => rfl
  | tree τ => exact Entries.lookup_insert_ne δ a b τ (fun h ↦ hab (Entries.compare_eq_iff.mp h))

theorem Ctx.missing_compose_node [Ord Γ] (C : Ctx Γ) (δ : Entries Γ (FileTree Γ)) (a : Γ) :
    (C.compose (.node δ a .hole)).Missing ↔ C.Missing ∧ δ.lookup a = none := by
  induction C <;> simp_all [Ctx.compose, Ctx.Missing, and_assoc]

theorem Ctx.plug_compose [Ord Γ] (C D : Ctx Γ) (f : Focus Γ) :
    (C.compose D).plug f = C.plug (D.plug f) := by
  induction C with
  | hole => simp [Ctx.compose, Ctx.plug_hole]
  | node δ a C ih => rw [Ctx.compose, Ctx.plug_node, Ctx.plug_node, ih]

theorem Ctx.plug_eq_tree_of_fill [Ord Γ] {C : Ctx Γ} {f : Focus Γ} {τ : FileTree Γ}
    (hfill : C.fill f = some τ) : C.plug f = .tree τ := by
  simp [Ctx.plug, hfill]

theorem Ctx.path_eq_descend_word (C : Ctx Γ) : C.path = Path.descend C.word := by
  induction C with
  | hole => rfl
  | node δ a C ih => rw [Ctx.path, Ctx.word, ih]; rfl

open Focus (follow)

theorem Focus.follow_append [Ord Γ] (f : FileTree.Focus Γ) (left right : List Γ) :
    follow f (left ++ right) = (follow f left).bind (follow · right) := by
  induction left generalizing f with
  | nil => rfl
  | cons a left ih =>
      rcases f with (_ | δ) | _
      · rfl
      · cases h : δ.lookup a <;> simp [follow, h, ih]
      · rfl

theorem Focus.follow_plug_word_append [Ord Γ] [Std.LawfulEqOrd Γ] (C : FileTree.Ctx Γ)
    (f : FileTree.Focus Γ) (suffix : List Γ) (hC : FileTree.Ctx.Missing C) :
    follow (FileTree.Ctx.plug C f) (FileTree.Ctx.word C ++ suffix) = follow f suffix := by
  induction C with
  | hole => simp [FileTree.Ctx.word, FileTree.Ctx.plug_hole]
  | node δ a C ih =>
      obtain ⟨ha, hC⟩ := hC
      have ih := ih hC
      rw [FileTree.Ctx.plug_node]
      cases hplug : FileTree.Ctx.plug C f <;> rw [hplug] at ih <;>
        simpa [FileTree.Ctx.word, follow, FileTree.Entries.getElem?_eq_lookup,
          FileTree.Entries.lookup_plug_self δ a _ ha] using ih

theorem Zipper.map_focus_traverse_descend [Ord Γ] (w : List Γ) (z : FileTree.Zipper Γ) :
    (FileTree.Zipper.traverse (Path.descend w) z).map FileTree.Zipper.focus =
      follow z.focus w := by
  induction w generalizing z with
  | nil => rfl
  | cons a w ih =>
      rw [Zipper.traverse_descend_cons]
      rcases z with ⟨frames, (_ | δ) | _⟩
      · rfl
      · cases hchild : δ[a]? <;>
          simp [FileTree.Zipper.down, follow, hchild, ih]
      · rfl

theorem Zipper.missing_ctx_of_traverse_descend [Ord Γ] (w : List Γ) (z z' : FileTree.Zipper Γ)
    (hz : FileTree.Ctx.Missing z.frames.ctx)
    (h : FileTree.Zipper.traverse (Path.descend w) z = some z') :
    FileTree.Ctx.Missing z'.frames.ctx := by
  induction w generalizing z with
  | nil => cases h; exact hz
  | cons a w ih =>
      rw [Zipper.traverse_descend_cons, Option.bind_eq_some_iff] at h
      obtain ⟨z₁, hdown, hrest⟩ := h
      refine ih z₁ ?_ hrest
      rcases z with ⟨frames, (_ | δ) | _⟩ <;>
        simp only [FileTree.Zipper.down, reduceCtorEq] at hdown
      cases hlookup : δ[a]? <;> simp only [hlookup, Option.some.injEq] at hdown <;> subst z₁ <;>
        simp only [FileTree.Frames.ctx, FileTree.Ctx.missing_compose_node] <;> refine ⟨hz, ?_⟩
      · exact hlookup
      · exact FileTree.Entries.lookup_erase_self δ a

theorem Zipper.plug_ctx_of_traverse_descend [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    {base : FileTree Γ} (w : List Γ) (z z' : FileTree.Zipper Γ) (hz : z.Canonical)
    (hplug : FileTree.Ctx.plug z.frames.ctx z.focus = .tree base)
    (h : FileTree.Zipper.traverse (Path.descend w) z = some z') :
    FileTree.Ctx.plug z'.frames.ctx z'.focus = .tree base := by
  induction w generalizing z with
  | nil => cases h; exact hplug
  | cons a w ih =>
      rw [Zipper.traverse_descend_cons, Option.bind_eq_some_iff] at h
      obtain ⟨z₁, hdown, hrest⟩ := h
      refine ih z₁ (FileTree.Zipper.down_canonical hz hdown) ?_ hrest
      rcases z with ⟨frames, (_ | δ) | _⟩ <;>
        simp only [FileTree.Zipper.down, reduceCtorEq] at hdown
      cases hlookup : δ[a]? <;> simp only [hlookup, Option.some.injEq] at hdown <;> subst z₁ <;>
        rw [FileTree.Frames.ctx, FileTree.Ctx.plug_compose, FileTree.Ctx.plug_node,
          FileTree.Ctx.plug_hole]
      · exact hplug
      · rw [FileTree.Entries.plug,
          FileTree.Entries.insert_erase (by cases hz.2; assumption) hlookup]
        exact hplug

theorem missing_of_resolve_descend [Ord Γ] {w : List Γ} {τ : FileTree Γ}
    {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ}
    (h : FileTree.resolve (Path.descend w) τ = some (C, f)) : FileTree.Ctx.Missing C := by
  obtain ⟨z, hz, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
  exact Zipper.missing_ctx_of_traverse_descend w (FileTree.Zipper.zip τ) z trivial hz

theorem plug_eq_tree_of_resolve_descend [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] {w : List Γ}
    {τ : FileTree Γ} {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ} (hτ : τ.Canonical)
    (h : FileTree.resolve (Path.descend w) τ = some (C, f)) : FileTree.Ctx.plug C f = .tree τ := by
  obtain ⟨z, hz, ⟨⟩⟩ := Option.map_eq_some_iff.1 h
  exact Zipper.plug_ctx_of_traverse_descend w (FileTree.Zipper.zip τ) z
    (FileTree.Zipper.zip_canonical hτ) rfl hz

theorem Focus.map_snd_resolve_descend [Ord Γ] (w : List Γ) (f : FileTree.Focus Γ) :
    (f.resolve (Path.descend w)).map Prod.snd = follow f w := by
  cases f with
  | tree τ =>
      simpa [FileTree.Focus.resolve, FileTree.resolve, FileTree.Zipper.zip, Option.map_map,
        Function.comp_def] using Zipper.map_focus_traverse_descend w (FileTree.Zipper.zip τ)
  | abst =>
      rcases w with _ | ⟨a, w⟩
      · rfl
      · cases hp : Path.descend (a :: w) with
        | nil =>
            have := congrArg Path.depth hp
            simp [Path.depth] at this
            omega
        | app => rfl

theorem word_eq_of_resolve_descend [Ord Γ] {w : List Γ} {base : FileTree Γ}
    {C : FileTree.Ctx Γ} {f : FileTree.Focus Γ}
    (hres : FileTree.resolve (Path.descend w) base = some (C, f)) : FileTree.Ctx.word C = w :=
  Path.descend_injective <| (FileTree.Ctx.path_eq_descend_word C).symm.trans <|
    (FileTree.path_eq_norm_of_resolve hres).trans (Path.norm_descend w)

end FileTree

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel BigConnectives
open WE (GroundWord)
open FileTree.Focus (follow shapeFollow entriesFollow follow_append follow_plug_word_append
  map_snd_resolve_descend)
open FileTree (missing_of_resolve_descend plug_eq_tree_of_resolve_descend
  word_eq_of_resolve_descend)

variable {Γ : Type} {V : TWE.Vars}

theorem mem_dom_iff_follow_child_tree [Ord Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    (focus : FileTree.Focus Γ) (path : List Γ)
    (entries : FileTree.Entries Γ (FileTree Γ))
    (hfollow : follow focus path = some (.tree (.dirc entries))) (name : Γ) :
    name ∈ entries.dom ↔
      ∃ tree, follow focus (path ++ [name]) = some (.tree tree) := by
  rw [follow_append, hfollow, FileTree.Entries.mem_dom_iff,
    FileTree.Entries.mem_iff_lookup_isSome]
  cases h : entries.lookup name <;> simp [follow, h]

theorem shapeFollow_leaf_not_strictPrefix [Ord Γ]
    (f : FileTree.Focus Γ) (path query : List Γ) (h k : TWE.Shape)
    (hpath : shapeFollow f path = some h) (hleaf : h ≠ .dirc)
    (hquery : shapeFollow f query = some k) :
    ¬(path <+: query ∧ path ≠ query) := by
  rintro ⟨⟨_ | ⟨a, s⟩, rfl⟩, hne⟩
  · simp at hne
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hpath
  rw [shapeFollow, follow_append, hg] at hquery
  rcases g with (_ | _) | _ <;> simp_all [follow, FileTree.Focus.shape]

theorem shapeFollow_plug_of_not_prefix [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (C : FileTree.Ctx Γ) (oldFocus newFocus : FileTree.Focus Γ) (query : List Γ)
    (hC : FileTree.Ctx.Missing C) (houtside : ¬FileTree.Ctx.word C <+: query) :
    shapeFollow (C.plug newFocus) query = shapeFollow (C.plug oldFocus) query := by
  induction C generalizing query with
  | hole => exact absurd List.nil_prefix houtside
  | node δ a C ih =>
      obtain ⟨ha, hC⟩ := hC
      rcases query with _ | ⟨b, suffix⟩
      · simp [shapeFollow, FileTree.Ctx.plug_node, follow, FileTree.Focus.shape]
      by_cases hab : a = b
      · subst b
        have ih := ih suffix hC fun hp ↦ houtside (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        simp only [FileTree.Ctx.plug_node, shapeFollow, follow, FileTree.Entries.getElem?_eq_lookup,
          FileTree.Entries.lookup_plug_self δ a _ ha]
        cases hnew : FileTree.Ctx.plug C newFocus <;> cases hold : FileTree.Ctx.plug C oldFocus <;>
          simp_all [shapeFollow]
      · simp [shapeFollow, FileTree.Ctx.plug_node, follow,
          FileTree.Entries.lookup_plug_ne δ a b _ hab]

theorem follow_eq_none_iff [Ord Γ] (f : FileTree.Focus Γ) (w : List Γ) :
    follow f w = none ↔ ∃ p a s g, w = p ++ a :: s ∧ follow f p = some g ∧ Leaf g := by
  induction w generalizing f with
  | nil => simp [follow]
  | cons a w ih =>
      rcases f with (_ | δ) | _
      · exact ⟨fun _ ↦ ⟨[], a, w, _, rfl, rfl, by simp [Leaf, FileTree.Focus.shape]⟩,
          fun _ ↦ rfl⟩
      · obtain ⟨g₀, hg₀⟩ : ∃ g₀, ∀ p, follow (.tree (.dirc δ)) (a :: p) = follow g₀ p :=
          ⟨(δ[a]?).elim .abst .tree, fun p ↦ by cases h : δ[a]? <;> simp [follow, h]⟩
        rw [hg₀, ih]
        constructor
        · rintro ⟨p, b, s, g, rfl, hp, hg⟩
          exact ⟨a :: p, b, s, g, rfl, (hg₀ p).trans hp, hg⟩
        · rintro ⟨_ | ⟨c, p⟩, b, s, g, hw, hp, hg⟩
          · cases hp
            simp [Leaf, FileTree.Focus.shape] at hg
          · obtain ⟨rfl, rfl⟩ := List.cons.inj hw
            exact ⟨p, b, s, g, rfl, (hg₀ p).symm.trans hp, hg⟩
      · exact ⟨fun _ ↦ ⟨[], a, w, _, rfl, rfl, by simp [Leaf, FileTree.Focus.shape]⟩,
          fun _ ↦ rfl⟩

theorem toWE_sourceSkeleton [Ord Γ] (target : WE.Model Γ (ToWE.Vars V)) :
    (sourceSkeleton target).toWE = target := by
  apply congrArg₂ WE.Model.mk <;> funext x <;> rcases x with _ | _ <;> rfl

theorem evalPath_toTWE [Ord Γ] (m : WordModel Γ V) {p : TWE.Path Γ V}
    (hp : p.hasLinearConstants) :
    m.toTWE.evalPath p = Path.descend (WordModel.evalPath m p) := by
  induction p with
  | init b =>
      rcases b with _ | _ | _ | (_ | _) | _ <;>
        first | rfl | simp [TWE.Path.hasLinearConstants] at hp
  | join p q ihp ihq =>
      simp only [TWE.Path.hasLinearConstants, Bool.and_eq_true] at hp
      simp only [TWE.Model.evalPath, WordModel.evalPath, ihp hp.1, ihq hp.2]
      exact (Path.descend_append _ _).symm
  | norm p ih =>
      simp only [TWE.Model.evalPath, WordModel.evalPath, ih hp]
      exact Path.norm_descend _
  | _ => rfl

theorem sat_toTWE_pathEq_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) {p q : TWE.Path Γ V}
    (hp : p.hasLinearConstants) (hq : q.hasLinearConstants) :
    m.toTWE ⊨ (p ≐ q : TWE.Formula Γ V) ↔ m.evalPath p = m.evalPath q := by
  change m.toTWE.evalPath p = m.toTWE.evalPath q ↔ _
  rw [evalPath_toTWE m hp, evalPath_toTWE m hq, Path.descend_injective.eq_iff]

open scoped WE in
theorem sat_toWE_toWord_eq_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) {p q : TWE.Path Γ V}
    (hp : p.hasLinearConstants) (hq : q.hasLinearConstants) :
    m.toWE ⊨ (p.toWord ≐ q.toWord : WordFormula Γ V) ↔ m.toTWE ⊨ (p ≐ q : TWE.Formula Γ V) := by
  change m.toWE.evalWord p.toWord = m.toWE.evalWord q.toWord ↔ _
  rw [Path.evalWord_toWord, Path.evalWord_toWord]
  exact (sat_toTWE_pathEq_iff m hp hq).symm

theorem sat_toWE_toWord_ne_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) {p q : TWE.Path Γ V}
    (hp : p.hasLinearConstants) (hq : q.hasLinearConstants) :
    m.toWE ⊨ (p.toWord ≠̇ q.toWord : WordFormula Γ V) ↔ ¬m.toTWE ⊨ (p ≐ q : TWE.Formula Γ V) :=
  not_congr (sat_toWE_toWord_eq_iff m hp hq)

section PrefixMacros

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem not_prefix_of_sat_notPrefixFormula (M : WE.Model Γ (ToWE.Vars V)) (U : TWE.Free V)
    (p q : Word Γ V)
    (h : M ⊨ ((p ⋠ q).run U).1) : ¬M.evalWord p <+: M.evalWord q := by
  rw [GroundWord.not_prefix_iff_exists]
  let A : V.Name := Fresh.fresh U.name
  let B : V.Name := Fresh.fresh (insert A U.name)
  let K : V.Path := Fresh.fresh U.path
  let J : V.Path := Fresh.fresh (insert K U.path)
  let K' : V.Path := Fresh.fresh (insert J (insert K U.path))
  change
    (M.evalWord p = M.evalWord q ++ [M.σLetter (.inl A)] ++ M.σWord (.inl K)) ∨
      (((M.evalWord p = M.σWord (.inl J) ++ [M.σLetter (.inl A)] ++ M.σWord (.inl K)) ∧
        M.evalWord q = M.σWord (.inl J) ++ [M.σLetter (.inl B)] ++ M.σWord (.inl K')) ∧
        ¬[M.σLetter (.inl A)] = [M.σLetter (.inl B)]) at h
  rcases h with h | ⟨⟨hp, hq⟩, hab⟩
  · exact Or.inl ⟨_, _, by simpa using h⟩
  · exact Or.inr ⟨_, _, _, _, _, by simpa using hp, by simpa using hq,
      fun heq ↦ hab (congrArg ([·]) heq)⟩

theorem sat_pathIncomparableFormula_iff (M : WE.Model Γ (ToWE.Vars V)) (P Q : Word Γ V)
    (U : TWE.Free V) :
    M ⊨ ((P ∥ Q).run U).1 ↔
      M ⊨ ((P ⋠ Q).run U).1 ∧ M ⊨ ((Q ⋠ P).run ((P ⋠ Q).run U).2).1 := Iff.rfl

variable [Ord Γ] (m : WordModel Γ V) {U W : TWE.Free V} {p q : Word Γ V}

theorem exists_sat_notPrefixFormula_iff (hUW : U ⊆ W) (hp : Word.free p ⊆ U)
    (hq : Word.free q ⊆ U) :
    (∃ m', m ≡[U] m' ∧ m'.toWE ⊨ ((p ⋠ q).run W).1) ↔
      ¬m.toWE.evalWord p <+: m.toWE.evalWord q := by
  constructor
  · rintro ⟨m', hm, h⟩
    simpa only [evalWord_congr hm hp, evalWord_congr hm hq] using
      not_prefix_of_sat_notPrefixFormula _ _ p q h
  let A : V.Name := Fresh.fresh W.name
  let B : V.Name := Fresh.fresh (insert A W.name)
  let K : V.Path := Fresh.fresh W.path
  let J : V.Path := Fresh.fresh (insert K W.path)
  let K' : V.Path := Fresh.fresh (insert J (insert K W.path))
  have hA : A ∉ U.name := Fresh.fresh_notMem_of_subset hUW.1
  have hB : B ∉ U.name := Fresh.fresh_notMem_of_subset (hUW.1.trans (Finset.subset_insert _ _))
  have hK : K ∉ U.path := Fresh.fresh_notMem_of_subset hUW.2.2.1
  have hJ : J ∉ U.path :=
    Fresh.fresh_notMem_of_subset (hUW.2.2.1.trans (Finset.subset_insert _ _))
  have hK' : K' ∉ U.path := Fresh.fresh_notMem_of_subset
    (hUW.2.2.1.trans ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
  have hAB : A ≠ B := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
  have hKJ : K ≠ J := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
  have hKK' : K ≠ K' := Fresh.ne_fresh_of_mem (by simp)
  have hJK' : J ≠ K' := Fresh.ne_fresh_of_mem (Finset.mem_insert_self _ _)
  intro h
  obtain ⟨a, b, i, r, r', h⟩ : ∃ a b i r r',
      m.toWE.evalWord p = m.toWE.evalWord q ++ [a] ++ r ∨
        (m.toWE.evalWord p = i ++ [a] ++ r ∧ m.toWE.evalWord q = i ++ [b] ++ r') ∧
          ¬[a] = [b] := by
    rcases (GroundWord.not_prefix_iff_exists _ _).1 h with
      ⟨a, r, h⟩ | ⟨i, a, r, b, r', hp', hq', hab⟩
    · exact ⟨a, a, [], r, [], .inl (by simpa using h)⟩
    · exact ⟨a, b, i, r, r', .inr ⟨⟨by simpa using hp', by simpa using hq'⟩, by simpa using hab⟩⟩
  let m' := ((((m.setName A a).setName B b).setPath K r).setPath J i).setPath K' r'
  have hm : m ≡[U] m' :=
    ((((WordModel.congr_setName hA).trans (WordModel.congr_setName hB)).trans
      (WordModel.congr_setPath hK)).trans (WordModel.congr_setPath hJ)).trans
      (WordModel.congr_setPath hK')
  refine ⟨m', hm, ?_⟩
  change
    (m'.toWE.evalWord p = m'.toWE.evalWord q ++ [m'.σName A] ++ m'.σPath K) ∨
      (((m'.toWE.evalWord p = m'.σPath J ++ [m'.σName A] ++ m'.σPath K) ∧
        m'.toWE.evalWord q = m'.σPath J ++ [m'.σName B] ++ m'.σPath K') ∧
        ¬[m'.σName A] = [m'.σName B])
  rw [← evalWord_congr hm hp, ← evalWord_congr hm hq]
  have hσA : m'.σName A = a := by simp [m', hAB]
  have hσB : m'.σName B = b := by simp [m']
  have hσK : m'.σPath K = r := by simp [m', hKJ, hKK']
  have hσJ : m'.σPath J = i := by simp [m', hJK']
  have hσK' : m'.σPath K' = r' := by simp [m']
  rw [hσA, hσB, hσK, hσJ, hσK']
  exact h

theorem exists_sat_notStrictPrefixFormula_iff (hUW : U ⊆ W) (hp : Word.free p ⊆ U)
    (hq : Word.free q ⊆ U) :
    (∃ m', m ≡[U] m' ∧ m'.toWE ⊨ ((p ⊀ q).run W).1) ↔
      ¬(m.toWE.evalWord p <+: m.toWE.evalWord q ∧ m.toWE.evalWord p ≠ m.toWE.evalWord q) := by
  rw [not_and_or, not_not, ← exists_sat_notPrefixFormula_iff m hUW hp hq]
  constructor
  · rintro ⟨m', hm, h | h⟩
    · exact .inr ((evalWord_congr hm hp).trans (h.trans (evalWord_congr hm hq).symm))
    · exact .inl ⟨m', hm, h⟩
  · rintro (⟨m', hm, h⟩ | h)
    exacts [⟨m', hm, .inr h⟩, ⟨m, .refl m U, .inl h⟩]

theorem exists_sat_pathIncomparableFormula_iff (hUW : U ⊆ W) (hp : Word.free p ⊆ U)
    (hq : Word.free q ⊆ U) :
    (∃ m', m ≡[U] m' ∧ m'.toWE ⊨ ((p ∥ q).run W).1) ↔
      ¬m.toWE.evalWord p <+: m.toWE.evalWord q ∧ ¬m.toWE.evalWord q <+: m.toWE.evalWord p := by
  have hW := subset_notPrefixFormula p q W
  simp only [sat_pathIncomparableFormula_iff]
  constructor
  · rintro ⟨m', hm, h₁, h₂⟩
    exact ⟨(exists_sat_notPrefixFormula_iff m hUW hp hq).1 ⟨m', hm, h₁⟩,
      (exists_sat_notPrefixFormula_iff m (Free.Subset.trans hUW hW) hq hp).1 ⟨m', hm, h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨m₁, hm₁, h₁⟩ := (exists_sat_notPrefixFormula_iff m hUW hp hq).2 h₁
    rw [evalWord_congr hm₁ hq, evalWord_congr hm₁ hp] at h₂
    have hU' := Free.Subset.trans hUW hW
    obtain ⟨m₂, hm₂, h₂⟩ := (exists_sat_notPrefixFormula_iff m₁ (Free.Subset.refl _)
      (Free.Subset.trans hq hU') (Free.Subset.trans hp hU')).2 h₂
    exact ⟨m₂, hm₁.trans (hm₂.mono hU'),
      (sat_wordFormula_congr hm₂ (free_notPrefixFormula_subset (Free.Subset.trans hp hUW)
        (Free.Subset.trans hq hUW))).1 h₁, h₂⟩

end PrefixMacros

theorem evalTree_canonical [Ord Γ] [Std.TransOrd Γ] (m : WordModel Γ V) {T : TWE.Tree V}
    {f : FileTree.Focus Γ} (h : m.toTWE.evalTree T = some f) : f.Canonical := by
  induction T generalizing f with
  | var x => cases h; exact (m.θ x).2
  | file => cases h; exact FileTree.Canonical.file
  | emptyDirc =>
      cases h
      exact FileTree.Canonical.dirc FileTree.Entries.canonical_empty fun p hp ↦ by
        simp [FileTree.Entries.empty, EmptyCollection.emptyCollection] at hp
  | abst => cases h; trivial
  | select T l ih =>
      obtain ⟨g, C, hT, hres⟩ := (TWE.Model.evalTree_select_eq_some_iff m.toTWE T l f).1 h
      rcases g with τ | _
      · exact FileTree.resolve_canonical (ih hT) hres
      · cases hloc : Path.descend (m.σLoc l) <;> simp [FileTree.Focus.resolve, hloc] at hres
        exact hres.2 ▸ trivial
  | update T l T' ih ih' =>
      rcases f with updated | _
      · obtain ⟨base, C, _, newFocus, hT, hres, hT', hfill⟩ :=
          (TWE.Model.evalTree_update_eq_some_iff m.toTWE T T' l updated).1 h
        exact FileTree.Ctx.fill_canonical (FileTree.resolve_ctx_canonical (ih hT) hres) (ih' hT')
          hfill
      · exact absurd h (TWE.Model.evalTree_update_ne_abst m.toTWE T T' l)

theorem sat_treeShape_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (h : TWE.Shape) :
    m.toTWE ⊨ (T ∶ h : TWE.Formula Γ V) ↔ ∃ f, m.toTWE.evalTree T = some f ∧ f.shape = h := by
  change (match m.toTWE.evalTree T with | some f => f.shape = h | none => False) ↔ _
  cases m.toTWE.evalTree T <;> simp

theorem sat_treeShape_or_iff_exists_evalTree [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V)
    (τ : TWE.Tree V) :
    (m.toTWE ⊨ (τ ∶ .absent : TWE.Formula Γ V) ∨ m.toTWE ⊨ (τ ∶ .file : TWE.Formula Γ V) ∨
        m.toTWE ⊨ (τ ∶ .dirc : TWE.Formula Γ V)) ↔
      ∃ f, m.toTWE.evalTree τ = some f := by
  simp only [sat_treeShape_iff]
  cases m.toTWE.evalTree τ with
  | none => simp
  | some f => cases h : f.shape <;> simp [h]

theorem observesShape_iff [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V) (query : List Γ)
    (h : TWE.Shape) :
    ObservesShape m T query h ↔ (m.toTWE.evalTree T).bind (shapeFollow · query) = some h := by
  simp [ObservesShape, Option.bind_eq_some_iff]

theorem observesShape_nil_iff [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V) (h : TWE.Shape) :
    ObservesShape m T ([] : List Γ) h ↔ ∃ f, m.toTWE.evalTree T = some f ∧ f.shape = h := by
  simp [ObservesShape, shapeFollow, follow]

theorem observesShape_nil_iff_sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (h : TWE.Shape) :
    ObservesShape m T ([] : List Γ) h ↔ m.toTWE ⊨ (T ∶ h : TWE.Formula Γ V) :=
  (observesShape_nil_iff m T h).trans (sat_treeShape_iff m T h).symm

theorem not_exists_observesShape_nil_or_absent_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V)
    (T : TWE.Tree V) :
    (¬∃ h, ObservesShape m T ([] : List Γ) h) ∨ ObservesShape m T ([] : List Γ) .absent ↔
      ¬(m.toTWE ⊨ (T ∶ .file : TWE.Formula Γ V) ∨ m.toTWE ⊨ (T ∶ .dirc : TWE.Formula Γ V)) := by
  simp only [observesShape_nil_iff_sat, sat_treeShape_iff]
  cases m.toTWE.evalTree T with
  | none => simp
  | some f => cases h : f.shape <;> simp [h]

theorem exists_observesShape_iff [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (query : List Γ) :
    (∃ h, ObservesShape m T query h) ↔
      ObservesShape m T query .absent ∨ ObservesShape m T query .file ∨
        ObservesShape m T query .dirc := by
  constructor
  · rintro ⟨_ | _ | _, h⟩ <;> simp [h]
  · rintro (h | h | h) <;> exact ⟨_, h⟩

theorem not_observesShape_iff [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V) (query : List Γ)
    (h : TWE.Shape) :
    ¬ObservesShape m T query h ↔
      (¬∃ h', ObservesShape m T query h') ∨
        ∃ h' ∈ [TWE.Shape.absent, .file, .dirc].filter (· ≠ h), ObservesShape m T query h' := by
  simp only [observesShape_iff]
  cases (m.toTWE.evalTree T).bind (shapeFollow · query) with
  | none => simp
  | some h' => cases h <;> cases h' <;> simp

theorem entriesValue_eq_some_iff_observesEntries [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V)
    (T : TWE.Tree V) (value : Finset Γ) :
    WordModel.entriesValue m T = some value ↔ ObservesEntries m T List.nil value := by
  simp only [WordModel.entriesValue, ObservesEntries, TWE.Model.evalNameSet, entriesFollow, follow]
  rcases m.toTWE.evalTree T with _ | (_ | _) | _ <;> simp [FileTree.Focus.entryNames, eq_comm]

theorem exists_observesEntries [Ord Γ] [DecidableEq Γ] {m : WordModel Γ V} {T : TWE.Tree V}
    {w : List Γ} (hw : ∃ h, ObservesShape m T w h) : ∃ N, ObservesEntries m T w N := by
  obtain ⟨h, f, hf, hshape⟩ := hw
  obtain ⟨g, hg, -⟩ := Option.map_eq_some_iff.1 hshape
  exact ⟨FileTree.Focus.entryNames g, f, hf, by simp [entriesFollow, hg]⟩

theorem observesEntries_iff [Ord Γ] [DecidableEq Γ] [Std.LawfulEqOrd Γ] (m : WordModel Γ V)
    (T : TWE.Tree V) (w : List Γ) (N : Finset Γ) :
    ObservesEntries m T w N ↔ (∃ h, ObservesShape m T w h) ∧
      ∀ a, a ∈ N ↔ ObservesShape m T (w ++ [a]) .file ∨ ObservesShape m T (w ++ [a]) .dirc := by
  simp only [ObservesEntries, ObservesShape, entriesFollow, shapeFollow, follow_append]
  rcases m.toTWE.evalTree T with _ | f
  · simp
  rcases hfw : follow f w with _ | ((_ | δ) | _)
  · simp [hfw]
  · simp [hfw, FileTree.Focus.entryNames, follow, FileTree.Focus.shape,
      Finset.eq_empty_iff_forall_notMem, eq_comm]
  · simp only [hfw, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
      FileTree.Focus.entryNames, Finset.ext_iff]
    rw [and_iff_right ⟨_, rfl⟩]
    refine forall_congr' fun a ↦ ?_
    rw [FileTree.Entries.mem_dom_iff, FileTree.Entries.mem_iff_lookup_isSome]
    rcases h : δ.lookup a with _ | (_ | _) <;> simp [follow, h, FileTree.Focus.shape]
  · simp [hfw, FileTree.Focus.entryNames, follow, FileTree.Focus.shape,
      Finset.eq_empty_iff_forall_notMem, eq_comm]

theorem sat_treeShape_select_iff [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V)
    (l : V.Loc) (h : TWE.Shape) :
    m.toTWE ⊨ ((T[l]) ∶ h : TWE.Formula Γ V) ↔ ObservesShape m T (m.σLoc l) h := by
  simp only [sat_treeShape_iff, TWE.Model.evalTree_select_eq_some_iff, ObservesShape, shapeFollow,
    ← map_snd_resolve_descend, Option.map_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨f, ⟨g, C, hg, hres⟩, rfl⟩
    exact ⟨g, hg, (C, f), hres, rfl⟩
  · rintro ⟨g, hg, ⟨C, f⟩, hres, rfl⟩
    exact ⟨f, ⟨g, C, hg, hres⟩, rfl⟩

theorem shapeFollow_fill_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    {base updated : FileTree Γ} {oldFocus newFocus : FileTree.Focus Γ} {C : FileTree.Ctx Γ}
    {updatePath query : List Γ} {h : TWE.Shape} (hbase : base.Canonical)
    (hres : FileTree.resolve (Path.descend updatePath) base = some (C, oldFocus))
    (hfill : C.fill newFocus = some updated) :
    shapeFollow (.tree updated) query = some h ↔
      (∃ suffix, query = updatePath ++ suffix ∧ shapeFollow newFocus suffix = some h) ∨
      (¬updatePath <+: query ∧ shapeFollow (.tree base) query = some h) := by
  have hmissing := missing_of_resolve_descend hres
  have hpath := word_eq_of_resolve_descend hres
  have hnew := FileTree.Ctx.plug_eq_tree_of_fill hfill
  by_cases hp : updatePath <+: query
  · obtain ⟨suffix, rfl⟩ := hp
    have hins := follow_plug_word_append C newFocus suffix hmissing
    rw [hpath, hnew] at hins
    simp [shapeFollow, hins]
  · have hout := shapeFollow_plug_of_not_prefix C oldFocus newFocus query hmissing (hpath ▸ hp)
    rw [hnew, plug_eq_tree_of_resolve_descend hbase hres] at hout
    rw [hout]
    exact ⟨fun h ↦ Or.inr ⟨hp, h⟩, by
      rintro (⟨s, rfl, -⟩ | ⟨-, h⟩)
      exacts [absurd (List.prefix_append _ _) hp, h]⟩

theorem observesShape_update_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (m : WordModel Γ V) {T replacement : TWE.Tree V} {updateLoc : V.Loc}
    (hdefined : (m.toTWE.evalTree (.update T updateLoc replacement)).isSome)
    (query : List Γ) (h : TWE.Shape) :
    ObservesShape m (.update T updateLoc replacement) query h ↔
      (∃ suffix, query = m.σLoc updateLoc ++ suffix ∧ ObservesShape m replacement suffix h) ∨
        (¬m.σLoc updateLoc <+: query ∧ ObservesShape m T query h) := by
  obtain ⟨updated, hupdate⟩ := (TWE.Model.isSome_evalTree_update_iff _ _ _ _).1 hdefined
  obtain ⟨base, C, oldFocus, newFocus, hbase, hres, hreplacement, hfill⟩ :=
    (TWE.Model.evalTree_update_eq_some_iff m.toTWE T replacement updateLoc updated).1 hupdate
  simp only [ObservesShape, hupdate, hbase, hreplacement, Option.some.injEq, exists_eq_left']
  exact shapeFollow_fill_iff (evalTree_canonical m hbase) hres hfill

theorem exists_evalTree_update_iff [Ord Γ] (m : WordModel Γ V) (τ replacement : TWE.Tree V)
    (l : V.Loc) :
    (∃ updated, m.toTWE.evalTree (.update τ l replacement) = some (.tree updated)) ↔
      (m.σLoc l = [] ∧
        ∃ base newTree,
          m.toTWE.evalTree τ = some (.tree base) ∧
          m.toTWE.evalTree replacement = some (.tree newTree)) ∨
      (m.σLoc l ≠ [] ∧
        (∃ f, m.toTWE.evalTree (.select τ l) = some f) ∧
        ∃ newFocus, m.toTWE.evalTree replacement = some newFocus) := by
  by_cases hw : m.σLoc l = []
  · have hroot (base : FileTree Γ) :
        FileTree.resolve (m.toTWE.σLoc l) base = some (.hole, .tree base) := by
      simp [WordModel.toTWE, hw, Path.descend, FileTree.resolve,
        FileTree.Zipper.zip, FileTree.Zipper.traverse, FileTree.Frames.ctx]
    simp only [hw, ne_eq, not_true_eq_false, false_and, or_false, true_and]
    constructor
    · rintro ⟨updated, hupdate⟩
      obtain ⟨base, C, oldFocus, _ | _, hbase, hres, hreplacement, hfill⟩ :=
        (TWE.Model.evalTree_update_eq_some_iff m.toTWE τ replacement l updated).1 hupdate
      · exact ⟨base, _, hbase, hreplacement⟩
      · rw [hroot] at hres
        cases hres
        simp [FileTree.Ctx.fill] at hfill
    · rintro ⟨base, newTree, hbase, hreplacement⟩
      exact ⟨newTree, (TWE.Model.evalTree_update_eq_some_iff m.toTWE τ replacement l newTree).2
        ⟨base, .hole, .tree base, .tree newTree, hbase, hroot base, hreplacement, rfl⟩⟩
  · simp only [hw, false_and, false_or, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro ⟨updated, hupdate⟩
      obtain ⟨base, C, oldFocus, newFocus, hbase, hres, hreplacement, -⟩ :=
        (TWE.Model.evalTree_update_eq_some_iff m.toTWE τ replacement l updated).1 hupdate
      exact ⟨⟨oldFocus, (TWE.Model.evalTree_select_eq_some_iff m.toTWE τ l oldFocus).2
        ⟨.tree base, C, hbase, hres⟩⟩, newFocus, hreplacement⟩
    · rintro ⟨⟨oldFocus, hselect⟩, newFocus, hreplacement⟩
      obtain ⟨base | _, C, hbase, hres⟩ :=
        (TWE.Model.evalTree_select_eq_some_iff m.toTWE τ l oldFocus).1 hselect
      · rcases C with _ | ⟨δ, a, C⟩
        · exact absurd (word_eq_of_resolve_descend hres).symm hw
        · obtain ⟨updated, hfill⟩ : ∃ τ, (FileTree.Ctx.node δ a C).fill newFocus = some τ := by
            simp only [FileTree.Ctx.fill]
            split <;> exact ⟨_, rfl⟩
          exact ⟨updated, (TWE.Model.evalTree_update_eq_some_iff m.toTWE τ replacement l updated).2
            ⟨base, _, oldFocus, newFocus, hbase, hres, hreplacement, hfill⟩⟩
      · have hfollow := map_snd_resolve_descend (m.σLoc l) FileTree.Focus.abst
        change Option.map Prod.snd (FileTree.Focus.resolve (m.toTWE.σLoc l) .abst) = _ at hfollow
        rw [hres] at hfollow
        cases hσ : m.σLoc l
        · exact absurd hσ hw
        · simp [follow, hσ] at hfollow

section LinearFragment

theorem wf_toTWE_and_linearAt_toTWE [Ord Γ] (M : WordModel Γ V) {φ : TWE.Formula Γ V}
    (hφ : φ.hasLinearConstants) : M.toTWE.WF ∧ M.toTWE.LinearAt φ := by
  refine ⟨⟨fun _ ↦ Path.linear_descend _, fun x ↦ (M.θ x).2⟩, fun p hp ↦ ?_⟩
  rw [evalPath_toTWE M (TWE.Formula.hasLinearConstants_of_mem_paths hφ hp)]
  exact Path.linear_descend _

section LinearModelOf

variable [Ord Γ] {m : TWE.Model Γ V} (hwf : m.WF) (a : Γ)

theorem evalTree_toTWE_toWordModel (T : TWE.Tree V) :
    (m.toWordModel hwf a).toTWE.evalTree T = m.evalTree T := by
  have hloc : ∀ l, (m.toWordModel hwf a).toTWE.σLoc l = m.σLoc l := fun l ↦
    Path.descend_names_of_linear (hwf.1 l)
  induction T with
  | select T l ih => simp only [TWE.Model.evalTree, ih, hloc]
  | update T l T' ih ih' => simp only [TWE.Model.evalTree, ih, ih', hloc]
  | _ => rfl

theorem evalNameSet_toTWE_toWordModel [DecidableEq Γ] (S : TWE.Set Γ V) :
    (m.toWordModel hwf a).toTWE.evalNameSet S = m.evalNameSet S := by
  induction S with
  | insert b S ih =>
      simp only [TWE.Model.evalNameSet, ih]
      cases b <;> rfl
  | entries T => simp only [TWE.Model.evalNameSet, evalTree_toTWE_toWordModel hwf]
  | _ => rfl

theorem evalPath_toTWE_toWordModel {p : TWE.Path Γ V}
    (h : ∀ q ∈ p.subterms, (m.evalPath q).Linear) :
    (m.toWordModel hwf a).toTWE.evalPath p = m.evalPath p := by
  induction p with
  | init c =>
      have := h _ (TWE.Path.mem_subterms_self _)
      cases c with
      | var x =>
          simp only [TWE.Model.evalPath, TWE.Model.evalComponent, WordModel.toTWE,
            TWE.Model.toWordModel] at this ⊢
          cases hx : m.σComp x with
          | name b => rfl
          | _ => simp [hx, Accordion.Path.init, Accordion.Path.Linear] at this
      | name b => cases b <;> rfl
      | _ => simp [TWE.Model.evalPath, TWE.Model.evalComponent, Accordion.Path.init,
          Accordion.Path.Linear] at this
  | join p q ihp ihq =>
      simp only [TWE.Model.evalPath]
      rw [ihp fun r hr ↦ h r (by simp [TWE.Path.subterms, hr]),
        ihq fun r hr ↦ h r (by simp [TWE.Path.subterms, hr])]
  | loc l => exact Path.descend_names_of_linear (hwf.1 l)
  | var x => exact Path.descend_names_of_linear (h _ (TWE.Path.mem_subterms_self _))
  | norm p ih =>
      simp only [TWE.Model.evalPath]
      rw [ih fun r hr ↦ h r (by simp [TWE.Path.subterms, hr])]
  | nil => rfl

theorem sat_toTWE_toWordModel [DecidableEq Γ] {φ : TWE.Formula Γ V} (h : m.LinearAt φ) :
    (m.toWordModel hwf a).toTWE ⊨ φ ↔ m ⊨ φ := by
  induction φ with
  | top | bot => exact Iff.rfl
  | conj φ ψ ihφ ihψ =>
      exact and_congr (ihφ fun q hq ↦ h q (by simp [TWE.Formula.paths, hq]))
        (ihψ fun q hq ↦ h q (by simp [TWE.Formula.paths, hq]))
  | disj φ ψ ihφ ihψ =>
      exact or_congr (ihφ fun q hq ↦ h q (by simp [TWE.Formula.paths, hq]))
        (ihψ fun q hq ↦ h q (by simp [TWE.Formula.paths, hq]))
  | neg φ ih => exact not_congr (ih h)
  | atom b =>
      have hpath {p : TWE.Path Γ V} (hp : p ∈ TWE.Formula.paths (.atom b)) :
          (m.toWordModel hwf a).toTWE.evalPath p = m.evalPath p :=
        evalPath_toTWE_toWordModel hwf a fun q hq ↦
          h q (TWE.Formula.mem_paths_of_mem_subterms hp hq)
      change TWE.Model.satAtom _ b ↔ TWE.Model.satAtom _ b
      cases b with
      | pathEq P Q =>
          simp only [TWE.Model.satAtom,
            hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self]),
            hpath (p := Q) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])]
      | pathIsLin P =>
          simp only [TWE.Model.satAtom,
            hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self])]
      | treeWalk P T l =>
          simp only [TWE.Model.satAtom,
            hpath (p := P) (by simp [TWE.Formula.paths, TWE.Path.mem_subterms_self]),
            evalTree_toTWE_toWordModel hwf]
          rw [show (m.toWordModel hwf a).toTWE.σLoc l = m.σLoc l from
            Path.descend_names_of_linear (hwf.1 l)]
      | treeShape T sh => simp only [TWE.Model.satAtom, evalTree_toTWE_toWordModel hwf]
      | setEq S S' => simp only [TWE.Model.satAtom, evalNameSet_toTWE_toWordModel hwf]
      | setMem A S =>
          simp only [TWE.Model.satAtom, evalNameSet_toTWE_toWordModel hwf]
          cases A <;> rfl

end LinearModelOf

theorem SAT_iff_exists_sat_toTWE [Ord Γ] [DecidableEq Γ] [Nonempty Γ] {φ : TWE.Formula Γ V}
    (hφ : φ.hasLinearConstants) :
    TWE.Linear.Formula.SAT φ ↔ ∃ M : WordModel Γ V, M.toTWE ⊨ φ := by
  constructor
  · rintro ⟨⟨m, hwf, hlin⟩, hsat⟩
    obtain ⟨a⟩ := ‹Nonempty Γ›
    exact ⟨m.toWordModel hwf a, (sat_toTWE_toWordModel hwf a hlin).2 hsat⟩
  · rintro ⟨M, hsat⟩
    exact ⟨⟨M.toTWE, wf_toTWE_and_linearAt_toTWE M hφ⟩, hsat⟩

end LinearFragment

end ToWE

end Linear

end TWE

end Accordion

end
