module

public import Accordion.FileTree.Zipper.Properties
public import Accordion.WE.LenEq.ToNorm.Properties
public import Accordion.WE.LenEq.ToWalk.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula
open ToWalk Accordion.Path

variable {Γ : Type} {V : WE.Vars}

namespace ToWalk

variable [IsEmpty V.Letter]

theorem evalPath_liftWord (m : Walk.Model Γ (Vars Γ V)) (u : WE.Word Γ V) :
    m.evalPath (liftWord u) = (normModel m).evalPath (ToNorm.liftWord u) := by
  induction u with
  | letterVar x => exact isEmptyElim x
  | concat u v ihu ihv => exact congrArg₂ (· ++ ·) ihu ihv
  | _ => rfl

theorem evalPath_invertWord (m : Walk.Model Γ (Vars Γ V)) (v : WE.Word Γ V) :
    m.evalPath (invertWord v) = (normModel m).evalPath (ToNorm.invertWord v) := by
  induction v with
  | letterVar x => exact isEmptyElim x
  | concat u v ihu ihv => exact congrArg₂ (· ++ ·) ihu ihv
  | _ => rfl

theorem evalPath_liftWord_join_invertWord (m : Walk.Model Γ (Vars Γ V)) (u v : WE.Word Γ V) :
    m.evalPath (liftWord u ++ invertWord v) =
      (normModel m).evalPath (ToNorm.liftWord u ++ ToNorm.invertWord v) :=
  congrArg₂ (· ++ ·) (evalPath_liftWord m u) (evalPath_invertWord m v)

variable [Ord Γ]

theorem linear_evalPath_liftWord {m : Walk.Model Γ (Vars Γ V)} (hm : m.WF) (u : WE.Word Γ V) :
    (m.evalPath (liftWord u)).Linear := by
  induction u with
  | letterVar x => exact isEmptyElim x
  | var x => exact hm.1 _
  | concat u v ihu ihv => exact join_linear ihu ihv
  | _ => trivial

theorem eq_norm_of_sat_treeWalk {V : Walk.Vars} {m : Walk.Model Γ V} {p : Walk.Path Γ V}
    {τ : V.Tree} {l : V.Loc} (h : Sat.sat m (Walk.Atom.treeWalk p τ l)) :
    m.σLoc l = (m.evalPath p).norm := by
  change Walk.Model.satAtom m _ at h
  simp only [Walk.Model.satAtom] at h
  split at h
  · split at h
    · next hr => exact h ▸ FileTree.path_eq_norm_of_resolve hr
    · exact h.elim
  · exact h.elim

theorem sat_atRoot_iff_of_sat_walks [Inhabited Γ] {m : Walk.Model Γ (Vars Γ V)}
    {u v : WE.Word Γ V} (h : m ⊨ walks u v) :
    m ⊨ atRoot u v ↔ (m.evalPath (liftWord u ++ invertWord v)).IsBalanced := by
  change m.σLoc (Loc.endpoint u v) = (ε : Accordion.Path Γ) ∧
    ¬ m.σLoc (Loc.prefixed u v) = (ε : Accordion.Path Γ) ↔ _
  rw [eq_norm_of_sat_treeWalk h.1, eq_norm_of_sat_treeWalk h.2]
  exact (isBalanced_iff_norm_eq_nil default _).symm

theorem sat_guards [Inhabited Γ] {m : Walk.Model Γ (Vars Γ V)} {φ : Formula Γ V}
    (hg : m ⊨ guards φ) :
    normModel m ⊨ ToNorm.inverseGuards (Γ := Γ) (Formula.vars φ) ∧
      ∀ u v, Atom.lenEq u v ∈ φ.atoms → m ⊨ walks u v := by
  rw [guards, Accordion.Formula.sat_bigConj] at hg
  have hw : ∀ w ∈ (.letter default : WE.Word Γ V) :: (Formula.vars φ).map .var,
      (m.evalPath (liftWord w ++ invertWord w)).IsBalanced := fun w hw =>
    have h := hg _ (List.mem_append_left _ (List.mem_map_of_mem hw))
    (sat_atRoot_iff_of_sat_walks h.1).1 h.2
  exact ⟨(ToNorm.sat_inverseGuards_iff _ _).2 ⟨hw _ List.mem_cons_self,
      fun x hx => hw _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hx))⟩,
    fun u v hA => hg _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨_, hA, rfl⟩))⟩

theorem sat_treeWalk_of_resolve {V : Walk.Vars} {m : Walk.Model Γ V} {p : Walk.Path Γ V}
    {τ : V.Tree} {l : V.Loc} {T : FileTree Γ} {q : Accordion.Path Γ} {C : FileTree.Ctx Γ}
    {f : FileTree.Focus Γ} (hθ : m.θ τ = .tree T) (hp : m.evalPath p = q)
    (hr : FileTree.resolve q T = some (C, f)) (hl : m.σLoc l = q.norm) :
    Sat.sat m (Walk.Atom.treeWalk p τ l) := by
  subst hp
  change Walk.Model.satAtom m _
  simp only [Walk.Model.satAtom, hθ, hr]
  exact (FileTree.path_eq_norm_of_resolve hr).trans hl.symm

theorem mkdir_canonical [Std.TransOrd Γ] (w : GroundWord Γ)
    {δ : FileTree.Entries Γ (FileTree Γ)} (hδ : (FileTree.dirc δ).Canonical) :
    (FileTree.dirc (mkdir w δ)).Canonical := by
  induction w generalizing δ with
  | nil => exact hδ
  | cons a w ih =>
      refine FileTree.canonical_insert_dirc hδ (ih ?_)
      split
      · next h => exact FileTree.canonical_of_lookup hδ h
      · exact .dirc FileTree.Entries.canonical_empty nofun

theorem mkdirs_canonical [Std.TransOrd Γ] (ws : List (GroundWord Γ)) :
    (FileTree.dirc (mkdirs ws)).Canonical := by
  induction ws with
  | nil => exact .dirc FileTree.Entries.canonical_empty nofun
  | cons w ws ih => exact mkdir_canonical w ih

theorem hasDir_mkdir_self [Std.LawfulEqOrd Γ] (w : GroundWord Γ)
    (δ : FileTree.Entries Γ (FileTree Γ)) : HasDir w (mkdir w δ) := by
  induction w generalizing δ with
  | nil => trivial
  | cons a w ih => exact ⟨_, FileTree.Entries.lookup_insert_self δ a _, ih _⟩

theorem hasDir_mkdir [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] (u w : GroundWord Γ)
    {δ : FileTree.Entries Γ (FileTree Γ)} (hu : HasDir u δ) : HasDir u (mkdir w δ) := by
  induction u generalizing w δ with
  | nil => trivial
  | cons b u ih =>
      obtain ⟨δb, hb, hub⟩ := hu
      cases w with
      | nil => exact ⟨δb, hb, hub⟩
      | cons a w =>
          by_cases hab : a = b
          · subst hab
            exact ⟨_, FileTree.Entries.lookup_insert_self δ a _, ih _ (by rw [hb]; exact hub)⟩
          · exact ⟨δb, (FileTree.Entries.lookup_insert_ne δ a b _ fun h =>
              hab (Std.LawfulEqCmp.eq_of_compare h)).trans hb, hub⟩

theorem hasDir_mkdirs [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] {w : GroundWord Γ}
    {ws : List (GroundWord Γ)} (hw : w ∈ ws) : HasDir w (mkdirs ws) := by
  induction ws with
  | nil => cases hw
  | cons v ws ih =>
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hasDir_mkdir_self _ _
      · exact hasDir_mkdir w v (ih hw)

theorem traverse_descend_of_hasDir {w : GroundWord Γ} {δ : FileTree.Entries Γ (FileTree Γ)}
    (hw : HasDir w δ) (frames : FileTree.Frames Γ) :
    ∃ frames' δ', FileTree.Zipper.traverse (descend w) ⟨frames, .tree (.dirc δ)⟩ =
      some ⟨frames', .tree (.dirc δ')⟩ := by
  induction w generalizing δ frames with
  | nil => exact ⟨frames, δ, rfl⟩
  | cons a w ih =>
      obtain ⟨δa, ha, hwa⟩ := hw
      obtain ⟨frames', δ', hz⟩ := ih hwa (frames.push (δ.erase a) a)
      refine ⟨frames', δ', ?_⟩
      rw [descend, FileTree.Zipper.traverse_join]
      simpa [Path.init, FileTree.Zipper.traverse, FileTree.Zipper.move, FileTree.Zipper.down,
        show δ.lookup a = _ from ha] using hz

theorem traverse_parents (n : Nat) (frames : FileTree.Frames Γ)
    (δ : FileTree.Entries Γ (FileTree Γ)) :
    ∃ frames' δ', FileTree.Zipper.traverse (ToNorm.parents n) ⟨frames, .tree (.dirc δ)⟩ =
      some ⟨frames', .tree (.dirc δ')⟩ := by
  induction n with
  | zero => exact ⟨frames, δ, rfl⟩
  | succ n ih =>
      obtain ⟨frames', δ', hz⟩ := ih
      cases frames' <;>
        simp [ToNorm.parents, FileTree.Zipper.traverse, hz, FileTree.Zipper.move,
          FileTree.Zipper.up]

theorem resolve_descend_join_parents {w : GroundWord Γ} {δ : FileTree.Entries Γ (FileTree Γ)}
    (hw : HasDir w δ) (n : Nat) :
    ∃ C δ', FileTree.resolve (descend w ++ ToNorm.parents n) (.dirc δ) =
      some (C, .tree (.dirc δ')) := by
  obtain ⟨frames, δ₁, hz⟩ := traverse_descend_of_hasDir hw .nil
  obtain ⟨frames', δ', hz'⟩ := traverse_parents n frames δ₁
  refine ⟨frames'.ctx, δ', ?_⟩
  rw [FileTree.resolve, FileTree.Zipper.traverse_join, FileTree.Zipper.zip, hz]
  exact congrArg _ hz'

theorem evalPath_liftWord_toWalk [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V)
    (u : WE.Word Γ V) :
    (Model.toWalk φ m).evalPath (liftWord u) = descend (m.evalWord u) := by
  induction u with
  | letterVar x => exact isEmptyElim x
  | concat u v ihu ihv =>
      exact (congrArg₂ (· ++ ·) ihu ihv).trans (descend_append _ _).symm
  | _ => rfl

theorem evalPath_invertWord_toWalk [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V)
    (v : WE.Word Γ V) :
    (Model.toWalk φ m).evalPath (invertWord v) =
      ToNorm.parents (List.length (m.evalWord v)) := by
  induction v with
  | letterVar x => exact isEmptyElim x
  | concat u v ihu ihv =>
      exact (congrArg₂ (· ++ ·) ihu ihv).trans
        ((ToNorm.parents_add _ _).symm.trans (congrArg _ List.length_append.symm))
  | _ => rfl

theorem evalPath_liftWord_join_invertWord_toWalk [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V)
    (u v : WE.Word Γ V) :
    (Model.toWalk φ m).evalPath (liftWord u ++ invertWord v) =
      descend (m.evalWord u) ++ ToNorm.parents (List.length (m.evalWord v)) :=
  congrArg₂ (· ++ ·) (evalPath_liftWord_toWalk φ m u) (evalPath_invertWord_toWalk φ m v)

theorem sat_toWalk_walks [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [Inhabited Γ] (φ : Formula Γ V)
    (m : Model Γ V) (u v : WE.Word Γ V) (hu : m.evalWord u ∈ walkedWords φ m) :
    Model.toWalk φ m ⊨ walks u v := by
  have e₁ := evalPath_liftWord_join_invertWord_toWalk φ m u v
  have e₂ : (Model.toWalk φ m).evalPath (.letter default ++ (liftWord u ++ invertWord v)) =
      descend (default :: m.evalWord u) ++ ToNorm.parents (List.length (m.evalWord v)) :=
    (congrArg (((default : Γ) : Accordion.Path Γ) ++ ·) e₁).trans (join_assoc _ _ _)
  obtain ⟨C₁, δ₁, h₁⟩ := resolve_descend_join_parents (n := List.length (m.evalWord v))
    (hasDir_mkdirs (ws := dirWords φ m) (List.mem_append_left _ hu))
  obtain ⟨C₂, δ₂, h₂⟩ := resolve_descend_join_parents (n := List.length (m.evalWord v))
    (hasDir_mkdirs (ws := dirWords φ m) (List.mem_append_right _ (List.mem_map_of_mem hu)))
  exact ⟨sat_treeWalk_of_resolve rfl e₁ h₁ rfl, sat_treeWalk_of_resolve rfl e₂ h₂ rfl⟩

end ToWalk

variable [Ord Γ]

theorem wf_toWalk [Std.TransOrd Γ] [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    (Model.toWalk φ m).WF :=
  ⟨fun l => by cases l <;> first | exact linear_descend _ | exact linear_norm _,
    fun _ => mkdirs_canonical _⟩

variable [IsEmpty V.Letter]

theorem sat_toWalk_guards [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [Inhabited Γ] (φ : Formula Γ V)
    (m : Model Γ V) : Model.toWalk φ m ⊨ guards φ := by
  rw [guards, Accordion.Formula.sat_bigConj]
  intro ψ hψ
  rcases List.mem_append.1 hψ with hψ | hψ
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hψ
    have h := sat_toWalk_walks φ m w w (List.mem_append_left _ (by
      simpa [Model.evalWord] using List.mem_map_of_mem (f := m.evalWord) hw))
    refine ⟨h, (sat_atRoot_iff_of_sat_walks h).2 ?_⟩
    rw [evalPath_liftWord_join_invertWord_toWalk]
    exact ToNorm.isBalanced_descend_join_parents _
  · obtain ⟨⟨u, v⟩ | ⟨u, v⟩, hA, hAψ⟩ := List.mem_filterMap.1 hψ <;> cases hAψ
    exact sat_toWalk_walks φ m u v
      (List.mem_append_right _ (List.mem_filterMap.2 ⟨.lenEq u v, hA, rfl⟩))

theorem sat_toWalk_wordEq [Inhabited Γ] {m : Walk.Model Γ (ToWalk.Vars Γ V)} {φ : Formula Γ V}
    (hm : m.WF) (hg : m ⊨ guards φ) (u v : WE.Word Γ V)
    (hu : ∀ x ∈ u.vars, x ∈ Formula.vars φ) (hv : ∀ x ∈ v.vars, x ∈ Formula.vars φ) :
    m ⊨ Atom.toWalk (.wordEq u v) ↔
      (ToNorm.sourceModel (normModel m)).evalWord u =
        (ToNorm.sourceModel (normModel m)).evalWord v := by
  rw [← sat_toNorm_wordEq (sat_guards hg).1 u v hu hv]
  change m.evalPath (liftWord u) = m.evalPath (liftWord v) ↔
    ((normModel m).evalPath (ToNorm.liftWord u)).norm =
      ((normModel m).evalPath (ToNorm.liftWord v)).norm
  rw [← evalPath_liftWord, ← evalPath_liftWord,
    norm_eq_self_of_linear (linear_evalPath_liftWord hm u),
    norm_eq_self_of_linear (linear_evalPath_liftWord hm v)]

theorem sat_toWalk_lenEq [Inhabited Γ] {m : Walk.Model Γ (ToWalk.Vars Γ V)} {φ : Formula Γ V}
    (hg : m ⊨ guards φ) (u v : WE.Word Γ V) (hA : Atom.lenEq u v ∈ φ.atoms)
    (hu : ∀ x ∈ u.vars, x ∈ Formula.vars φ) (hv : ∀ x ∈ v.vars, x ∈ Formula.vars φ) :
    m ⊨ Atom.toWalk (.lenEq u v) ↔
      GroundWord.length ((ToNorm.sourceModel (normModel m)).evalWord u) =
        GroundWord.length ((ToNorm.sourceModel (normModel m)).evalWord v) := by
  rw [← sat_toNorm_lenEq (sat_guards hg).1 u v hu hv]
  refine (sat_atRoot_iff_of_sat_walks ((sat_guards hg).2 u v hA)).trans ?_
  rw [evalPath_liftWord_join_invertWord]
  exact (Norm.Model.sat_pathBalanced _ _).symm

theorem sat_toWalk_atom [Inhabited Γ] {m : Walk.Model Γ (ToWalk.Vars Γ V)} {φ : Formula Γ V}
    (hm : m.WF) (hg : m ⊨ guards φ) (A : Atom Γ V) (hA : A ∈ φ.atoms) :
    m ⊨ Atom.toWalk A ↔ Sat.sat (ToNorm.sourceModel (normModel m)) A := by
  have hvars : ∀ x ∈ A.vars, x ∈ Formula.vars φ := fun x hx => List.mem_flatMap.2 ⟨A, hA, hx⟩
  cases A <;> obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hvars
  · exact sat_toWalk_wordEq hm hg _ _ hu hv
  · exact sat_toWalk_lenEq hg _ _ hA hu hv

theorem Formula.guards_bind_equisat [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [Inhabited Γ] (φ : Formula Γ V) :
    Walk.Formula.SAT (guards φ ⋏ φ.bind Atom.toWalk) ↔ Formula.SAT φ := by
  constructor
  · rintro ⟨m, hm, hg, hφ⟩
    exact ⟨_, (Accordion.Formula.sat_bind _ m _ φ (sat_toWalk_atom hm hg)).1 hφ⟩
  · rintro ⟨m, hφ⟩
    have hm := wf_toWalk φ m
    have hg := sat_toWalk_guards φ m
    exact ⟨_, hm, hg, (Accordion.Formula.sat_bind _ _ _ φ (sat_toWalk_atom hm hg)).2
      ((ToNorm.sourceModel_toNorm m).symm ▸ hφ)⟩

end LenEq

end WE

end Accordion

end
