module

public import Accordion.WE.LenEq.ToWalk.Properties
public import Accordion.WE.LenEq.ToShapeReg.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula ShapeReg
open ToShapeReg Accordion.Path

variable {Γ : Type} {V : WE.Vars}

namespace ToShapeReg

variable [IsEmpty V.Letter]

open ToNorm (parents)

theorem encWord_append (u v : GroundWord Γ) : encWord (u ++ v) = encWord u ++ encWord v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [encWord, ih]

theorem length_encWord (w : GroundWord Γ) : List.length (encWord w) = 2 * List.length w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [encWord, ih]; omega

theorem filterMap_letter?_encWord (w : GroundWord Γ) :
    (encWord w).filterMap Alphabet.letter? = w := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (a :: ·) ih

section

variable {Δ : Type}

theorem components_parents (n : Nat) :
    (parents n : Accordion.Path Δ).components = List.replicate n ‥ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [parents, components, ih, List.replicate_succ']

theorem norm_join_parents_of_norm_eq_nil {p : Accordion.Path Δ}
    (h : p.norm = (ε : Accordion.Path Δ)) (n : Nat) :
    (p ++ parents n).norm = (ε : Accordion.Path Δ) := by
  induction n with
  | zero => exact h
  | succ n ih => exact congrArg Path.dir ih

end

theorem norm_descend_join_parents_length (w : GroundWord (Alphabet Γ)) :
    (descend w ++ parents (List.length w)).norm = (ε : Accordion.Path (Alphabet Γ)) :=
  ((isBalanced_iff_norm_eq_nil .sep _).1 (ToNorm.isBalanced_descend_join_parents w)).1

theorem norm_descend_append_join_parents (u v : GroundWord (Alphabet Γ)) :
    (descend (u ++ v) ++ parents (List.length v)).norm = descend u := by
  rw [descend_append, ← join_assoc,
    norm_join_of_isAnchored_right _ (ToNorm.isBalanced_descend_join_parents v).1,
    norm_descend_join_parents_length, norm_eq_self_of_linear (linear_descend u)]
  rfl

theorem norm_descend_encWord_join_parents_of_le {w : GroundWord Γ} {n : Nat}
    (h : List.length w ≤ n) : (descend (encWord w) ++ parents (2 * n)).norm =
      (ε : Accordion.Path (Alphabet Γ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.mul_add, ← length_encWord, ToNorm.parents_add, join_assoc]
  exact norm_join_parents_of_norm_eq_nil (norm_descend_join_parents_length _) _

theorem norm_descend_encWord_join_parents_of_lt {w : GroundWord Γ} {n : Nat}
    (h : n < List.length w) :
    ∃ q, (descend (encWord w) ++ parents (2 * n)).norm = .app q (.name .sep) := by
  obtain ⟨w₀, c, hw₀⟩ := (List.eq_nil_or_concat' (w.take (List.length w - n))).resolve_left
    (List.ne_nil_of_length_pos (by rw [List.length_take]; omega))
  have hw : encWord w =
      ((encWord w₀ ++ [.letter c]) ++ [.sep]) ++ encWord (w.drop (List.length w - n)) := by
    conv_lhs => rw [← List.take_append_drop (List.length w - n) w, hw₀]
    simp [encWord_append, encWord]
  rw [hw, show 2 * n = List.length (encWord (w.drop (List.length w - n))) by
    rw [length_encWord, List.length_drop]; omega, norm_descend_append_join_parents]
  exact ⟨_, descend_append _ [Alphabet.sep]⟩

theorem descend_encWord_cons_join (a : Γ) (w : GroundWord Γ) (q : Accordion.Path (Alphabet Γ)) :
    ((.letter a : Alphabet Γ) : Accordion.Path (Alphabet Γ)) ++
        (((.sep : Alphabet Γ) : Accordion.Path (Alphabet Γ)) ++ (descend (encWord w) ++ q)) =
      descend (encWord (a :: w)) ++ q := by
  rw [encWord, descend, descend, join_assoc, join_assoc, join_assoc]

theorem matches_sourceLang (w : GroundWord Γ) :
    (sourceLang : ShapeReg.Regex (Alphabet Γ)).Matches (descend (encWord w)).components := by
  rw [components_descend]
  refine ⟨w.map fun c => [.name (.letter c), .name .sep], ?_, List.forall_mem_map.2 fun c _ =>
    ⟨[.name (.letter c)], [.name .sep], rfl, ⟨.letter c, by simp, rfl⟩, rfl⟩⟩
  induction w with
  | nil => rfl
  | cons a w ih => simp [encWord, ih]

theorem matches_inverseLang (n : Nat) :
    (inverseLang : ShapeReg.Regex (Alphabet Γ)).Matches
      (parents (2 * n) : Accordion.Path (Alphabet Γ)).components := by
  rw [components_parents, Nat.mul_comm]
  exact ⟨List.replicate n [‥, ‥], (List.flatten_replicate_replicate (m := 2)).symm,
    fun u hu => ⟨[‥], [‥], List.eq_of_mem_replicate hu, rfl, rfl⟩⟩

theorem eq_descend_encWord_of_matches {p : Accordion.Path (Alphabet Γ)}
    (h : (sourceLang : ShapeReg.Regex (Alphabet Γ)).Matches p.components) :
    p = descend (encWord ((names p).filterMap Alphabet.letter?)) := by
  obtain ⟨ws, hws, hall⟩ := h
  obtain ⟨w, hw⟩ : ∃ w : GroundWord Γ, ws.flatten = (encWord w).map Component.name := by
    clear hws
    induction ws with
    | nil => exact ⟨[], rfl⟩
    | cons u ws ih =>
        obtain ⟨⟨u₁, u₂, rfl, ⟨c, hc, rfl⟩, rfl⟩, hws⟩ := List.forall_mem_cons.1 hall
        obtain ⟨w, hw⟩ := ih hws
        cases c with
        | sep => simp at hc
        | letter c => exact ⟨c :: w, by simp [encWord, hw]⟩
  obtain rfl : p = descend (encWord w) := eq_of_components_eq (by rw [hws, hw, components_descend])
  rw [names_descend, filterMap_letter?_encWord]

theorem eq_parents_of_matches {p : Accordion.Path (Alphabet Γ)}
    (h : (inverseLang : ShapeReg.Regex (Alphabet Γ)).Matches p.components) :
    ∃ n, p = parents (2 * n) := by
  obtain ⟨ws, hws, hall⟩ := h
  have hrep : ws = List.replicate ws.length (List.replicate 2 ‥) :=
    List.eq_replicate_iff.2 ⟨rfl, fun u hu => by
      obtain ⟨_, _, rfl, rfl, rfl⟩ := hall u hu
      rfl⟩
  exact ⟨ws.length, eq_of_components_eq (by
    rw [hws, hrep, List.flatten_replicate_replicate, List.length_replicate,
      components_parents, Nat.mul_comm])⟩

theorem evalPath_liftWord {m : ShapeReg.Model (Alphabet Γ) (Vars V.Word)} {s : Model Γ V}
    (u : WE.Word Γ V)
    (hsrc : ∀ x ∈ u.vars, m.σPath (.source x) = descend (encWord (s.σWord x))) :
    m.evalPath (liftWord u) = descend (encWord (s.evalWord u)) := by
  induction u with
  | letterVar x => exact isEmptyElim x
  | var x => exact hsrc x List.mem_cons_self
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hsrc
      change m.evalPath (liftWord u) ++ m.evalPath (liftWord v) =
        descend (encWord (s.evalWord u ++ s.evalWord v))
      rw [ihu hu, ihv hv, encWord_append, descend_append]
  | _ => rfl

theorem evalPath_invertWord {m : ShapeReg.Model (Alphabet Γ) (Vars V.Word)} {s : Model Γ V}
    (hup : m.σPath .up = parents 1) (v : WE.Word Γ V)
    (hinv : ∀ x ∈ v.vars, m.σPath (.inverse x) = parents (2 * List.length (s.σWord x))) :
    m.evalPath (invertWord v) = parents (2 * List.length (s.evalWord v)) := by
  induction v with
  | empty => rfl
  | letter a => exact congrArg₂ (· ++ ·) hup hup
  | letterVar x => exact isEmptyElim x
  | var x => exact hinv x List.mem_cons_self
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hinv
      change m.evalPath (invertWord u) ++ m.evalPath (invertWord v) =
        parents (2 * List.length (s.evalWord u ++ s.evalWord v))
      rw [ihu hu, ihv hv, List.length_append, Nat.mul_add, ToNorm.parents_add]

variable [Ord Γ]

theorem resolve_of_sat_treeWalkShape {V : ShapeReg.Vars} {m : ShapeReg.Model (Alphabet Γ) V}
    {p : ShapeReg.Path (Alphabet Γ) V} {τ : V.Tree} {h : TWE.Shape}
    (hs : Sat.sat m (ShapeReg.Atom.treeWalkShape p τ h)) :
    ∃ T C f, m.θ τ = .tree T ∧ FileTree.resolve (m.evalPath p) T = some (C, f) ∧ f.shape = h := by
  change ShapeReg.Model.satAtom m _ at hs
  simp only [ShapeReg.Model.satAtom] at hs
  split at hs
  · next hθ =>
      split at hs
      · next hr => exact ⟨_, _, _, hθ, hr, hs⟩
      · exact hs.elim
  · exact hs.elim

theorem sat_treeWalkShape_iff_of_resolve {V : ShapeReg.Vars} {m : ShapeReg.Model (Alphabet Γ) V}
    {p : ShapeReg.Path (Alphabet Γ) V} {τ : V.Tree} {h : TWE.Shape} {T : FileTree (Alphabet Γ)}
    {q : Accordion.Path (Alphabet Γ)} {r : FileTree.Ctx (Alphabet Γ) × FileTree.Focus (Alphabet Γ)}
    (hθ : m.θ τ = .tree T) (hp : m.evalPath p = q) (hr : FileTree.resolve q T = some r) :
    Sat.sat m (ShapeReg.Atom.treeWalkShape p τ h) ↔ r.2.shape = h := by
  subst hp
  change ShapeReg.Model.satAtom m _ ↔ _
  simp only [ShapeReg.Model.satAtom, hθ, hr]

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem shape_resolve_probe {τ : FileTree (Alphabet Γ)} (hτ : τ.Canonical)
    {r₀ : FileTree.Ctx (Alphabet Γ) × FileTree.Focus (Alphabet Γ)}
    (h₀ : FileTree.resolve ((.sep : Alphabet Γ) : Accordion.Path (Alphabet Γ)) τ = some r₀)
    (hs₀ : r₀.2.shape = .file) {p : Accordion.Path (Alphabet Γ)} {w : GroundWord Γ} {n : Nat}
    (hp : p = descend (encWord w) ++ parents (2 * n))
    {r : FileTree.Ctx (Alphabet Γ) × FileTree.Focus (Alphabet Γ)}
    (h : FileTree.resolve p τ = some r) (hs : r.2.shape = .dirc) :
    ∃ r', FileTree.resolve (.app (.app p ‥) (.name .sep)) τ = some r' ∧
      r'.2.shape = if List.length w ≤ n then .file else .dirc := by
  subst hp
  obtain ⟨C, (_ | δ) | _⟩ := r <;> try cases hs
  obtain ⟨r', hr'⟩ := FileTree.exists_resolve_app_parent_app_name h .sep
  refine ⟨r', hr', ?_⟩
  split
  · next hle =>
      rw [FileTree.resolve_eq_of_norm_eq hτ hr' h₀ (by
        simp only [Path.norm, Path.init, norm_descend_encWord_join_parents_of_le hle, Path.dir])]
      exact hs₀
  · next hle =>
      obtain ⟨q, hq⟩ := norm_descend_encWord_join_parents_of_lt (Nat.lt_of_not_le hle)
      rw [FileTree.resolve_eq_of_norm_eq hτ hr' h (by simp only [Path.norm, hq, Path.dir])]
      rfl

theorem sat_balanced_iff_of_sat_walks [Inhabited Γ] {m : ShapeReg.Model (Alphabet Γ) (Vars V.Word)}
    (hm : m.WF)
    (h₀ : m ⊨ (() ⊢ .letter .sep ⇝ .file : ShapeReg.Formula (Alphabet Γ) (Vars V.Word)))
    (hup : m.σPath .up = parents 1) {u v : WE.Word Γ V} {w : GroundWord Γ} {n : Nat}
    (hu : m.evalPath (liftWord u) = descend (encWord w))
    (hv : m.evalPath (invertWord v) = parents (2 * n)) (hw : m ⊨ walks u v) :
    m ⊨ balanced u v ↔ List.length w = n := by
  obtain ⟨T, C₀, f₀, hθ, hr₀, hs₀⟩ := resolve_of_sat_treeWalkShape h₀
  obtain ⟨T₁, C₁, f₁, hθ₁, hr₁, hs₁⟩ := resolve_of_sat_treeWalkShape hw.1
  obtain ⟨T₂, C₂, f₂, hθ₂, hr₂, hs₂⟩ := resolve_of_sat_treeWalkShape hw.2
  obtain rfl : T₁ = T := FileTree.Focus.tree.inj (hθ₁.symm.trans hθ)
  obtain rfl : T₂ = T₁ := FileTree.Focus.tree.inj (hθ₂.symm.trans hθ)
  have hτ : T₂.Canonical := by
    have := hm ()
    rwa [hθ] at this
  have e₁ : m.evalPath (site u v) = descend (encWord w) ++ parents (2 * n) :=
    congrArg₂ (· ++ ·) hu hv
  have e₂ : m.evalPath (prefixed (site u v)) =
      descend (encWord (default :: w)) ++ parents (2 * n) :=
    (congrArg (fun q => _ ++ (_ ++ q)) e₁).trans (descend_encWord_cons_join default w _)
  have hprobe : ∀ p, m.evalPath (probe p) = .app (.app (m.evalPath p) ‥) (.name .sep) :=
    fun p => congrArg (fun q => m.evalPath p ++ (q ++ _)) hup
  obtain ⟨r₁, hr₁, hs₁⟩ := shape_resolve_probe hτ hr₀ hs₀ e₁ hr₁ hs₁
  obtain ⟨r₂, hr₂, hs₂⟩ := shape_resolve_probe hτ hr₀ hs₀ e₂ hr₂ hs₂
  change Sat.sat m (ShapeReg.Atom.treeWalkShape _ _ _) ∧
    Sat.sat m (ShapeReg.Atom.treeWalkShape _ _ _) ↔ _
  rw [sat_treeWalkShape_iff_of_resolve hθ (hprobe (site u v)) hr₁,
    sat_treeWalkShape_iff_of_resolve hθ (hprobe (prefixed (site u v))) hr₂, hs₁, hs₂,
    List.length_cons]
  split <;> split <;> simp <;> omega

theorem sat_guards [Inhabited Γ] {m : ShapeReg.Model (Alphabet Γ) (Vars V.Word)} {φ : Formula Γ V}
    (hm : m.WF) (hg : m ⊨ guards φ) :
    m ⊨ (() ⊢ .letter .sep ⇝ .file : ShapeReg.Formula (Alphabet Γ) (Vars V.Word)) ∧
      m.σPath .up = parents 1 ∧
      (∀ x ∈ Formula.vars φ,
        m.σPath (.source x) = descend (encWord ((sourceModel m).σWord x))) ∧
      (∀ x ∈ Formula.vars φ,
        m.σPath (.inverse x) = parents (2 * List.length ((sourceModel m).σWord x))) ∧
      ∀ u v, Atom.lenEq u v ∈ φ.atoms → m ⊨ walks u v := by
  rw [guards, Accordion.Formula.sat_bigConj] at hg
  have h₀ : m ⊨ (() ⊢ .letter .sep ⇝ .file : ShapeReg.Formula (Alphabet Γ) (Vars V.Word)) :=
    hg _ (by simp)
  have hup : m.σPath .up = parents 1 :=
    eq_of_components_eq (hg (.var PathVar.up ∈̇ .parent) (by simp))
  have hx := fun x (hx : x ∈ Formula.vars φ) =>
    hg _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx)))
  have hsrc : ∀ x ∈ Formula.vars φ,
      m.σPath (.source x) = descend (encWord ((sourceModel m).σWord x)) :=
    fun x h => eq_descend_encWord_of_matches (hx x h).1.1.1
  refine ⟨h₀, hup, hsrc, fun x h => ?_, fun u v hA =>
    hg _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨_, hA, rfl⟩))⟩
  obtain ⟨⟨⟨-, hinv⟩, hw⟩, hb⟩ := hx x h
  obtain ⟨n, hn⟩ := eq_parents_of_matches hinv
  obtain rfl := (sat_balanced_iff_of_sat_walks hm h₀ hup (u := .var x) (v := .var x)
    (hsrc x h) hn hw).1 hb
  exact hn

omit [Std.TransOrd Γ] in
theorem resolve_sep_touch (δ : FileTree.Entries (Alphabet Γ) (FileTree (Alphabet Γ))) :
    ∃ C, FileTree.resolve ((.sep : Alphabet Γ) : Accordion.Path (Alphabet Γ)) (.dirc (touch δ)) =
      some (C, .tree .file) := by
  simp [touch, FileTree.resolve, FileTree.Zipper.traverse, Path.init, FileTree.Zipper.zip,
    FileTree.Zipper.move, FileTree.Zipper.down, FileTree.Entries.lookup_insert_self]

theorem hasDir_touch (w : GroundWord Γ) {δ : FileTree.Entries (Alphabet Γ) (FileTree (Alphabet Γ))}
    (h : ToWalk.HasDir (encWord w) δ) : ToWalk.HasDir (encWord w) (touch δ) := by
  cases w with
  | nil => trivial
  | cons c w =>
      obtain ⟨δc, hc, hrest⟩ := h
      exact ⟨δc, (FileTree.Entries.lookup_insert_ne δ .sep (.letter c) _ (fun h => by
        cases Std.LawfulEqCmp.eq_of_compare h)).trans hc, hrest⟩

theorem sat_toShapeReg_walks [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) (u v : WE.Word Γ V)
    (hu : m.evalWord u ∈ walkedWords φ m) : Model.toShapeReg φ m ⊨ walks u v := by
  have e₁ : (Model.toShapeReg φ m).evalPath (site u v) =
      descend (encWord (m.evalWord u)) ++ parents (2 * List.length (m.evalWord v)) :=
    congrArg₂ (· ++ ·) (evalPath_liftWord (s := m) u fun _ _ => rfl)
      (evalPath_invertWord (s := m) rfl v fun _ _ => rfl)
  have e₂ : (Model.toShapeReg φ m).evalPath (prefixed (site u v)) =
      descend (encWord (default :: m.evalWord u)) ++ parents (2 * List.length (m.evalWord v)) :=
    (congrArg (fun q => _ ++ (_ ++ q)) e₁).trans (descend_encWord_cons_join default _ _)
  obtain ⟨C₁, δ₁, h₁⟩ := ToWalk.resolve_descend_join_parents
    (n := 2 * List.length (m.evalWord v)) (hasDir_touch _ (ToWalk.hasDir_mkdirs
      (ws := dirWords φ m) (List.mem_append_left _ (List.mem_map_of_mem hu))))
  obtain ⟨C₂, δ₂, h₂⟩ := ToWalk.resolve_descend_join_parents
    (n := 2 * List.length (m.evalWord v)) (hasDir_touch (default :: m.evalWord u)
      (ToWalk.hasDir_mkdirs (ws := dirWords φ m)
        (List.mem_append_right _ (List.mem_map_of_mem hu))))
  exact ⟨(sat_treeWalkShape_iff_of_resolve rfl e₁ h₁).2 rfl,
    (sat_treeWalkShape_iff_of_resolve rfl e₂ h₂).2 rfl⟩

end ToShapeReg

variable [Ord Γ]

theorem wf_toShapeReg [Std.TransOrd Γ] [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    (Model.toShapeReg φ m).WF :=
  fun _ => FileTree.canonical_insert_dirc (ToWalk.mkdirs_canonical _) .file

variable [IsEmpty V.Letter]

theorem sourceModel_toShapeReg [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    sourceModel (Model.toShapeReg φ m) = m :=
  congrArg₂ Model.mk (funext fun x => isEmptyElim x) (funext fun _ =>
    (congrArg (List.filterMap Alphabet.letter?) (names_descend _)).trans
      (filterMap_letter?_encWord _))

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem sat_toShapeReg_guards [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    Model.toShapeReg φ m ⊨ guards φ := by
  have h₀ : Model.toShapeReg φ m ⊨
      (() ⊢ .letter .sep ⇝ .file : ShapeReg.Formula (Alphabet Γ) (ToShapeReg.Vars V.Word)) := by
    obtain ⟨C, hC⟩ := resolve_sep_touch (ToWalk.mkdirs (dirWords φ m))
    exact (sat_treeWalkShape_iff_of_resolve (m := Model.toShapeReg φ m) (p := .letter .sep)
      rfl rfl hC).2 rfl
  rw [guards, Accordion.Formula.sat_bigConj]
  intro ψ hψ
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filterMap] at hψ
  obtain ((rfl | rfl) | ⟨x, hx, rfl⟩) | ⟨⟨u, v⟩ | ⟨u, v⟩, hA, hAψ⟩ := hψ
  · exact h₀
  · exact (rfl : (ToNorm.parents 1 : Accordion.Path (Alphabet Γ)).components = [‥])
  · have hw := sat_toShapeReg_walks φ m (.var x) (.var x)
      (List.mem_append_left _ (List.mem_map_of_mem hx))
    exact ⟨⟨⟨matches_sourceLang _, matches_inverseLang _⟩, hw⟩,
      (sat_balanced_iff_of_sat_walks (wf_toShapeReg φ m) h₀ rfl (u := .var x) (v := .var x)
        (w := m.σWord x) rfl rfl hw).2 rfl⟩
  · cases hAψ
  · cases hAψ
    exact sat_toShapeReg_walks φ m u v
      (List.mem_append_right _ (List.mem_filterMap.2 ⟨.lenEq u v, hA, rfl⟩))

theorem sat_toShapeReg_wordEq [Inhabited Γ]
    {m : ShapeReg.Model (Alphabet Γ) (ToShapeReg.Vars V.Word)}
    {φ : Formula Γ V} (hm : m.WF) (hg : m ⊨ guards φ) (u v : WE.Word Γ V)
    (hu : ∀ x ∈ u.vars, x ∈ Formula.vars φ) (hv : ∀ x ∈ v.vars, x ∈ Formula.vars φ) :
    m ⊨ Atom.toShapeReg (.wordEq u v) ↔
      (sourceModel m).evalWord u = (sourceModel m).evalWord v := by
  obtain ⟨-, -, hsrc, -⟩ := sat_guards hm hg
  change m.evalPath (liftWord u) = m.evalPath (liftWord v) ↔ _
  rw [evalPath_liftWord u fun x hx => hsrc x (hu x hx),
    evalPath_liftWord v fun x hx => hsrc x (hv x hx)]
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simpa only [names_descend, filterMap_letter?_encWord] using
    congrArg (fun p => (names p).filterMap Alphabet.letter?) h

theorem sat_toShapeReg_lenEq [Inhabited Γ]
    {m : ShapeReg.Model (Alphabet Γ) (ToShapeReg.Vars V.Word)}
    {φ : Formula Γ V} (hm : m.WF) (hg : m ⊨ guards φ) (u v : WE.Word Γ V)
    (hA : Atom.lenEq u v ∈ φ.atoms)
    (hu : ∀ x ∈ u.vars, x ∈ Formula.vars φ) (hv : ∀ x ∈ v.vars, x ∈ Formula.vars φ) :
    m ⊨ Atom.toShapeReg (.lenEq u v) ↔
      GroundWord.length ((sourceModel m).evalWord u) =
        GroundWord.length ((sourceModel m).evalWord v) := by
  obtain ⟨h₀, hup, hsrc, hinv, hw⟩ := sat_guards hm hg
  exact sat_balanced_iff_of_sat_walks hm h₀ hup (evalPath_liftWord u fun x hx => hsrc x (hu x hx))
    (evalPath_invertWord hup v fun x hx => hinv x (hv x hx)) (hw u v hA)

theorem sat_toShapeReg_atom [Inhabited Γ]
    {m : ShapeReg.Model (Alphabet Γ) (ToShapeReg.Vars V.Word)}
    {φ : Formula Γ V} (hm : m.WF) (hg : m ⊨ guards φ) (A : Atom Γ V) (hA : A ∈ φ.atoms) :
    m ⊨ Atom.toShapeReg A ↔ Sat.sat (sourceModel m) A := by
  have hvars : ∀ x ∈ A.vars, x ∈ Formula.vars φ := fun x hx => List.mem_flatMap.2 ⟨A, hA, hx⟩
  cases A <;> obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hvars
  · exact sat_toShapeReg_wordEq hm hg _ _ hu hv
  · exact sat_toShapeReg_lenEq hm hg _ _ hA hu hv

theorem Formula.guards_bind_toShapeReg_equisat [Inhabited Γ] (φ : Formula Γ V) :
    ShapeReg.Formula.SAT (guards φ ⋏ φ.bind Atom.toShapeReg) ↔ Formula.SAT φ := by
  constructor
  · rintro ⟨m, hm, hg, hφ⟩
    exact ⟨_, (Accordion.Formula.sat_bind _ m _ φ (sat_toShapeReg_atom hm hg)).1 hφ⟩
  · rintro ⟨m, hφ⟩
    have hm := wf_toShapeReg φ m
    have hg := sat_toShapeReg_guards φ m
    exact ⟨_, hm, hg, (Accordion.Formula.sat_bind _ _ _ φ (sat_toShapeReg_atom hm hg)).2
      ((sourceModel_toShapeReg φ m).symm ▸ hφ)⟩

end LenEq

end WE

end Accordion

end
