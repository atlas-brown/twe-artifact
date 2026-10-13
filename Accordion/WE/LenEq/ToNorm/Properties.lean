module

public import Accordion.Formula.Properties
public import Accordion.Path.Measures
public import Accordion.WE.LenEq.ToNorm.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula
open ToNorm Accordion.Path GroundWord

variable {Γ X : Type} {V : WE.Vars}

namespace ToNorm

variable [IsEmpty V.Letter]

theorem depth_parents (n : Nat) : (parents n : Accordion.Path Γ).depth = -(n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [parents, depth, Component.depth, ih]
      omega

theorem parents_add (n k : Nat) :
    (parents (n + k) : Accordion.Path Γ) = parents n ++ parents k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (Path.app · ‥) ih

theorem isAnchored_join_parents {p : Accordion.Path Γ} (hp : p.IsAnchored) {n : Nat}
    (hn : (n : Int) ≤ p.depth) : (p ++ parents n).IsAnchored := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      refine (isAnchored_app_iff (p ++ parents n) ‥).2 ⟨ih (by omega), ?_⟩
      rw [depth_join, depth_parents, Component.depth]
      omega

theorem isBalanced_descend_join_parents (w : GroundWord Γ) :
    (descend w ++ parents (List.length w)).IsBalanced :=
  ⟨isAnchored_join_parents (isAnchored_of_linear (linear_descend w)) (by rw [depth_descend]; omega),
    by rw [depth_join, depth_parents, depth_descend]; omega⟩

theorem sourceModel_toNorm (m : Model Γ V) : sourceModel (Model.toNorm m) = m :=
  congr (congrArg Model.mk (funext fun x => isEmptyElim x)) (funext fun _ =>
    (congrArg names (norm_eq_self_of_linear (linear_descend _))).trans (names_descend _))

theorem sat_inverseGuards_iff [Inhabited Γ] (τ : Norm.Model Γ (Var X)) (xs : List X) :
    τ ⊨ inverseGuards (Γ := Γ) xs ↔
      (((default : Γ) : Accordion.Path Γ) ++ τ.σPath .up).IsBalanced ∧
        ∀ x ∈ xs, (τ.σPath (.source x) ++ τ.σPath (.inverse x)).IsBalanced := by
  change τ ⊨ _ ∧ τ ⊨ Accordion.Formula.bigConj _ ↔ _
  rw [Norm.Model.sat_pathBalanced, Accordion.Formula.sat_bigConj, List.forall_mem_map]
  exact and_congr Iff.rfl
    (forall₂_congr fun x _ => Norm.Model.sat_pathBalanced τ _)

variable (τ : Norm.Model Γ (Var V.Word)) {xs : List V.Word}

theorem isAnchored_evalPath_liftWord
    (hinv : ∀ x ∈ xs, (τ.σPath (.source x) ++ τ.σPath (.inverse x)).IsBalanced)
    (u : WE.Word Γ V) (hu : ∀ x ∈ u.vars, x ∈ xs) :
    (τ.evalPath (liftWord u)).IsAnchored := by
  induction u with
  | empty => exact isAnchored_of_linear trivial
  | letter b => exact isAnchored_of_linear (p := (b : Accordion.Path Γ)) trivial
  | letterVar x => exact isEmptyElim x
  | var x => exact (hinv x (hu x List.mem_cons_self)).1.of_join_left
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hu
      exact (ihu hu).join (ihv hv)

theorem names_norm_evalPath_liftWord
    (hinv : ∀ x ∈ xs, (τ.σPath (.source x) ++ τ.σPath (.inverse x)).IsBalanced)
    (u : WE.Word Γ V) (hu : ∀ x ∈ u.vars, x ∈ xs) :
    names (τ.evalPath (liftWord u)).norm = (sourceModel τ).evalWord u := by
  induction u with
  | letterVar x => exact isEmptyElim x
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hu
      change names (τ.evalPath (liftWord u) ++ τ.evalPath (liftWord v)).norm = _
      rw [norm_join_of_isAnchored_right _ (isAnchored_evalPath_liftWord τ hinv v hv),
        names_join, ihu hu, ihv hv]
      rfl
  | _ => rfl

theorem depth_evalPath_liftWord
    (hinv : ∀ x ∈ xs, (τ.σPath (.source x) ++ τ.σPath (.inverse x)).IsBalanced)
    (u : WE.Word Γ V) (hu : ∀ x ∈ u.vars, x ∈ xs) :
    (τ.evalPath (liftWord u)).depth = (List.length ((sourceModel τ).evalWord u) : Int) := by
  rw [(isAnchored_evalPath_liftWord τ hinv u hu).depth_eq_length_norm,
    ← names_norm_evalPath_liftWord τ hinv u hu, length_names_of_linear (linear_norm _)]

theorem isBalanced_evalPath_liftWord_join_invertWord [Inhabited Γ]
    (hup : (((default : Γ) : Accordion.Path Γ) ++ τ.σPath .up).IsBalanced)
    (hinv : ∀ x ∈ xs, (τ.σPath (.source x) ++ τ.σPath (.inverse x)).IsBalanced)
    (v : WE.Word Γ V) (hv : ∀ x ∈ v.vars, x ∈ xs) :
    (τ.evalPath (liftWord v) ++ τ.evalPath (invertWord v)).IsBalanced := by
  induction v with
  | empty => exact ⟨isAnchored_of_linear trivial, rfl⟩
  | letter b =>
      have hd := hup.2
      simp only [depth_join, depth_coe] at hd
      exact ⟨(isAnchored_join_iff_of_isBalanced
        (isAnchored_of_linear (p := (b : Accordion.Path Γ)) trivial) hup).2 (by simp),
        (depth_join _ _).trans ((depth_coe b).symm ▸ hd)⟩
  | letterVar x => exact isEmptyElim x
  | var x => exact hinv x (hv x List.mem_cons_self)
  | concat v w ihv ihw =>
      obtain ⟨hv, hw⟩ := List.forall_mem_append.1 hv
      obtain ⟨hav, hdv⟩ := ihv hv
      obtain ⟨haw, hdw⟩ := ihw hw
      have hw0 := depth_nonneg_of_isAnchored haw.of_join_left
      simp only [depth_join] at hdv hdw
      have h1 := (isAnchored_join_iff_of_isBalanced (hav.of_join_left.join haw.of_join_left)
        (ihv hv)).2 (by rw [depth_join]; omega)
      have h2 := (isAnchored_join_iff_of_isBalanced h1 (ihw hw)).2
        (by simp only [depth_join]; omega)
      change ((τ.evalPath (liftWord v) ++ τ.evalPath (liftWord w)) ++
        (τ.evalPath (invertWord v) ++ τ.evalPath (invertWord w))).IsBalanced
      rw [join_assoc]
      exact ⟨h2, by simp only [depth_join]; omega⟩

end ToNorm

theorem sat_toNorm_inverseGuards [Inhabited Γ] (m : Model Γ V) (xs : List V.Word) :
    Model.toNorm m ⊨ inverseGuards (Γ := Γ) xs :=
  (sat_inverseGuards_iff _ xs).2
    ⟨isBalanced_descend_join_parents [default], fun _ _ => isBalanced_descend_join_parents _⟩

variable [IsEmpty V.Letter]

theorem sat_toNorm_wordEq [Inhabited Γ] {τ : Norm.Model Γ (Var V.Word)} {xs : List V.Word}
    (hg : τ ⊨ inverseGuards (Γ := Γ) xs) (u v : WE.Word Γ V)
    (hu : ∀ x ∈ u.vars, x ∈ xs) (hv : ∀ x ∈ v.vars, x ∈ xs) :
    τ ⊨ Atom.toNorm (.wordEq u v) ↔
      (sourceModel τ).evalWord u = (sourceModel τ).evalWord v := by
  obtain ⟨-, hinv⟩ := (sat_inverseGuards_iff τ xs).1 hg
  rw [← names_norm_evalPath_liftWord τ hinv u hu, ← names_norm_evalPath_liftWord τ hinv v hv]
  refine ⟨congrArg names, fun h => ?_⟩
  have := congrArg descend h
  rwa [descend_names_of_linear (linear_norm _), descend_names_of_linear (linear_norm _)] at this

theorem sat_toNorm_lenEq [Inhabited Γ] {τ : Norm.Model Γ (Var V.Word)} {xs : List V.Word}
    (hg : τ ⊨ inverseGuards (Γ := Γ) xs) (u v : WE.Word Γ V)
    (hu : ∀ x ∈ u.vars, x ∈ xs) (hv : ∀ x ∈ v.vars, x ∈ xs) :
    τ ⊨ Atom.toNorm (.lenEq u v) ↔
      GroundWord.length ((sourceModel τ).evalWord u) =
        GroundWord.length ((sourceModel τ).evalWord v) := by
  obtain ⟨hup, hinv⟩ := (sat_inverseGuards_iff τ xs).1 hg
  have hdu := depth_evalPath_liftWord τ hinv u hu
  have hdv := depth_evalPath_liftWord τ hinv v hv
  have hbal := isBalanced_evalPath_liftWord_join_invertWord τ hup hinv v hv
  have hd := hbal.2
  change τ ⊨ Norm.Formula.pathBalanced (liftWord u ++ invertWord v) ↔ _
  rw [Norm.Model.sat_pathBalanced]
  change (τ.evalPath (liftWord u) ++ τ.evalPath (invertWord v)).IsAnchored ∧
    (τ.evalPath (liftWord u) ++ τ.evalPath (invertWord v)).depth = 0 ↔ _
  rw [isAnchored_join_iff_of_isBalanced (isAnchored_evalPath_liftWord τ hinv u hu) hbal]
  simp only [depth_join, GroundWord.length] at hd ⊢
  omega

theorem Formula.inverseGuards_bind_equisat [Inhabited Γ] (φ : Formula Γ V) :
    Norm.Formula.SAT (inverseGuards (Formula.vars φ) ⋏ φ.bind Atom.toNorm) ↔
      Formula.SAT φ := by
  have atoms : ∀ τ : Norm.Model Γ (Var V.Word),
      τ ⊨ inverseGuards (Γ := Γ) (Formula.vars φ) →
      ∀ A ∈ φ.atoms, τ ⊨ Atom.toNorm A ↔ Sat.sat (sourceModel τ) A := by
    intro τ hg A hA
    have hvars : ∀ x ∈ A.vars, x ∈ Formula.vars φ := fun x hx => List.mem_flatMap.2 ⟨A, hA, hx⟩
    cases A <;> obtain ⟨hu, hv⟩ := List.forall_mem_append.1 hvars
    · exact sat_toNorm_wordEq hg _ _ hu hv
    · exact sat_toNorm_lenEq hg _ _ hu hv
  constructor
  · rintro ⟨τ, hg, hφ⟩
    exact ⟨_, (Accordion.Formula.sat_bind _ τ _ φ (atoms τ hg)).1 hφ⟩
  · rintro ⟨m, hφ⟩
    have hg := sat_toNorm_inverseGuards m (Formula.vars φ)
    exact ⟨_, hg, (Accordion.Formula.sat_bind _ _ _ φ (atoms _ hg)).2
      ((sourceModel_toNorm m).symm ▸ hφ)⟩

end LenEq

end WE

end Accordion

end
