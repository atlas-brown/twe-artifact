module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Accordion.Formula.Properties
public import Accordion.WE.Properties
public import Accordion.WE.Len.ToLenEq.Defs

@[expose] public section

namespace Accordion

namespace WE

namespace Len

open scoped Accordion.Formula
open ToLenEq

variable {Γ : Type} {V : WE.Vars}

namespace ToLenEq

theorem length_evalWord_sidePart (m : LenEq.Model Γ V) (k : Int) (w : WE.Word Γ V) :
    (List.length (m.evalWord (sidePart true k w)) : Int) -
      List.length (m.evalWord (sidePart false k w)) = k * List.length (m.evalWord w) := by
  have key : ∀ n : Nat, List.length (m.evalWord ((List.replicate n w).foldr (· ++ ·) ε)) =
      n * List.length (m.evalWord w) := by
    intro n
    induction n with
    | zero => simp [Model.evalWord]
    | succ n ih =>
        simp only [List.replicate_succ, List.foldr_cons, Word.append_eq, Model.evalWord,
          List.length_append] at ih ⊢
        rw [ih]
        ring
  simp only [sidePart, key, Bool.cond_true, Bool.cond_false]
  push_cast
  rw [← sub_mul, Int.toNat_sub_toNat_neg]

theorem sat_guards_iff [Inhabited Γ] (m : LenEq.Model Γ (Vars V)) (xs : List V.Letter) :
    m ⊨ guards (Γ := Γ) xs ↔ ∀ x ∈ xs, List.length (m.σWord (.inl x)) = 1 := by
  rw [guards, Accordion.Formula.sat_bigConj, List.forall_mem_map]
  exact Iff.rfl

theorem evalWord_liftWord [Inhabited Γ] {m : LenEq.Model Γ (Vars V)} (u : WE.Word Γ V)
    (h : ∀ x ∈ u.letterVars, List.length (m.σWord (.inl x)) = 1) :
    m.evalWord (liftWord u) = (sourceModel m).evalWord u := by
  induction u with
  | letterVar x =>
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (h x List.mem_cons_self)
      change m.σWord (.inl x) = [(m.σWord (.inl x)).headD default]
      rw [hb]
      rfl
  | concat u v ihu ihv =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 h
      exact congrArg₂ (· ++ ·) (ihu hu) (ihv hv)
  | _ => rfl

end ToLenEq

theorem sat_toLenEq_atom [Inhabited Γ] {m : LenEq.Model Γ (ToLenEq.Vars V)} (A : Atom Γ V)
    (h : ∀ x ∈ A.letterVars, List.length (m.σWord (.inl x)) = 1) :
    m ⊨ Atom.toLenEq A ↔ Sat.sat (sourceModel m) A := by
  cases A with
  | wordEq u v =>
      obtain ⟨hu, hv⟩ := List.forall_mem_append.1 h
      change m.evalWord (liftWord u) = m.evalWord (liftWord v) ↔ _
      rw [evalWord_liftWord u hu, evalWord_liftWord v hv]
      exact Iff.rfl
  | wordLength c =>
      have key : ∀ ts : List (LenTerm V.Word),
          (List.length (m.evalWord (sideWord true c.c₀ ts)) : Int) -
            List.length (m.evalWord (sideWord false c.c₀ ts)) =
          c.c₀ + (ts.map fun t => t.c * (GroundWord.length (m.σWord (.inr t.x)) : Int)).sum := by
        intro ts
        induction ts with
        | nil =>
            simpa [sideWord, Model.evalWord] using length_evalWord_sidePart m c.c₀ (.letter default)
        | cons t ts ih =>
            have hlen := length_evalWord_sidePart m t.c (.var (.inr t.x))
            simp only [sideWord, Word.append_eq, Model.evalWord, List.length_append,
              List.map_cons, List.sum_cons, Nat.cast_add, GroundWord.length] at hlen ih ⊢
            linarith
      change GroundWord.length _ = GroundWord.length _ ↔
        Model.evalConstraint (sourceModel m) c = 0
      rw [Model.evalConstraint, sourceModel, ← key]
      simp only [GroundWord.length]
      omega

theorem Formula.guards_bind_toLenEq_equisat [Inhabited Γ] (φ : Formula Γ V) :
    LenEq.Formula.SAT (guards (Formula.letterVars φ) ⋏ φ.bind Atom.toLenEq) ↔
      Formula.SAT φ := by
  have atoms : ∀ m : LenEq.Model Γ (ToLenEq.Vars V),
      m ⊨ guards (Γ := Γ) (Formula.letterVars φ) →
      ∀ A ∈ φ.atoms, m ⊨ Atom.toLenEq A ↔ Sat.sat (sourceModel m) A := fun m hg A hA =>
    sat_toLenEq_atom A fun x hx =>
      (sat_guards_iff m _).1 hg x (List.mem_flatMap.2 ⟨A, hA, hx⟩)
  constructor
  · rintro ⟨m, hg, hφ⟩
    exact ⟨_, (Accordion.Formula.sat_bind _ m _ φ (atoms m hg)).1 hφ⟩
  · rintro ⟨m, hφ⟩
    have hg : Model.toLenEq m ⊨ guards (Γ := Γ) (Formula.letterVars φ) :=
      (sat_guards_iff _ _).2 fun _ _ => rfl
    exact ⟨_, hg, (Accordion.Formula.sat_bind _ _ _ φ (atoms _ hg)).2 hφ⟩

end Len

end WE

end Accordion

end
