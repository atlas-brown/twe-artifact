module

public import Accordion.WE.Decidability.Properties.Basic

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

lemma length_sepBy (a : Γ) (us : List (List Γ)) :
    List.length (sepBy a us) = (us.map List.length).sum + us.length := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [sepBy] at ih ⊢; omega

lemma getElem?_append_cons_length (u v : List Γ) (a : Γ) : (u ++ a :: v)[u.length]? = some a := by
  simp

lemma eq_of_sepBy_eq {a b : Γ} (hab : a ≠ b) :
    ∀ {us vs : List (GroundWord Γ)}, us.length = vs.length → sepBy a us = sepBy a vs →
      sepBy b us = sepBy b vs → us = vs
  | [], [], _, _, _ => rfl
  | u :: us, v :: vs, hl, ha, hb => by
      simp only [sepBy, List.flatMap_cons, List.append_assoc, List.cons_append,
        List.nil_append] at ha hb
      have key : ∀ {u v : List Γ} {x y : List Γ}, u ++ a :: x = v ++ a :: y →
          ∀ {x' y' : List Γ}, u ++ b :: x' = v ++ b :: y' → ¬u.length < v.length := by
        intro u v x y h1 x' y' h2 hlt
        have e1 := congrArg (·[u.length]?) h1
        have e2 := congrArg (·[u.length]?) h2
        simp only [getElem?_append_cons_length, List.getElem?_append_left hlt] at e1 e2
        exact hab (Option.some.inj (e1.trans e2.symm))
      have huv : u.length = v.length := by
        rcases lt_trichotomy u.length v.length with h | h | h
        · exact absurd h (key ha hb)
        · exact h
        · exact absurd h (key ha.symm hb.symm)
      obtain ⟨rfl, ha'⟩ := List.append_inj ha huv
      obtain ⟨-, hb'⟩ := List.append_inj hb huv
      rw [eq_of_sepBy_eq hab (by simpa using hl) (List.cons.inj ha').2 (List.cons.inj hb').2]

lemma sepBy_eq_iff {a b : Γ} (hab : a ≠ b) {us vs : List (GroundWord Γ)}
    (hl : us.length = vs.length) :
    sepBy a us ++ sepBy b us = sepBy a vs ++ sepBy b vs ↔ us = vs := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hlen : List.length (sepBy a us) = List.length (sepBy a vs) := by
    have := congrArg List.length h
    rw [List.length_append, List.length_append] at this
    simp only [length_sepBy] at this ⊢
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact eq_of_sepBy_eq hab hl h1 h2

lemma eval_flatMap_sep (σ : Subst Γ V) (a : Γ) (us : List (Side Γ V)) :
    eval σ (us.flatMap (· ++ [.inl a])) = sepBy a (us.map (eval σ)) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [sepBy, eval, Sym.eval] at ih ⊢; rw [ih]

lemma solves_joinEquations [DecidableEq Γ] [Fresh Γ] (σ : Subst Γ V) (E : System Γ V) :
    (joinEquations E).Solves σ ↔ ∀ e ∈ E, e.Solves σ := by
  have h1 : ∀ a, eval σ (E.flatMap (·.1 ++ [.inl a])) = sepBy a (E.map fun e ↦ eval σ e.1) :=
    fun a ↦ by
      simpa [List.flatMap_map, Function.comp_def] using eval_flatMap_sep σ a (E.map Prod.fst)
  have h2 : ∀ a, eval σ (E.flatMap (·.2 ++ [.inl a])) = sepBy a (E.map fun e ↦ eval σ e.2) :=
    fun a ↦ by
      simpa [List.flatMap_map, Function.comp_def] using eval_flatMap_sep σ a (E.map Prod.snd)
  have hab : Fresh.fresh (E.flatMap Eqn.letters).toFinset ≠
      Fresh.fresh (insert (Fresh.fresh (E.flatMap Eqn.letters).toFinset)
        (E.flatMap Eqn.letters).toFinset) :=
    fun h ↦ Fresh.fresh_notMem (insert _ _) (by rw [← h]; exact Finset.mem_insert_self _ _)
  simp only [joinEquations, Eqn.Solves, eval_append, h1, h2]
  rw [sepBy_eq_iff hab (by simp), List.map_inj_left]

lemma joinEquations_equisat [DecidableEq Γ] [Fresh Γ] (E : System Γ V) :
    (joinEquations E).Solvable ↔ E.Solvable := by
  simp only [Eqn.Solvable, System.Solvable, solves_joinEquations]

end Accordion.WE.Decidability

end
