module

public import Accordion.WE.Decidability.Properties.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Accordion.WE.Decidability

open Finset

namespace LinSystem

variable {k m : ℕ}

theorem solves_of_mem_halve {A : Fin k → Fin m → ℤ} {c c' : Fin k → ℤ} (h : c' ∈ halve A c)
    {v' : Fin m → ℕ} (hv' : Solves ⟨A, c'⟩ v') : ∃ v, Solves ⟨A, c⟩ v := by
  obtain ⟨β, hβ, rfl⟩ := mem_image.1 h
  refine ⟨fun i => 2 * v' i + (β i).toNat, fun r => ?_⟩
  have h2 := Int.ediv_mul_cancel ((mem_filter.1 hβ).2 r)
  have hr : ∑ i, A r i * (v' i : ℤ) = rest A c β r / 2 := hv' r
  have hsum : ∑ i, A r i * ((2 * v' i + (β i).toNat : ℕ) : ℤ) =
      2 * ∑ i, A r i * (v' i : ℤ) + ∑ i, A r i * (β i).toNat := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by push_cast; ring
  change ∑ i, A r i * ((2 * v' i + (β i).toNat : ℕ) : ℤ) = c r
  have hrest : rest A c β r = c r - ∑ i, A r i * (β i).toNat := rfl
  linarith

theorem exists_mem_halve_of_solves {A : Fin k → Fin m → ℤ} {c : Fin k → ℤ} {v : Fin m → ℕ}
    (hv : Solves ⟨A, c⟩ v) (hv0 : v ≠ 0) :
    ∃ c' ∈ halve A c, Solves ⟨A, c'⟩ (fun i => v i / 2) ∧ ∑ i, v i / 2 < ∑ i, v i := by
  set β : Fin m → Bool := fun i => v i % 2 == 1
  have hβ (i : Fin m) : (β i).toNat = v i % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (v i) with h | h <;> simp [β, h]
  have hrest (r : Fin k) : rest A c β r = 2 * ∑ i, A r i * (v i / 2 : ℕ) := by
    have hr : ∑ i, A r i * (v i : ℤ) = c r := hv r
    simp only [rest, hβ]
    rw [← hr, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    have := Nat.div_add_mod (v i) 2
    have : (v i : ℤ) = 2 * (v i / 2 : ℕ) + (v i % 2 : ℕ) := by exact_mod_cast this.symm
    rw [this]
    ring
  refine ⟨fun r => rest A c β r / 2, mem_image.2 ⟨β, mem_filter.2 ⟨mem_univ _, fun r => ?_⟩, rfl⟩,
    fun r => ?_, ?_⟩
  · rw [hrest]
    exact dvd_mul_right _ _
  · simp only [hrest]
    rw [Int.mul_ediv_cancel_left _ two_ne_zero]
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact sum_lt_sum (fun i _ => Nat.div_le_self _ _)
      ⟨j, mem_univ _, Nat.div_lt_self (Nat.pos_of_ne_zero hj) one_lt_two⟩

theorem solvable_iff_reflTransGen (S : LinSystem k m) :
    S.Solvable ↔ Relation.ReflTransGen (fun x y => y ∈ halve S.A x) S.b 0 := by
  constructor
  · rintro ⟨v, hv⟩
    induction hs : ∑ i, v i using Nat.strong_induction_on generalizing S v with
    | _ n ih =>
      by_cases hv0 : v = 0
      · have : S.b = 0 := funext fun r => by simpa [hv0] using (hv r).symm
        rw [this]
      · obtain ⟨c', hc', hv', hlt⟩ := exists_mem_halve_of_solves (A := S.A) (c := S.b) hv hv0
        exact Relation.ReflTransGen.head hc' (ih _ (hs ▸ hlt) ⟨S.A, c'⟩ _ hv' rfl)
  · suffices ∀ c, Relation.ReflTransGen (fun x y => y ∈ halve S.A x) c 0 →
        Solvable ⟨S.A, c⟩ from this S.b
    intro c h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, fun r => by simp⟩
    | head hc _ ih =>
      obtain ⟨v', hv'⟩ := ih
      exact solves_of_mem_halve hc hv'

theorem abs_b_le_bound (S : LinSystem k m) (r : Fin k) : |S.b r| ≤ S.bound :=
  le_trans (le_add_of_nonneg_right (sum_nonneg fun _ _ => abs_nonneg _))
    (single_le_sum (f := fun r => |S.b r| + ∑ i, |S.A r i|)
      (fun _ _ => add_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)) (mem_univ r))

theorem sum_abs_A_le_bound (S : LinSystem k m) (r : Fin k) : ∑ i, |S.A r i| ≤ S.bound :=
  le_trans (le_add_of_nonneg_left (abs_nonneg _))
    (single_le_sum (f := fun r => |S.b r| + ∑ i, |S.A r i|)
      (fun _ _ => add_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)) (mem_univ r))

theorem mem_states {S : LinSystem k m} {c : Fin k → ℤ} : c ∈ S.states ↔ ∀ r, |c r| ≤ S.bound := by
  simp [states, abs_le]

theorem halve_subset_states (S : LinSystem k m) {c : Fin k → ℤ} (hc : c ∈ S.states) :
    halve S.A c ⊆ S.states := by
  intro c' hc'
  obtain ⟨β, hβ, rfl⟩ := mem_image.1 hc'
  refine mem_states.2 fun r => ?_
  have h2 := Int.ediv_mul_cancel ((mem_filter.1 hβ).2 r)
  have hAβ : |∑ i, S.A r i * ((β i).toNat : ℤ)| ≤ ∑ i, |S.A r i| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    cases β i <;> simp
  have hrest : |rest S.A c β r| ≤ 2 * S.bound := by
    have := (abs_sub _ _).trans
      (add_le_add (mem_states.1 hc r) (hAβ.trans (S.sum_abs_A_le_bound r)))
    simpa [rest, two_mul] using this
  rw [← h2, abs_mul] at hrest
  simp only [abs_two] at hrest
  linarith

theorem card_states (S : LinSystem k m) : S.states.card = (2 * S.bound + 1).toNat ^ k := by
  simp only [states, Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
  congr 2
  ring

lemma mem_verifyDiophantine_succ {A : Fin k → Fin m → ℤ} {n : ℕ} {c : Fin k → ℤ} :
    true ∈ verifyDiophantine A (n + 1) c ↔
      c = 0 ∨ ∃ c' ∈ halve A c, true ∈ verifyDiophantine A n c' := by
  by_cases hc : c = 0
  · simp [verifyDiophantine, hc]
  · simp only [verifyDiophantine, hc, ite_false, false_or, halve, mem_image, mem_filter, mem_univ,
      true_and]
    simp only [Guess.mem_bind]
    constructor
    · rintro ⟨β, -, hβ⟩
      split_ifs at hβ with h
      · exact ⟨_, ⟨β, h, rfl⟩, hβ⟩
      · simp at hβ
    · rintro ⟨_, ⟨β, h, rfl⟩, hβ⟩
      exact ⟨β, mem_bitVectors β, by simpa [h] using hβ⟩

theorem solves_of_verifyDiophantine {A : Fin k → Fin m → ℤ} :
    ∀ {n : ℕ} {c : Fin k → ℤ}, true ∈ verifyDiophantine A n c → ∃ v, Solves ⟨A, c⟩ v
  | 0, _, h => by simp [verifyDiophantine] at h
  | n + 1, c, h => by
    rcases mem_verifyDiophantine_succ.1 h with rfl | ⟨c', hc', h⟩
    · exact ⟨fun _ => 0, fun r => by simp⟩
    · obtain ⟨v', hv'⟩ := solves_of_verifyDiophantine h
      exact solves_of_mem_halve hc' hv'

theorem verifyDiophantine_of_reachIn {A : Fin k → Fin m → ℤ} :
    ∀ {n : ℕ} {c : Fin k → ℤ}, ReachIn (halve A) n c 0 → true ∈ verifyDiophantine A (n + 1) c
  | 0, c, h => mem_verifyDiophantine_succ.2 (.inl h)
  | n + 1, c, h => by
    rcases h with h | ⟨c', hc', h⟩
    · exact mem_verifyDiophantine_succ.2 (.inl h)
    · exact mem_verifyDiophantine_succ.2 (.inr ⟨c', hc', verifyDiophantine_of_reachIn h⟩)

theorem true_mem_verify_iff (S : LinSystem k m) : true ∈ S.verify ↔ S.Solvable := by
  rw [verify]
  refine ⟨fun h => solves_of_verifyDiophantine h, fun h => ?_⟩
  have := reachIn_card_of_reflTransGen (mem_states.2 S.abs_b_le_bound)
    (fun _ => S.halve_subset_states) ((solvable_iff_reflTransGen S).1 h)
  rw [card_states] at this
  exact verifyDiophantine_of_reachIn this

lemma bound_lenSystem_le (eqs : List (Length × Length)) :
    (lenSystem eqs).bound ≤ eqs.length * ((eqs.map fun p ↦ p.1.const + p.2.const).sum
      + (lenVars eqs).length * (eqs.map fun p ↦ p.1.vars.length + p.2.vars.length).sum) := by
  have hrow (r : Fin eqs.length) : |(lenSystem eqs).b r| + ∑ i, |(lenSystem eqs).A r i| ≤
      (((eqs.map fun p ↦ p.1.const + p.2.const).sum + (lenVars eqs).length *
        (eqs.map fun p ↦ p.1.vars.length + p.2.vars.length).sum : ℕ) : ℤ) := by
    have hc : (eqs.get r).1.const + (eqs.get r).2.const ≤
        (eqs.map fun p ↦ p.1.const + p.2.const).sum :=
      List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _
        (List.mem_map.2 ⟨_, List.get_mem eqs r, rfl⟩)
    have hv : (eqs.get r).1.vars.length + (eqs.get r).2.vars.length ≤
        (eqs.map fun p ↦ p.1.vars.length + p.2.vars.length).sum :=
      List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _
        (List.mem_map.2 ⟨_, List.get_mem eqs r, rfl⟩)
    have hb : |(lenSystem eqs).b r| ≤
        (((eqs.get r).1.const + (eqs.get r).2.const : ℕ) : ℤ) := by
      simp only [lenSystem]
      rw [abs_le]
      constructor <;> push_cast <;> omega
    have hA (i : Fin (lenVars eqs).length) : |(lenSystem eqs).A r i| ≤
        (((eqs.get r).1.vars.length + (eqs.get r).2.vars.length : ℕ) : ℤ) := by
      have h1 := List.count_le_length (a := (lenVars eqs)[i]) (l := (eqs.get r).1.vars)
      have h2 := List.count_le_length (a := (lenVars eqs)[i]) (l := (eqs.get r).2.vars)
      simp only [lenSystem]
      rw [abs_le]
      constructor <;> push_cast <;> omega
    have hs : ∑ i, |(lenSystem eqs).A r i| ≤ ((lenVars eqs).length : ℤ) *
        (((eqs.get r).1.vars.length + (eqs.get r).2.vars.length : ℕ) : ℤ) := by
      simpa using sum_le_card_nsmul univ _ _ fun i _ ↦ hA i
    calc |(lenSystem eqs).b r| + ∑ i, |(lenSystem eqs).A r i|
        ≤ (((eqs.get r).1.const + (eqs.get r).2.const : ℕ) : ℤ) + ((lenVars eqs).length : ℤ) *
          (((eqs.get r).1.vars.length + (eqs.get r).2.vars.length : ℕ) : ℤ) := add_le_add hb hs
      _ ≤ _ := by exact_mod_cast Nat.add_le_add hc (Nat.mul_le_mul_left _ hv)
  simpa [bound] using sum_le_card_nsmul univ _ _ fun r _ ↦ hrow r

end LinSystem

end Accordion.WE.Decidability

end
