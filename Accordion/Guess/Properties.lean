module

public import Accordion.Guess
public import Mathlib.Data.List.Sublists

@[expose] public section

namespace Accordion

variable {α β : Type}

namespace Guess

theorem mem_iff_of_any_eq {D : Guess α} {xs : List α} (h : ∀ p, D.any p = xs.any p) {x : α} :
    x ∈ D ↔ x ∈ xs := by
  classical
  refine ⟨fun hx => ?_, fun hx p hp => (h p).trans (List.any_eq_true.2 ⟨x, hx, hp⟩)⟩
  have := hx (fun y => decide (y = x)) (by simp)
  rw [h] at this
  simpa using this

theorem any_eq_true {D : Guess α} {p : α → Bool} : D.any p = true ↔ ∃ x ∈ D, p x = true := by
  obtain ⟨xs, hxs⟩ := D.lawful
  simp only [hxs, List.any_eq_true, mem_iff_of_any_eq hxs]

@[ext]
theorem ext {D E : Guess α} (h : ∀ x, x ∈ D ↔ x ∈ E) : D = E := by
  have : D.any = E.any := funext fun p => by
    rw [Bool.eq_iff_iff, any_eq_true, any_eq_true]
    simp only [h]
  cases D; cases E; cases this; rfl

end Guess

@[simp] theorem mem_guess {xs : List α} {x : α} : x ∈ guess xs ↔ x ∈ xs :=
  Guess.mem_iff_of_any_eq fun _ => rfl

namespace Guess

@[simp] theorem any_guess {xs : List α} {p : α → Bool} : (guess xs).any p = xs.any p := rfl

@[simp] theorem any_pure {a : α} {p : α → Bool} : (pure a : Guess α).any p = p a := rfl

@[simp] theorem any_bind {D : Guess α} {f : α → Guess β} {p : β → Bool} :
    (D >>= f).any p = D.any fun a => (f a).any p := rfl

@[simp] theorem any_map {D : Guess α} {f : α → β} {p : β → Bool} :
    (f <$> D).any p = D.any fun a => p (f a) := rfl

@[simp] theorem any_failure {p : α → Bool} : (failure : Guess α).any p = false := rfl

@[simp] theorem any_append {D E : Guess α} {p : α → Bool} :
    (D ++ E).any p = (D.any p || E.any p) := rfl

theorem mem_iff_any {D : Guess α} {x : α} [DecidableEq α] :
    x ∈ D ↔ D.any (fun y => decide (y = x)) = true := by
  simp [any_eq_true]

@[simp] theorem mem_pure {a x : α} : x ∈ (pure a : Guess α) ↔ x = a := by
  classical simp [mem_iff_any, eq_comm]

@[simp] theorem mem_bind {D : Guess α} {f : α → Guess β} {y : β} :
    y ∈ D >>= f ↔ ∃ x ∈ D, y ∈ f x := by
  classical
  rw [mem_iff_any, any_bind, any_eq_true]
  simp only [← mem_iff_any]

@[simp] theorem mem_flatMap {D : Guess α} {f : α → Guess β} {y : β} :
    y ∈ D.flatMap f ↔ ∃ x ∈ D, y ∈ f x :=
  mem_bind

@[simp] theorem mem_map {D : Guess α} {f : α → β} {y : β} :
    y ∈ f <$> D ↔ ∃ x ∈ D, f x = y := by
  classical
  rw [mem_iff_any, any_map, any_eq_true]
  simp

@[simp] theorem mem_map' {D : Guess α} {f : α → β} {y : β} :
    y ∈ D.map f ↔ ∃ x ∈ D, f x = y :=
  mem_map

@[simp] theorem notMem_failure {x : α} : x ∉ (failure : Guess α) := by
  classical simp [mem_iff_any]

@[simp] theorem mem_append {D E : Guess α} {x : α} : x ∈ D ++ E ↔ x ∈ D ∨ x ∈ E := by
  classical simp [mem_iff_any]

instance : LawfulMonad Guess :=
  LawfulMonad.mk' (m := Guess)
    (id_map := fun D => ext fun x => by simp)
    (pure_bind := fun a f => ext fun x => by simp)
    (bind_assoc := fun D f g => ext fun x => by
      simp only [mem_bind]
      exact ⟨fun ⟨y, ⟨z, hz, hy⟩, hx⟩ => ⟨z, hz, y, hy, hx⟩,
        fun ⟨z, hz, y, hy, hx⟩ => ⟨y, ⟨z, hz, hy⟩, hx⟩⟩)
    (bind_pure_comp := fun f D => ext fun x => by simp [eq_comm])

@[simp] theorem mem_guard {p : Prop} [Decidable p] {u : Unit} : u ∈ (guard p : Guess Unit) ↔ p := by
  by_cases h : p <;> simp [guard, h]

@[simp] theorem mem_sublist : ∀ {l s : List α}, s ∈ sublist l ↔ s ∈ l.sublists
  | [], s => by simp [sublist]
  | a :: l, s => by
    simp only [sublist, mem_bind, mem_pure, mem_guess, mem_sublist (l := l), List.mem_sublists,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨t, ht, k, rfl | rfl, rfl⟩
      · exact ht.cons _
      · exact ht.cons_cons _
    · intro h
      cases h with
      | cons _ h => exact ⟨s, h, false, by simp⟩
      | cons_cons _ h => exact ⟨_, h, true, by simp⟩

end Guess

end Accordion

end
