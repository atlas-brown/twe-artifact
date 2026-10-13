module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace Accordion

/-- A nondeterministic computation that produces one `α` per run (§6): `any p` says whether some
run's result passes `p`, and the results, which are those of some list, are never collected. -/
structure Guess (α : Type) where
  any : (α → Bool) → Bool
  lawful : ∃ xs : List α, ∀ p, any p = xs.any p

variable {α β : Type}

def guess (xs : List α) : Guess α := ⟨xs.any, xs, fun _ => rfl⟩

namespace Guess

/-- `x` is the result of some run: every test that `x` passes is passed by some run. -/
protected def Mem (D : Guess α) (x : α) : Prop := ∀ p : α → Bool, p x = true → D.any p = true

instance : Membership α (Guess α) := ⟨Guess.Mem⟩

protected def pure (a : α) : Guess α := ⟨fun p => p a, [a], fun p => by simp⟩

protected def bind (D : Guess α) (f : α → Guess β) : Guess β where
  any p := D.any fun a => (f a).any p
  lawful := by
    obtain ⟨xs, hxs⟩ := D.lawful
    suffices h : ∃ ys : List β, ∀ p, (xs.any fun a => (f a).any p) = ys.any p by
      obtain ⟨ys, hys⟩ := h
      exact ⟨ys, fun p => (hxs _).trans (hys p)⟩
    clear hxs
    induction xs with
    | nil => exact ⟨[], fun _ => rfl⟩
    | cons a xs ih =>
      obtain ⟨ys, hys⟩ := ih
      obtain ⟨zs, hzs⟩ := (f a).lawful
      exact ⟨zs ++ ys, fun p => by simp [hys, hzs]⟩

protected def map (f : α → β) (D : Guess α) : Guess β where
  any p := D.any fun a => p (f a)
  lawful := by
    obtain ⟨xs, hxs⟩ := D.lawful
    exact ⟨xs.map f, fun p => by simp [hxs, List.any_map, Function.comp_def]⟩

protected def failure : Guess α := guess []

protected def append (D E : Guess α) : Guess α where
  any p := D.any p || E.any p
  lawful := by
    obtain ⟨xs, hxs⟩ := D.lawful
    obtain ⟨ys, hys⟩ := E.lawful
    exact ⟨xs ++ ys, fun p => by simp [hxs, hys]⟩

instance : Monad Guess where
  pure := Guess.pure
  bind := Guess.bind
  map := Guess.map

instance : Alternative Guess where
  failure := Guess.failure
  orElse D E := D.append (E ())

instance : Append (Guess α) := ⟨Guess.append⟩

protected def flatMap (D : Guess α) (f : α → Guess β) : Guess β := D.bind f

def sublist : List α → Guess (List α)
  | [] => pure []
  | a :: l => do
    let s ← sublist l
    let keep ← guess [false, true]
    pure (if keep then a :: s else s)

end Guess

end Accordion

end
