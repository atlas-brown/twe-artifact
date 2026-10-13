module

public import Accordion.Formula

@[expose] public section

namespace Accordion

namespace Formula

variable {M N A B : Type}

variable [Sat M A] [Sat N B]

instance (m : M) [∀ a : A, Decidable (Sat.sat m a)] : (φ : Formula A) → Decidable (m ⊨ φ) := go
where
  go : (φ : Formula A) → Decidable (m ⊨ φ)
  | ⊤ => isTrue trivial
  | ⊥ => isFalse not_false
  | .atom a => inferInstanceAs (Decidable (Sat.sat m a))
  | φ ⋏ ψ =>
      letI := go φ; letI := go ψ
      inferInstanceAs (Decidable (m ⊨ φ ∧ m ⊨ ψ))
  | φ ⋎ ψ =>
      letI := go φ; letI := go ψ
      inferInstanceAs (Decidable (m ⊨ φ ∨ m ⊨ ψ))
  | ∼φ =>
      letI := go φ
      inferInstanceAs (Decidable (¬ m ⊨ φ))

theorem sat_bigConj (m : M) (Φ : List (Formula A)) :
    m ⊨ bigConj Φ ↔ ∀ φ ∈ Φ, m ⊨ φ := by
  induction Φ with
  | nil => simp [bigConj]
  | cons φ Φ ih => simp [bigConj, ih]

theorem sat_bigDisj (m : M) (Φ : List (Formula A)) :
    m ⊨ bigDisj Φ ↔ ∃ φ ∈ Φ, m ⊨ φ := by
  induction Φ with
  | nil => simp [bigDisj]
  | cons φ Φ ih => simp [bigDisj, ih]

theorem sat_bind (m : M) (n : N) (f : A → Formula B) (φ : Formula A)
    (h : ∀ a ∈ φ.atoms, n ⊨ f a ↔ Sat.sat m a) :
    n ⊨ φ.bind f ↔ m ⊨ φ := by
  induction φ with
  | atom a => exact h a List.mem_cons_self
  | conj φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := List.forall_mem_append.1 h
      exact and_congr (ihφ hφ) (ihψ hψ)
  | disj φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := List.forall_mem_append.1 h
      exact or_congr (ihφ hφ) (ihψ hψ)
  | neg φ ih => exact not_congr (ih h)
  | _ => exact Iff.rfl

@[grind =] theorem sat_conj {M Atom : Type} [Sat M Atom] (m : M) (φ ψ : Formula Atom) :
    sat m (.conj φ ψ) = (sat m φ ∧ sat m ψ) := rfl

end Formula

end Accordion

end
