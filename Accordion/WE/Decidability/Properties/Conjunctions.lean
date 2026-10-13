module

public import Accordion.WE.Decidability.Steps
public import Accordion.Guess.Properties

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

lemma exists_mem_append {α : Type} {P : α → Prop} {D E : Guess (List α)} :
    (∃ c ∈ (do let c ← D; let d ← E; pure (c ++ d) : Guess (List α)), ∀ l ∈ c, P l) ↔
      (∃ c ∈ D, ∀ l ∈ c, P l) ∧ ∃ d ∈ E, ∀ l ∈ d, P l := by
  simp only [Guess.mem_bind, Guess.mem_pure]
  constructor
  · rintro ⟨_, ⟨c, hc, d, hd, rfl⟩, h⟩
    exact ⟨⟨c, hc, fun l hl ↦ h l (List.mem_append_left _ hl)⟩,
      ⟨d, hd, fun l hl ↦ h l (List.mem_append_right _ hl)⟩⟩
  · rintro ⟨⟨c, hc, h⟩, ⟨d, hd, h'⟩⟩
    refine ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, fun l hl ↦ ?_⟩
    rcases List.mem_append.1 hl with hl | hl
    · exact h l hl
    · exact h' l hl

lemma exists_mem_either {β : Type} {Q : β → Prop} {D E : Guess β} :
    (∃ c ∈ (do let left ← guess [true, false]; if left then D else E : Guess β), Q c) ↔
      (∃ c ∈ D, Q c) ∨ ∃ c ∈ E, Q c := by
  simp only [Guess.mem_bind, mem_guess, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨c, ⟨left, rfl | rfl, hc⟩, h⟩
    exacts [.inl ⟨c, by simpa using hc, h⟩, .inr ⟨c, by simpa using hc, h⟩]
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    exacts [⟨c, ⟨true, .inl rfl, by simpa using hc⟩, h⟩,
      ⟨c, ⟨false, .inr rfl, by simpa using hc⟩, h⟩]

lemma sat_iff_guessConj (m : Model Γ V) :
    ∀ φ : Formula Γ V,
      (m ⊨ φ ↔ ∃ c ∈ guessConj.positive φ, ∀ l ∈ c, l.Holds m) ∧
        (¬m ⊨ φ ↔ ∃ c ∈ guessConj.negative φ, ∀ l ∈ c, l.Holds m)
  | .top => by simp [guessConj.positive, guessConj.negative, Formula.sat]
  | .bot => by simp [guessConj.positive, guessConj.negative, Formula.sat]
  | .atom (.wordEq p q) => by
      simp [guessConj.positive, guessConj.negative, Literal.Holds, Sat.sat, Model.satAtom]
  | .conj φ ψ => by
      obtain ⟨h1, h1'⟩ := sat_iff_guessConj m φ
      obtain ⟨h2, h2'⟩ := sat_iff_guessConj m ψ
      rw [guessConj.positive, guessConj.negative, exists_mem_append, exists_mem_either,
        ← h1, ← h2, ← h1', ← h2']
      simp only [Formula.sat, not_and_or, iff_self, and_self]
  | .disj φ ψ => by
      obtain ⟨h1, h1'⟩ := sat_iff_guessConj m φ
      obtain ⟨h2, h2'⟩ := sat_iff_guessConj m ψ
      rw [guessConj.positive, guessConj.negative, exists_mem_either, exists_mem_append,
        ← h1, ← h2, ← h1', ← h2']
      simp only [Formula.sat, not_or, iff_self, and_self]
  | .neg φ => by
      obtain ⟨h, h'⟩ := sat_iff_guessConj m φ
      rw [guessConj.positive, guessConj.negative, ← h, ← h']
      simp only [Formula.sat, not_not, iff_self, and_self]

theorem guessConj_equisat (φ : Formula Γ V) : (∃ c ∈ guessConj φ, c.SAT) ↔ φ.SAT := by
  simp only [Formula.SAT, guessConj, Conj.SAT]
  constructor
  · rintro ⟨c, hc, m, h⟩
    exact ⟨m, (sat_iff_guessConj m φ).1.2 ⟨c, hc, h⟩⟩
  · rintro ⟨m, hm⟩
    obtain ⟨c, hc, h⟩ := (sat_iff_guessConj m φ).1.1 hm
    exact ⟨c, hc, m, h⟩

end Accordion.WE.Decidability

end
