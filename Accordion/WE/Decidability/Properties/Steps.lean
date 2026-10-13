module

public import Accordion.WE.Decidability.Properties.Conjunctions
public import Accordion.WE.Decidability.Properties.Phases
public import Accordion.WE.Decidability.Properties.Encoding
public import Accordion.WE.Decidability.Properties.Join

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

theorem solvedNaively_iff [DecidableEq Γ] [DecidableEq V.Word] {e : Eqn Γ V} (hs : e.Short) :
    SolvedNaively e ↔ e.Solvable :=
  ⟨SolvedNaively.solvable, solvedNaively_of_short hs⟩

variable [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word]

theorem wordEquations_equisat [DecidableEq V.Letter] [Fresh V.Word] (φ : Formula Γ V) :
    (∃ e ∈ wordEquations φ, e.Solvable) ↔ φ.SAT := by
  simp only [← guessConj_equisat, ← conjEquations_equisat, ← joinEquations_equisat, wordEquations,
    Guess.mem_bind, Guess.mem_pure]
  constructor
  · rintro ⟨_, ⟨c, hc, E, hE, rfl⟩, h⟩
    exact ⟨c, hc, E, hE, h⟩
  · rintro ⟨c, hc, E, hE, h⟩
    exact ⟨_, ⟨c, hc, E, hE, rfl⟩, h⟩

theorem pairComp_equisat (L₀ : List Γ) (hL₀ : L₀.Nodup) (S : List Γ) (e : Eqn Γ V)
    (he : e.letterCount + 2 * e.varCount ≤ L₀.length) :
    (∃ f ∈ pairComp L₀ S e, f.Solvable) ↔ e.Solvable := by
  refine ⟨fun ⟨f, hf, h⟩ ↦
    solvable_of_mem_pairComp hL₀ hf ((le_of_mem_pairComp hf).1.trans he) h, fun ⟨σ, hσ⟩ ↦ ?_⟩
  obtain ⟨σ₀, hσ₀, hA₀, -⟩ := e.exists_solves_letters hσ
  obtain ⟨f, hf, σ', hσ', -⟩ := exists_pair_succ L₀ hσ₀ hA₀ S
  exact ⟨f, hf, σ', hσ'⟩

theorem blockComp_equisat (L₀ : List Γ) (hL₀ : L₀.Nodup) (e : Eqn Γ V)
    (he : e.letterCount + 2 * e.varCount ≤ L₀.length) :
    (∃ f ∈ blockComp L₀ e, f.Solvable) ↔ e.Solvable := by
  refine ⟨fun ⟨f, hf, h⟩ ↦
    solvable_of_mem_blockComp hL₀ hf ((le_of_mem_blockComp hf).1.trans he) h, fun ⟨σ, hσ⟩ ↦ ?_⟩
  obtain ⟨σ₀, hσ₀, hA₀, -⟩ := e.exists_solves_letters hσ
  obtain ⟨f, hf, σ', hσ', -⟩ := exists_block_succ hL₀ hσ₀ hA₀ he
  exact ⟨f, hf, σ', hσ'⟩

theorem wordEqSat_sound {L₀ : List Γ} (hL₀ : L₀.Nodup) {bound v : Nat}
    (hb : bound + 6 * v ≤ L₀.length) :
    ∀ {fuel : Nat} {e : Eqn Γ V}, e.letterCount ≤ bound → e.varCount ≤ v →
      true ∈ wordEqSat L₀ bound fuel e → e.Solvable
  | 0, _, _, _, h => by simp [wordEqSat] at h
  | fuel + 1, e, hl, hv, h => by
    unfold wordEqSat at h
    split_ifs at h with hs
    · exact (solvedNaively_iff hs).1 (by simpa [SolvedNaively] using h)
    · simp only [Guess.mem_bind] at h
      obtain ⟨e₃, hp, h⟩ := h
      obtain ⟨e₁, h₁, S₁, -, e₂, h₂, S₂, -, h₃⟩ := mem_phase.1 hp
      split_ifs at h with hb₃
      · have b₁ := le_of_mem_blockComp h₁
        have b₂ := le_of_mem_pairComp h₂
        have b₃ := le_of_mem_pairComp h₃
        have hs₃ := e₃.size_eq
        exact (blockComp_equisat L₀ hL₀ e (by omega)).1 ⟨e₁, h₁,
          (pairComp_equisat L₀ hL₀ S₁ e₁ (by omega)).1 ⟨e₂, h₂,
            (pairComp_equisat L₀ hL₀ S₂ e₂ (by omega)).1 ⟨e₃, h₃,
              wordEqSat_sound hL₀ hb (by omega) (by omega) h⟩⟩⟩
      · simp at h

theorem wordEqSat_of_isChain {L₀ : List Γ} {bound : Nat} :
    ∀ (es : List (Eqn Γ V)) (e : Eqn Γ V) (fuel : Nat),
      (e :: es).IsChain (fun x y ↦ ¬x.Short ∧
        (∃ x₁ ∈ blockComp L₀ x, ∃ S₁ ∈ x₁.letters.dedup.sublists, ∃ x₂ ∈ pairComp L₀ S₁ x₁,
          ∃ S₂ ∈ x₂.letters.dedup.sublists, y ∈ pairComp L₀ S₂ x₂) ∧ y.size ≤ bound) →
      ((e :: es).getLast (List.cons_ne_nil _ _)).Short →
      SolvedNaively ((e :: es).getLast (List.cons_ne_nil _ _)) → es.length < fuel →
      true ∈ wordEqSat L₀ bound fuel e
  | _, _, 0, _, _, _, hlen => absurd hlen (Nat.not_lt_zero _)
  | [], e, fuel + 1, _, hs, hm, _ => by
    simp only [List.getLast_singleton] at hs hm
    simpa [wordEqSat, hs, SolvedNaively] using hm
  | y :: es, e, fuel + 1, hchain, hs, hm, hlen => by
    obtain ⟨⟨hse, ⟨e₁, h₁, S₁, hS₁, e₂, h₂, S₂, hS₂, h₃⟩, hy⟩, hchain⟩ :=
      List.isChain_cons_cons.1 hchain
    rw [List.getLast_cons (List.cons_ne_nil _ _)] at hs hm
    have ih := wordEqSat_of_isChain es y fuel hchain hs hm (by simp at hlen; omega)
    unfold wordEqSat
    simp only [hse, ↓reduceIte, Guess.mem_bind]
    exact ⟨y, mem_phase.2 ⟨e₁, h₁, S₁, hS₁, e₂, h₂, S₂, hS₂, h₃⟩,
      by simpa only [hy, ↓reduceIte] using ih⟩

theorem eqnSat?_iff (e : Eqn Γ V) : eqnSat? e = true ↔ e.Solvable := by
  have hL : e.letterList.Nodup := nodup_freshList _ _
  have hlen : e.letterList.length = e.lengthBound + 6 * e.varCount := length_freshList _ _
  have hs := e.size_eq
  simp only [eqnSat?, Guess.any_eq_true, id, exists_eq_right]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (Eqn.renumber_solvable_iff hL (by simp only [Eqn.lengthBound] at hlen; omega)).1
      (wordEqSat_sound hL hlen.ge ?_ (Eqn.varCount_renumber _ e).le h)
    rw [Eqn.letterCount_renumber, Eqn.lengthBound]
    omega
  · obtain ⟨es, hlen', hchain, hs', hm⟩ := phases_reach_short h
    exact wordEqSat_of_isChain es _ _ hchain hs' hm (by simp only [Eqn.phaseBound]; omega)

end Accordion.WE.Decidability

end
