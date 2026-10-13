module

public import Accordion.TWE.Linear.ToWE.Properties.EncodeSets

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Guess WordModel Accordion.Formula BigConnectives

variable {Γ : Type} {V : TWE.Vars}

section Run

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem run_reifyShapes (β : Conj Γ V) (W : TWE.Free V) :
    ((reifyShapes β).run W).1 =
      (⋀ F ∈ β.words, F) ⋏
        ((⋀ p ∈ β.baseShapes ×ˢ β.baseShapes, if p.1.tree = p.2.tree ∧ p.1.shape ≠ p.2.shape
            then p.1.query ≠̇ p.2.query else ⊤) ⋏
          ⋀ F ∈ (((β.baseShapes ×ˢ β.baseShapes).mapM leafPairFormula).run W).1, F) :=
  rfl

theorem subset_leafPairFormula (p : BaseShapeAssertion Γ V × BaseShapeAssertion Γ V)
    (W : TWE.Free V) : W ⊆ ((leafPairFormula p).run W).2 := by
  unfold leafPairFormula
  split
  · exact subset_notStrictPrefixFormula _ _ W
  · exact Free.Subset.refl W

end Run

section Realising

variable [Ord Γ] (m : WordModel Γ V) (A : List (BaseShapeAssertion Γ V))

theorem functionalConsistency_iff :
    FunctionalConsistency (evalBaseShapeAssertions m A) ↔
      ∀ p ∈ A ×ˢ A, p.1.tree = p.2.tree → p.1.shape ≠ p.2.shape →
        m.toWE.evalWord p.1.query ≠ m.toWE.evalWord p.2.query := by
  constructor
  · intro h p hp htree hshape heq
    exact hshape (h _ (List.mem_map_of_mem (List.mem_product.1 hp).1) _
      (List.mem_map_of_mem (List.mem_product.1 hp).2) htree heq)
  · intro h l hl r hr htree heq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
    by_contra hshape
    exact h (a, b) (List.mem_product.2 ⟨ha, hb⟩) htree hshape heq

theorem leafCondition_iff :
    LeafCondition (evalBaseShapeAssertions m A) ↔
      ∀ p ∈ A ×ˢ A, p.1.tree = p.2.tree → p.1.shape ≠ .dirc →
        ¬(m.toWE.evalWord p.1.query <+: m.toWE.evalWord p.2.query ∧
          m.toWE.evalWord p.1.query ≠ m.toWE.evalWord p.2.query) := by
  constructor
  · intro h p hp htree hshape
    exact h _ (List.mem_map_of_mem (List.mem_product.1 hp).1) hshape _
      (List.mem_map_of_mem (List.mem_product.1 hp).2) htree
  · intro h l hl hshape r hr htree
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
    exact h (a, b) (List.mem_product.2 ⟨ha, hb⟩) htree hshape

variable [DecidableEq Γ]

theorem Conj.sat_iff_of_setsEncoded (β : Conj Γ V) (hβ : ∀ α ∈ β, α.SetsEncoded) :
    Conj.sat m β ↔
      (∀ F ∈ β.words, m.toWE ⊨ F) ∧ BaseShapeAssertionsSat m β.baseShapes := by
  constructor
  · intro hsat
    exact ⟨fun F hF ↦ hsat _ (Conj.mem_words.1 hF), fun s hs ↦ hsat _ (Conj.mem_baseShapes.1 hs)⟩
  · rintro ⟨hwords, hshapes⟩ α hα
    have := hβ α hα
    rcases α with F | ⟨_ | _, ℓ, h⟩ | _ | _ | _ | _ <;> simp [Atom.SetsEncoded] at this
    · exact hwords F (Conj.mem_words.2 hα)
    · exact hshapes ⟨_, ℓ, h⟩ (Conj.mem_baseShapes.2 hα)

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

theorem satFresh_reifyShapes_iff (β : Conj Γ V) (hβ : ∀ α ∈ β, α.SetsEncoded)
    {W : TWE.Free V} (hW : β.free ⊆ W) :
    Guess.satFresh m W ⌜((reifyShapes β).run W).1⌝ ↔
      ∃ θ, Conj.sat (m.withTrees θ) β := by
  have hpairs : ∀ p ∈ β.baseShapes ×ˢ β.baseShapes, Word.free p.1.query ⊆ W ∧
      Word.free p.2.query ⊆ W := fun p hp ↦
    ⟨(free_subset_of_mem_baseShapes hW (List.mem_product.1 hp).1).2,
      (free_subset_of_mem_baseShapes hW (List.mem_product.1 hp).2).2⟩
  have hwords : ∀ m', m ≡[W] m' → (m'.toWE ⊨ (⋀ F ∈ β.words, F : WordFormula Γ V) ↔
      ∀ F ∈ β.words, m.toWE ⊨ F) := fun m' hm ↦ by
    rw [sat_all]
    exact forall₂_congr fun F hF ↦ (sat_wordFormula_congr hm
      (Free.Subset.trans (Atom.free_subset_of_mem (Conj.mem_words.1 hF)) hW)).symm
  have hfunctional : ∀ m', m ≡[W] m' →
      (m'.toWE ⊨ (⋀ p ∈ β.baseShapes ×ˢ β.baseShapes,
          if p.1.tree = p.2.tree ∧ p.1.shape ≠ p.2.shape then p.1.query ≠̇ p.2.query else ⊤ :
            WordFormula Γ V) ↔
        ∀ p ∈ β.baseShapes ×ˢ β.baseShapes, p.1.tree = p.2.tree → p.1.shape ≠ p.2.shape →
          m.toWE.evalWord p.1.query ≠ m.toWE.evalWord p.2.query) := fun m' hm ↦ by
    rw [sat_all]
    refine forall₂_congr fun p hp ↦ ?_
    split
    · next h =>
      simp [h.1, h.2, evalWord_congr hm (hpairs p hp).1, evalWord_congr hm (hpairs p hp).2]
    · next h => exact iff_of_true trivial fun htree hshape ↦ absurd ⟨htree, hshape⟩ h
  have hleaves := Guess.satFresh_mapM_iff (fun F : WordFormula Γ V ↦ (⌜F⌝ : Guess (Conj Γ V)))
    leafPairFormula
    (fun m p ↦ p.1.tree = p.2.tree → p.1.shape ≠ .dirc →
      ¬(m.toWE.evalWord p.1.query <+: m.toWE.evalWord p.2.query ∧
        m.toWE.evalWord p.1.query ≠ m.toWE.evalWord p.2.query))
    subset_leafPairFormula (U₀ := W) (xs := β.baseShapes ×ˢ β.baseShapes)
    (fun p hp W' hW' ↦ by
      unfold leafPairFormula
      split
      · exact Guess.AllAtoms.inject (free_notStrictPrefixFormula_subset
          (Free.Subset.trans (hpairs p hp).1 hW') (Free.Subset.trans (hpairs p hp).2 hW'))
      · exact Guess.AllAtoms.inject (TWE.Free.empty_subset _))
    (fun p hp {U' W'} m' hU' hW' ↦ by
      unfold leafPairFormula
      simp only [Guess.satFresh, InjectAtom.inject_guess, Guess.sat_atom, Atom.sat]
      split
      · next h =>
        rw [exists_sat_notStrictPrefixFormula_iff m' hW' (Free.Subset.trans (hpairs p hp).1 hU')
          (Free.Subset.trans (hpairs p hp).2 hU')]
        simp [h.1, h.2]
      · next h =>
        exact iff_of_true ⟨m', .refl m' U', trivial⟩ fun htree hshape ↦ absurd ⟨htree, hshape⟩ h)
    m (Free.Subset.refl W) (Free.Subset.refl W)
  simp only [Guess.satFresh, Guess.sat_all, InjectAtom.inject_guess, Guess.sat_atom,
    Atom.sat] at hleaves
  have htoWE : ∀ θ, (m.withTrees θ).toWE = m.toWE := fun _ ↦ rfl
  rw [run_reifyShapes]
  simp only [Conj.sat_iff_of_setsEncoded _ β hβ, htoWE, exists_and_left, Guess.satFresh,
    InjectAtom.inject_guess, Guess.sat_atom]
  rw [baseTreeRealisation_iff, functionalConsistency_iff, leafCondition_iff]
  constructor
  · rintro ⟨m', hm, hw, hf, hl⟩
    exact ⟨(hwords m' hm).1 hw, (hfunctional m' hm).1 hf,
      hleaves.1 ⟨m', hm, (sat_all _ _ _).1 hl⟩⟩
  · rintro ⟨hw, hf, hl⟩
    obtain ⟨m', hm, hl⟩ := hleaves.2 hl
    exact ⟨m', hm, show _ ∧ _ ∧ _ from
      ⟨(hwords m' hm).2 hw, (hfunctional m' hm).2 hf, (sat_all _ _ _).2 hl⟩⟩

end Realising

theorem exists_SAT_map_reifyShapes_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] {D : Guess (Conj Γ V)}
    (hD : ∀ β ∈ D, ∀ α ∈ β, α.SetsEncoded) :
    (∃ ψ ∈ D.map (rewriteConj reifyShapes), WE.Formula.SAT ψ) ↔ D.SAT := by
  have hcorrect := fun β (hβ : β ∈ D) m ↦
    satFresh_reifyShapes_iff m β (hD β hβ) (Free.Subset.refl β.free)
  rw [Guess.SAT_iff_exists]
  simp only [Guess.mem_map', exists_exists_and_eq_and]
  refine exists_congr fun β ↦ and_congr_right fun hβ ↦ ⟨fun ⟨target, hreified⟩ ↦ ?_,
    fun ⟨m, hsat⟩ ↦ ?_⟩
  · rw [← toWE_sourceSkeleton target] at hreified
    obtain ⟨θ, hsat⟩ := (hcorrect β hβ (sourceSkeleton target)).1
      (Guess.satFresh_of_sat ((Guess.sat_atom _).2 hreified))
    exact ⟨_, hsat⟩
  · obtain ⟨m', -, hreified⟩ := (hcorrect β hβ m).2 ⟨m.θ, hsat⟩
    rw [InjectAtom.inject_guess, Guess.sat_atom] at hreified
    exact ⟨_, hreified⟩

end ToWE

end Linear

end TWE

end Accordion

end
