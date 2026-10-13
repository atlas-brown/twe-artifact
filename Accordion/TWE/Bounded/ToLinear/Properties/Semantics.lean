module

public import Accordion.TWE.Bounded.ToLinear.Properties.Defs
public import Accordion.TWE.Bounded.Properties
public import Accordion.TWE.Linear.ToWE.Properties.Trees

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open scoped Accordion.Formula Linear.ToWE.BigConnectives Linear.ToWE.WordModel
open Linear.ToWE (WordModel WordModel.evalPath)
open WE (GroundWord)

variable {Γ : Type} {V : TWE.Vars}

-- Paths are concatenated with `++` throughout, so that `Accordion.Path.join_assoc` applies.
attribute [-simp] Accordion.Path.append_eq

section Sat

variable [Ord Γ] (M : WordModel Γ V)

@[simp] theorem satAtom_pathEq [DecidableEq Γ] {P Q : TWE.Path Γ V} (hP : P.hasLinearConstants)
    (hQ : Q.hasLinearConstants) :
    M.toTWE.satAtom (.pathEq P Q) ↔ WordModel.evalPath M P = WordModel.evalPath M Q :=
  Linear.ToWE.sat_toTWE_pathEq_iff M hP hQ

end Sat

theorem Decomposition.eval_var [Ord Γ] [TWE.Vars.Comparable V] (δ : VariableDecomposition V)
    (M : WordModel Γ V) (X : V.Path) :
    Decomposition.eval M (.var (δ.path X)) = (sourceModel δ M).σPath X := by
  simp only [Decomposition.eval, Decomposition.restWords, Decomposition.var, sourceModel,
    List.map_map]
  rfl

section SourceModel

variable [Ord Γ] [TWE.Vars.Comparable V] (δ : VariableDecomposition V) (M : WordModel Γ V)

theorem wf_sourceModel : (sourceModel δ M).WF :=
  ⟨fun _ ↦ Path.linear_descend _, fun T ↦ (M.θ T).2⟩

@[simp] theorem σLoc_sourceModel (ℓ : V.Loc) :
    (sourceModel δ M).σLoc ℓ = (M.σLoc ℓ : Accordion.Path Γ) := rfl

theorem evalName_sourceModel (A : TWE.Name Γ V) :
    (sourceModel δ M).evalName A = M.toTWE.evalName A := by
  cases A <;> rfl

theorem evalTree_sourceModel (T : TWE.Tree V) :
    (sourceModel δ M).evalTree T = M.toTWE.evalTree T := by
  induction T <;> simp_all [TWE.Model.evalTree]
  rfl

theorem evalNameSet_sourceModel [DecidableEq Γ] (S : TWE.Set Γ V) :
    (sourceModel δ M).evalNameSet S = M.toTWE.evalNameSet S := by
  induction S <;>
    simp_all [TWE.Model.evalNameSet, evalName_sourceModel, evalTree_sourceModel]
  rfl

theorem eqOn_sourceModel {M M' : WordModel Γ V} {U U' : TWE.Free V} (h : M ≡[U] M')
    (hU : U' ⊆ U) (hδ : δ.free ⊆ U) :
    TWE.Model.EqOn (sourceModel δ M) (sourceModel δ M') U' := by
  have blocks : ∀ X ∈ U'.path, ∀ Y, Y = (δ.path X).1 ∨ Y ∈ (δ.path X).2.map Prod.snd →
      M.σPath Y = M'.σPath Y := by
    intro X hX Y hY
    refine h.2.2.1 (Finset.mem_coe.2 ?_)
    unfold VariableDecomposition.path at hY
    cases hl : δ.paths.lookup X with
    | none =>
        simp only [hl, Option.getD_none, List.map_nil, List.not_mem_nil, or_false] at hY
        exact hY ▸ hU.2.2.1 hX
    | some b =>
        simp only [hl, Option.getD_some] at hY
        refine hδ.2.2.1 (List.mem_toFinset.2 (List.mem_flatMap.2 ⟨(X, b), ?_, ?_⟩))
        · obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.1 hl
          simp [e]
        · simpa using hY
  refine ⟨fun x hx ↦ h.1 (hU.1 hx), fun x hx ↦ ?_, fun X hX ↦ ?_, fun ℓ hℓ ↦ ?_,
    fun x hx ↦ h.2.2.2.2.1 (hU.2.2.2.2.1 hx), fun x hx ↦ ?_⟩
  · simp only [sourceModel, h.2.1 (hU.2.1 hx)]
  · simp only [sourceModel]
    rw [blocks X hX _ (.inl rfl)]
    congr 1
    exact List.map_congr_left fun p hp ↦ by
      rw [blocks X hX p.2 (.inr (List.mem_map_of_mem hp))]
  · exact congrArg Path.descend (h.2.2.2.1 (hU.2.2.2.1 hℓ))
  · exact congrArg Subtype.val (h.2.2.2.2.2 (hU.2.2.2.2.2 hx))

end SourceModel

theorem splitComponents_names (w : List Γ) (cs : List (Accordion.Component Γ)) :
    splitComponents (w.map .name ++ cs) =
      (w ++ (splitComponents cs).1, (splitComponents cs).2) := by
  induction w <;> simp_all [splitComponents]

theorem splitComponents_blocksPath (w : List Γ) (r : List (Step × List Γ)) :
    splitComponents (blocksPath w r).components = (w, r) := by
  induction r generalizing w with
  | nil =>
      simpa [blocksPath, Path.components_descend, splitComponents] using
        splitComponents_names w ([] : List (Accordion.Component Γ))
  | cons p r ih =>
      obtain ⟨C, w'⟩ := p
      simp only [blocksPath, Accordion.Path.components_join, Path.components_descend]
      cases C <;> simp [Step.toComponent, Accordion.Path.init, Accordion.Path.components,
        splitComponents_names, splitComponents, ih]

theorem blocksPath_eq_blocksPath_iff {w w' : List Γ} {r r' : List (Step × List Γ)} :
    blocksPath w r = blocksPath w' r' ↔ w = w' ∧ r = r' := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simpa [splitComponents_blocksPath] using congrArg (splitComponents ·.components) h

theorem Decomposition.eval_eq_iff [Ord Γ] (M : WordModel Γ V) (d d' : Decomposition Γ V) :
    d.eval M = d'.eval M ↔
      d.steps = d'.steps ∧
        ∀ B ∈ d.blocks.zip d'.blocks, WordModel.evalPath M B.1 = WordModel.evalPath M B.2 := by
  simp only [eval, blocksPath_eq_blocksPath_iff, restWords, steps, blocks, List.zip_cons_cons,
    List.forall_mem_cons]
  suffices ∀ r r' : List (Step × TWE.Path Γ V),
      r.map (fun p ↦ (p.1, M.evalPath p.2)) = r'.map (fun p ↦ (p.1, M.evalPath p.2)) ↔
        r.map Prod.fst = r'.map Prod.fst ∧ ∀ B ∈ (r.map Prod.snd).zip (r'.map Prod.snd),
          WordModel.evalPath M B.1 = WordModel.evalPath M B.2 by
    rw [this]; tauto
  intro r r'
  induction r generalizing r' <;> cases r' <;> simp_all [and_assoc, and_left_comm]

theorem nonlinearCount_blocksPath (w : List Γ) (r : List (Step × List Γ)) :
    (blocksPath w r).nonlinearCount = r.length := by
  induction r generalizing w with
  | nil => simp [blocksPath, Path.nonlinearCount_descend]
  | cons p r ih =>
      obtain ⟨C, w'⟩ := p
      cases C <;> simp [blocksPath, Accordion.Path.nonlinearCount_join,
        Path.nonlinearCount_descend, ih, Step.toComponent, Accordion.Path.init,
        Accordion.Path.nonlinearCount, Nat.add_comm]

theorem blocksPath_append (u v : List Γ) (r : List (Step × List Γ)) :
    blocksPath (u ++ v) r = Path.descend u ++ blocksPath v r := by
  cases r <;> simp [blocksPath, Accordion.Path.join_assoc]

theorem Decomposition.eval_append [Ord Γ] (M : WordModel Γ V) (d d' : Decomposition Γ V) :
    (d.append d').eval M = d.eval M ++ d'.eval M := by
  obtain ⟨B, r⟩ := d
  cases r with
  | nil => simp [append, eval, restWords, blocksPath, WordModel.evalPath, blocksPath_append]
  | cons p r =>
      simp only [append, eval, restWords, List.map_append]
      induction r generalizing p B with
      | nil =>
          simp [appendToLast, blocksPath, WordModel.evalPath, blocksPath_append,
            Accordion.Path.join_assoc]
      | cons q r ih => simp [appendToLast, blocksPath, ih p.2 q, Accordion.Path.join_assoc]

theorem norm_descend_join_toComponent (w : List Γ) (C : Step) :
    (Path.descend w ++ .init C.toComponent).norm = Path.descend (C.apply w) := by
  have dir_descend : (Path.descend w).dir = Path.descend w.dropLast := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a _ =>
        rw [Path.descend_append_singleton, List.dropLast_concat]
        rfl
  cases C <;> simp [Step.toComponent, Step.apply, Accordion.Path.init, Accordion.Path.append_eq,
    Accordion.Path.norm, Accordion.Path.join, dir_descend]

theorem norm_blocksPath (w : List Γ) (r : List (Step × List Γ)) :
    (blocksPath w r).norm = Path.descend (normalWord w r) := by
  induction r generalizing w with
  | nil => simp [blocksPath, normalWord]
  | cons p r ih =>
      rw [blocksPath, Accordion.Path.norm_join_eq_norm_norm_join, norm_descend_join_toComponent,
        ← blocksPath_append, ih]
      rfl

end ToLinear

end Bounded

end TWE

end Accordion

end
