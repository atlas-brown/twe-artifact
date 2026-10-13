module

public import Accordion.TWE.Bounded.ToLinear.Properties.Semantics

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open Linear.ToWE (WordModel evalTree_canonical σLoc_toTWE)
open WE (GroundWord)
open FileTree (Zipper)

variable {Γ : Type} {V : TWE.Vars}

-- As in `Semantics.lean`: paths are concatenated with `++`.
attribute [-simp] Accordion.Path.append_eq

section Traverse

variable [Ord Γ] {base : FileTree Γ}

theorem move_toComponent (C : Step) (z : Zipper Γ) :
    Zipper.move C.toComponent z =
      if z.focus.shape = .dirc then some (if C = .parent then z.up else z) else none := by
  obtain ⟨_, focus⟩ := z
  cases focus with
  | abst => cases C <;> rfl
  | tree τ => cases τ <;> cases C <;> rfl

variable [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

theorem traverse_step (hbase : base.Canonical) (w : List Γ) (C : Step) :
    Zipper.traverse (Path.descend w ++ .init C.toComponent) (Zipper.zip base) =
      if IsDir base w then Zipper.traverse (Path.descend (C.apply w)) (Zipper.zip base)
      else none := by
  have step : ∀ z : Zipper Γ,
      Zipper.traverse (.init C.toComponent) z = Zipper.move C.toComponent z := fun _ ↦ rfl
  have walked := FileTree.Zipper.traverse_join (Path.descend w)
    (.init C.toComponent : Accordion.Path Γ) (Zipper.zip base)
  cases h : Zipper.traverse (Path.descend w) (Zipper.zip base) with
  | none => simp [walked, IsDir, h]
  | some z =>
      by_cases dir : z.focus.shape = .dirc
      · have walked' : Zipper.traverse (Path.descend w ++ .init C.toComponent)
            (Zipper.zip base) = some (if C = .parent then z.up else z) := by
          rw [walked, h, Option.bind_some, step, move_toComponent, ite_eq_left dir]
        generalize (if C = .parent then z.up else z) = z' at walked'
        have path := FileTree.path_eq_norm_of_resolve (τ := base)
          (p := Path.descend w ++ .init C.toComponent) (C := z'.frames.ctx) (f := z'.focus)
          (by simp [FileTree.resolve, walked'])
        rw [norm_descend_join_toComponent] at path
        simp only [IsDir, h, Option.map_some, dir, ite_true]
        rw [walked', ← path, FileTree.Zipper.traverse_idem hbase _ _ walked']
      · simp [walked, h, step, move_toComponent, dir, IsDir]

theorem traverse_blocksPath (hbase : base.Canonical) (w : List Γ) (r : List (Step × List Γ)) :
    Zipper.traverse (blocksPath w r) (Zipper.zip base) =
      if ∀ y ∈ prefixWords w r, IsDir base y then
        Zipper.traverse (Path.descend (normalWord w r)) (Zipper.zip base) else none := by
  induction r generalizing w with
  | nil => simp [blocksPath, prefixWords, normalWord]
  | cons p r ih =>
      obtain ⟨C, w'⟩ := p
      rw [blocksPath, FileTree.Zipper.traverse_join, traverse_step hbase]
      by_cases dir : IsDir base w
      · simp [dir, prefixWords, normalWord, ← FileTree.Zipper.traverse_join,
          ← blocksPath_append, ih]
      · simp [dir, prefixWords]

end Traverse

theorem sat_treeWalk_sourceModel_iff [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] (δ : VariableDecomposition V) (M : WordModel Γ V)
    {P : TWE.Path Γ V} {w : List Γ} {r : List (Step × List Γ)}
    (hP : (sourceModel δ M).evalPath P = blocksPath w r) (T : TWE.Tree V) (ℓ : V.Loc)
    {Ys : List V.Loc} {Y : V.Loc} (hYs : Ys.map M.σLoc = prefixWords w r)
    (hY : M.σLoc Y = normalWord w r) :
    (M.toTWE.satAtom (.treeWalk (.loc Y) T ℓ) ∧
        ∀ Yᵢ ∈ Ys, M.toTWE.satAtom (.treeShape (T[Yᵢ]) .dirc)) ↔
      (sourceModel δ M).satAtom (.treeWalk P T ℓ) := by
  match h : M.toTWE.evalTree T with
  | some (.tree base) =>
      have dirs : ∀ Yᵢ, M.toTWE.satAtom (.treeShape (T[Yᵢ]) .dirc) ↔ IsDir base (M.σLoc Yᵢ) := by
        intro Yᵢ
        cases ht : Zipper.traverse (Path.descend (M.σLoc Yᵢ)) (Zipper.zip base) <;>
          simp [TWE.Model.satAtom, TWE.Model.evalTree, h, FileTree.Focus.resolve,
            FileTree.resolve, IsDir, ht]
      simp only [dirs]
      rw [← List.forall_mem_map (f := M.σLoc) (P := IsDir base), hYs]
      have hY' : M.toTWE.evalPath (.loc Y) = Path.descend (normalWord w r) := by
        simp [TWE.Model.evalPath, hY]
      simp only [TWE.Model.satAtom, evalTree_sourceModel, hP, hY', h, σLoc_sourceModel,
        σLoc_toTWE, FileTree.resolve, traverse_blocksPath (evalTree_canonical M h)]
      by_cases all : ∀ y ∈ prefixWords w r, IsDir base y
      · rw [ite_eq_left all]
        exact and_iff_left all
      · simp [all]
  | none | some .abst =>
      simp [TWE.Model.satAtom, evalTree_sourceModel, h]

end ToLinear

end Bounded

end TWE

end Accordion

end
