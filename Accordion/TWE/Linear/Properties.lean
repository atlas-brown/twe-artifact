module

public import Accordion.TWE.Linear
public import Accordion.TWE.Fresh.Properties

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

namespace Path

theorem mem_subterms_self (p : TWE.Path Γ V) : p ∈ p.subterms := by
  cases p <;> simp [subterms]

theorem mem_subterms_trans {p q r : TWE.Path Γ V} (hq : q ∈ p.subterms) (hr : r ∈ q.subterms) :
    r ∈ p.subterms := by
  induction p with
  | join p₁ p₂ ih₁ ih₂ =>
      simp only [subterms, List.mem_cons, List.mem_append, or_assoc] at hq ⊢
      rcases hq with rfl | hq | hq
      · simpa [subterms] using hr
      · exact .inr (.inl (ih₁ hq))
      · exact .inr (.inr (ih₂ hq))
  | norm p ih =>
      simp only [subterms, List.mem_cons] at hq ⊢
      rcases hq with rfl | hq
      · simpa [subterms] using hr
      · exact .inr (ih hq)
  | _ => simp_all [subterms]

theorem free_subset_of_mem_subterms [TWE.Vars.Comparable V] {P Q : TWE.Path Γ V}
    (h : Q ∈ P.subterms) : Q.free ⊆ P.free := by
  induction P with
  | join P₁ P₂ ih₁ ih₂ =>
      simp only [subterms, List.mem_cons, List.mem_append] at h
      rcases h with (rfl | h) | h
      · exact Free.Subset.refl _
      · exact Free.Subset.trans (ih₁ h) Free.subset_union_left
      · exact Free.Subset.trans (ih₂ h) Free.subset_union_right
  | norm P ih =>
      simp only [subterms, List.mem_cons] at h
      rcases h with rfl | h
      · exact Free.Subset.refl _
      · exact ih h
  | _ =>
      simp only [subterms, List.mem_singleton] at h
      exact h ▸ Free.Subset.refl _

end Path

namespace Formula

theorem mem_paths_of_mem_subterms {φ : TWE.Formula Γ V} {p q : TWE.Path Γ V}
    (hp : p ∈ φ.paths) (hq : q ∈ p.subterms) : q ∈ φ.paths := by
  induction φ with
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      simp only [paths, List.mem_append] at hp ⊢
      exact hp.imp ihφ ihψ
  | neg φ ih => exact ih hp
  | atom a =>
      cases a <;> simp only [paths, List.mem_append] at hp ⊢
      all_goals first
        | exact Path.mem_subterms_trans hp hq
        | exact hp.imp (Path.mem_subterms_trans · hq) (Path.mem_subterms_trans · hq)
        | simp at hp
  | top | bot => simp [paths] at hp

theorem free_subset_of_mem_paths [TWE.Vars.Comparable V] {φ : TWE.Formula Γ V}
    {P : TWE.Path Γ V} (h : P ∈ φ.paths) : P.free ⊆ φ.free := by
  induction φ with
  | atom a =>
      cases a with
      | pathEq Q R =>
          rcases List.mem_append.1 h with h | h
          · exact Free.Subset.trans (Path.free_subset_of_mem_subterms h) Free.subset_union_left
          · exact Free.Subset.trans (Path.free_subset_of_mem_subterms h) Free.subset_union_right
      | pathIsLin Q => exact Path.free_subset_of_mem_subterms h
      | treeWalk Q T ℓ =>
          exact Free.Subset.trans (Path.free_subset_of_mem_subterms h)
            (Free.Subset.trans Free.subset_union_right Free.subset_union_left)
      | _ => simp [paths] at h
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      rcases List.mem_append.1 h with h | h
      · exact Free.Subset.trans (ihφ h) Free.subset_union_left
      · exact Free.Subset.trans (ihψ h) Free.subset_union_right
  | neg φ ih => exact ih h
  | _ => simp [paths] at h

end Formula

end TWE

end Accordion

end
