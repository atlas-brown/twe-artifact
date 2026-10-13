module

public import Accordion.Path.StrictPrefix

@[expose] public section

namespace Accordion

namespace Path

variable {Γ : Type}

-- Statements use `++` but proofs unfold `join`; being `simp`, this makes `join` the normal form.
@[simp] theorem append_eq (p q : Path Γ) : p ++ q = p.join q := rfl

theorem join_assoc (p q r : Path Γ) :
    p ++ (q ++ r) = (p ++ q) ++ r := by
  induction r with
  | nil => rfl
  | app r c ih =>
      simp only [append_eq] at ih
      simp [Path.join, ih]

theorem join_linear {p q : Path Γ} (hp : p.Linear) (hq : q.Linear) :
    (p ++ q).Linear := by
  induction q with
  | nil => simpa [Path.join]
  | app q c ih =>
      cases c with
      | name a => exact ih hq
      | empty => exact absurd hq (by simp [Path.Linear])
      | self => exact absurd hq (by simp [Path.Linear])
      | parent => exact absurd hq (by simp [Path.Linear])

theorem linear_dir {p : Path Γ} (hp : p.Linear) : p.dir.Linear := by
  cases p with
  | nil => simp [Path.dir, Path.Linear]
  | app p c =>
      cases c <;> simp [Path.Linear] at hp
      simpa [Path.dir] using hp

@[simp] theorem linear_norm (p : Path Γ) : p.norm.Linear := by
  induction p with
  | nil => simp [Path.norm, Path.Linear]
  | app p c ih =>
      cases c <;> simp [Path.norm, Path.Linear, ih, linear_dir ih]

theorem norm_eq_self_of_linear {p : Path Γ} (hp : p.Linear) : p.norm = p := by
  induction p with
  | nil => rfl
  | app p c ih =>
      cases c <;> simp [Path.Linear] at hp
      simp [Path.norm, ih hp]

theorem norm_join_eq_norm_norm_join (p q : Path Γ) : (p ++ q).norm = (p.norm ++ q).norm := by
  induction q with
  | nil => exact (norm_eq_self_of_linear (linear_norm p)).symm
  | app q c ih =>
      simp only [append_eq] at ih ⊢
      cases c <;> simp [Path.join, Path.norm, ih]

@[simp] theorem nil_join (p : Path Γ) : (ε : Path Γ) ++ p = p := by
  induction p with
  | nil => rfl
  | app p c ih =>
      simp only [append_eq] at ih
      simp [Path.join, ih]

theorem components_join (p q : Path Γ) :
    (p ++ q).components = p.components ++ q.components := by
  induction q with
  | nil => simp [Path.join, components]
  | app q c ih =>
      simp only [append_eq] at ih
      simp [Path.join, components, ih]

theorem eq_of_components_eq {p q : Path Γ} (h : p.components = q.components) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [components]
  | app p c ih =>
      cases q with
      | nil => simp [components] at h
      | app q d =>
          obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
          rw [ih h₁, List.singleton_inj.1 h₂]

@[simp] theorem linear_descend (w : List Γ) : (descend w).Linear := by
  induction w with
  | nil => simp [descend, Path.Linear]
  | cons a w ih => exact join_linear (p := (a : Path Γ)) trivial ih

@[simp] theorem norm_descend (w : List Γ) : (descend w).norm = descend w :=
  norm_eq_self_of_linear (linear_descend w)

@[simp] theorem descend_append (u v : List Γ) :
    descend (u ++ v) = descend u ++ descend v := by
  induction u with
  | nil => exact (nil_join _).symm
  | cons a u ih =>
      rw [List.cons_append, descend, descend, ih]
      exact join_assoc _ _ _

theorem descend_append_singleton (w : List Γ) (a : Γ) :
    descend (w ++ [a]) = .app (descend w) (.name a) :=
  descend_append w [a]

theorem components_descend (w : List Γ) :
    (descend w).components = w.map Component.name := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [descend, components_join, ih]; rfl

theorem names_join (p q : Path Γ) : names (p ++ q) = names p ++ names q := by
  induction q with
  | nil => exact (List.append_nil _).symm
  | app q c ih =>
      change names (Path.app (p ++ q) c) = names p ++ names (Path.app q c)
      cases c <;> simp only [names, ih, List.append_assoc]

@[simp] theorem names_descend (w : List Γ) : names (descend w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [descend, names_join, ih]
      rfl

theorem descend_names_of_linear {p : Path Γ} (hp : p.Linear) :
    descend p.names = p := by
  induction p with
  | nil => rfl
  | app p c ih =>
      cases c <;> simp [Path.Linear] at hp
      rw [names, descend_append, ih hp]
      rfl

theorem descend_injective : Function.Injective (descend (Γ := Γ)) := fun u v h =>
  (names_descend u).symm.trans ((congrArg names h).trans (names_descend v))

theorem IsStrictPrefix.exists_eq_join_app {q p : Path Γ} (h : q.IsStrictPrefix p) :
    ∃ (r : Path Γ) (c : Component Γ), p = q ++ r.app c := by
  induction h with
  | self c => exact ⟨ε, c, rfl⟩
  | step c _ ih =>
      obtain ⟨r, c', rfl⟩ := ih
      exact ⟨Path.app r c', c, rfl⟩

end Path

end Accordion

end
