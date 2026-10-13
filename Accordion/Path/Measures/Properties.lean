module

public import Accordion.Path.Measures.Defs
public import Accordion.Path.Properties

@[expose] public section

namespace Accordion

namespace Path

variable {Γ : Type}


theorem isAnchored_app_iff (p : Path Γ) (c : Component Γ) :
    (Path.app p c).IsAnchored ↔
      p.IsAnchored ∧ 0 ≤ p.depth + c.depth := by
  constructor
  · exact fun h => ⟨fun q ⟨r, hr⟩ => h q ⟨.app r c, congrArg (Path.app · c) hr⟩, h _ ⟨.nil, rfl⟩⟩
  · rintro ⟨hp, hdepth⟩ q ⟨r, hr⟩
    cases r with
    | nil =>
        obtain rfl : Path.app p c = q := hr
        exact hdepth
    | app r d => exact hp q ⟨r, (Path.app.inj hr).1⟩

theorem depth_nonneg_of_isAnchored {p : Path Γ} (hp : p.IsAnchored) :
    0 ≤ p.depth :=
  hp p ⟨.nil, rfl⟩

theorem isAnchored_of_linear {p : Path Γ} (hp : p.Linear) :
    p.IsAnchored := by
  induction p with
  | nil =>
      rintro q ⟨r, hr⟩
      cases r <;> cases hr
      exact Int.le_refl 0
  | app p c ih =>
      cases c <;> simp [Path.Linear] at hp
      have := depth_nonneg_of_isAnchored (ih hp)
      exact (isAnchored_app_iff _ _).2 ⟨ih hp, by simp only [Component.depth]; omega⟩

@[simp] theorem depth_join (p q : Path Γ) :
    (p ++ q).depth = p.depth + q.depth := by
  induction q with
  | nil => simp [Path.join, depth]
  | app q c ih => exact (congrArg (· + c.depth) ih).trans (Int.add_assoc _ _ _)

@[simp] theorem depth_coe (a : Γ) : ((a : Path Γ)).depth = 1 := by
  simp [Path.init, depth, Component.depth]

@[simp] theorem isAnchored_descend (w : List Γ) : (descend w).IsAnchored :=
  isAnchored_of_linear (linear_descend w)

@[simp] theorem depth_descend (w : List Γ) : (descend w).depth = (List.length w : Int) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [descend, depth_join, depth_coe, ih, List.length_cons]
      omega

theorem length_names_of_linear {p : Path Γ} (hp : p.Linear) :
    List.length (names p) = p.length := by
  induction p with
  | nil => rfl
  | app p c ih =>
      cases c <;> simp [Path.Linear] at hp
      simp [names, Path.length, ih hp]

theorem IsAnchored.of_join_left {p q : Path Γ} (h : (p ++ q).IsAnchored) : p.IsAnchored := by
  rintro r ⟨s, hs⟩
  exact h r ⟨s ++ q, by rw [hs]; exact (join_assoc r s q).symm⟩

theorem IsAnchored.join_of_depth_le {p s i : Path Γ} (hp : p.IsAnchored)
    (h : (s ++ i).IsAnchored) (hle : s.depth ≤ p.depth) : (p ++ i).IsAnchored := by
  induction i with
  | nil => exact hp
  | app i c ih =>
      obtain ⟨h, hc⟩ := (isAnchored_app_iff (s ++ i) c).1 h
      rw [depth_join] at hc
      exact (isAnchored_app_iff (p ++ i) c).2 ⟨ih h, by rw [depth_join]; omega⟩

theorem IsAnchored.join {p q : Path Γ}
    (hp : p.IsAnchored) (hq : q.IsAnchored) :
    (p ++ q).IsAnchored :=
  hp.join_of_depth_le (s := ε) (by rwa [nil_join]) (depth_nonneg_of_isAnchored hp)

theorem isAnchored_join_iff_of_isBalanced {p s i : Path Γ}
    (hp : p.IsAnchored) (h : (s ++ i).IsBalanced) :
    (p ++ i).IsAnchored ↔ s.depth ≤ p.depth := by
  have hdepth := h.2
  refine ⟨fun hpi => ?_, hp.join_of_depth_le h.1⟩
  have := depth_nonneg_of_isAnchored hpi
  rw [depth_join] at hdepth this
  omega

private theorem length_dir (p : Path Γ) : p.dir.length = p.length - 1 := by
  cases p <;> rfl

theorem depth_eq_length_norm_of_isAnchored {p : Path Γ} (hp : p.IsAnchored) :
    p.depth = (p.norm.length : Int) := by
  induction p with
  | nil => rfl
  | app p c ih =>
      obtain ⟨hp, hc⟩ := (isAnchored_app_iff p c).1 hp
      have := ih hp
      cases c <;> simp only [Path.norm, depth, length, Component.depth, length_dir] at hc ⊢ <;>
        omega

theorem norm_join_of_isAnchored_right (p : Path Γ) {q : Path Γ}
    (hq : q.IsAnchored) :
    (p ++ q).norm = p.norm ++ q.norm := by
  induction q with
  | nil => rfl
  | app q c ih =>
      obtain ⟨hq', hc⟩ := (isAnchored_app_iff q c).1 hq
      have hi := ih hq'
      cases c with
      | parent =>
          have hlen := depth_eq_length_norm_of_isAnchored hq'
          change (p ++ q).norm.dir = p.norm ++ q.norm.dir
          rw [hi]
          cases hn : q.norm with
          | nil =>
              simp only [hn, length, Component.depth] at hlen hc
              omega
          | app _ _ => rfl
      | _ => simpa [Path.join, Path.norm] using hi

private theorem norm_eq_nil_of_isBalanced {p : Path Γ} (hp : p.IsBalanced) : p.norm = ε := by
  have h := depth_eq_length_norm_of_isAnchored hp.1
  rw [hp.2] at h
  cases hn : p.norm with
  | nil => rfl
  | app q c =>
      rw [hn, length] at h
      omega

private theorem norm_join_eq_norm_of_not_isAnchored (a : Γ) {p : Path Γ}
    (hp : ¬p.IsAnchored) :
    p.norm = ((a : Path Γ) ++ p).norm := by
  induction p with
  | nil => exact absurd (isAnchored_of_linear (p := ε) trivial) hp
  | app p c ih =>
      by_cases hpa : p.IsAnchored
      · have hdepth := depth_nonneg_of_isAnchored hpa
        have hc : ¬0 ≤ p.depth + c.depth := fun h => hp ((isAnchored_app_iff p c).2 ⟨hpa, h⟩)
        cases c <;> simp only [Component.depth] at hc <;> try omega
        change p.norm.dir = ((a : Path Γ) ++ p).norm.dir
        rw [norm_join_of_isAnchored_right _ hpa, norm_eq_nil_of_isBalanced ⟨hpa, by omega⟩]
        rfl
      · cases c <;> simp [Path.join, Path.norm, ih hpa]

theorem isAnchored_iff_norm_ne_norm_join (a : Γ) (p : Path Γ) :
    p.IsAnchored ↔
      p.norm ≠ ((a : Path Γ) ++ p).norm := by
  refine ⟨fun hp heq => ?_, fun hne =>
    Classical.byContradiction fun hp => hne (norm_join_eq_norm_of_not_isAnchored a hp)⟩
  have hdepth := congrArg depth heq
  rw [norm_join_of_isAnchored_right _ hp, depth_join] at hdepth
  simp only [Path.norm, Path.init, depth, Component.depth] at hdepth
  omega

theorem isBalanced_iff_norm_eq_nil_and_norm_join_ne_nil
    (a : Γ) (p : Path Γ) :
    p.IsBalanced ↔
      p.norm = ε ∧
        ((a : Path Γ) ++ p).norm ≠ ε := by
  constructor
  · intro hp
    have hnorm := norm_eq_nil_of_isBalanced hp
    exact ⟨hnorm, fun h => (isAnchored_iff_norm_ne_norm_join a p).1 hp.1 (hnorm.trans h.symm)⟩
  · rintro ⟨hnorm, hpref⟩
    have hp := (isAnchored_iff_norm_ne_norm_join a p).2 fun heq => hpref (heq ▸ hnorm)
    have hdepth := depth_eq_length_norm_of_isAnchored hp
    rw [hnorm] at hdepth
    exact ⟨hp, hdepth⟩

end Path

end Accordion

end
