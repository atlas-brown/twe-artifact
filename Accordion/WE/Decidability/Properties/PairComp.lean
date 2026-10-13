module

public import Accordion.WE.Decidability.Properties.Compression

@[expose] public section

namespace Accordion.WE.Decidability

open scoped List

variable {Γ : Type} {V : Vars}

lemma PairPop.sideLetters_subset {left : Γ → Bool} {A : List Γ} {x : V.Word} {s : Side Γ V}
    (h : PairPop left A x s) : ∀ a ∈ sideLetters s, a ∈ A := by
  obtain ⟨pre, post, hpre, hpost, rfl | rfl⟩ := h <;>
  · rcases hpre with rfl | ⟨b, hb, -, rfl⟩ <;> rcases hpost with rfl | ⟨c, hc, -, rfl⟩ <;>
      simp_all [letters]

lemma PairPop.sideVars_sublist {left : Γ → Bool} {A : List Γ} {x : V.Word} {s : Side Γ V}
    (h : PairPop left A x s) : List.Sublist (sideVars s) [x] := by
  obtain ⟨pre, post, -, -, rfl | rfl⟩ := h <;> simp

lemma PairPop.length_sideLetters_le {left : Γ → Bool} {A : List Γ} {x : V.Word} {s : Side Γ V}
    (h : PairPop left A x s) : (sideLetters s).length ≤ 2 := by
  obtain ⟨pre, post, hpre, hpost, rfl | rfl⟩ := h <;>
  · rcases hpre with rfl | ⟨b, -, -, rfl⟩ <;> rcases hpost with rfl | ⟨c, -, -, rfl⟩ <;>
      simp [letters]

section Pop

variable (left : Γ → Bool) (w : List Γ)

lemma popFirst_append : (popFirst left w).1 ++ (popFirst left w).2 = w := by
  rcases w with _ | ⟨b, w⟩
  · rfl
  · by_cases hb : left b = false <;> simp [popFirst, hb]

lemma popFirst_cases :
    ((popFirst left w).1 = [] ∧ ∀ d ∈ (popFirst left w).2.head?, left d = true) ∨
      ∃ b ∈ w, left b = false ∧ (popFirst left w).1 = [b] := by
  rcases w with _ | ⟨b, w⟩
  · simp [popFirst]
  · by_cases hb : left b = false
    · simp [popFirst, hb]
    · simp_all [popFirst]

lemma popLast_append : (popLast left w).1 ++ (popLast left w).2 = w := by
  unfold popLast
  split
  · rename_i a ha
    by_cases hl : left a = true
    · simpa [hl] using List.dropLast_append_getLast? a ha
    · simp [hl]
  · simp

lemma popLast_cases :
    ((popLast left w).2 = [] ∧ ∀ c ∈ (popLast left w).1.getLast?, left c = false) ∨
      ∃ a ∈ w, left a = true ∧ (popLast left w).2 = [a] := by
  unfold popLast
  split
  · rename_i a ha
    by_cases hl : left a = true
    · simp only [hl, ite_true]
      exact .inr ⟨a, List.mem_of_getLast? ha, hl, rfl⟩
    · simp only [hl, Bool.false_eq_true, ite_false]
      refine .inl ⟨by simp, fun c hc ↦ ?_⟩
      rw [ha, Option.mem_def, Option.some.injEq] at hc
      subst hc
      simpa using hl
  · simp_all

end Pop

lemma pairMid_eq_nil (left : Γ → Bool) {w : List Γ} (hw : w.length ≤ 1) :
    pairMid left w = [] := by
  rcases w with _ | ⟨c, _ | ⟨d, w⟩⟩
  · rfl
  · cases hc : left c <;> simp [pairMid, popFirst, popLast, hc]
  · simp at hw

section Complete

variable (left : Γ → Bool)

lemma pairPop_pairPopOf {A : List Γ} (σ : Subst Γ V) (x : V.Word) (hσ : ∀ a ∈ σ x, a ∈ A) :
    PairPop left A x (pairPopOf left σ x) := by
  have h1 := popFirst_append left (σ x)
  refine ⟨(popFirst left (σ x)).1, (popLast left (popFirst left (σ x)).2).2, ?_, ?_, ?_⟩
  · rcases popFirst_cases left (σ x) with ⟨h, -⟩ | ⟨b, hb, hl, h⟩
    · exact .inl h
    · exact .inr ⟨b, hσ b hb, hl, h⟩
  · rcases popLast_cases left (popFirst left (σ x)).2 with ⟨h, -⟩ | ⟨a, ha, hl, h⟩
    · exact .inl h
    · refine .inr ⟨a, hσ a ?_, hl, h⟩
      rw [← h1]
      exact List.mem_append_right _ ha
  · unfold pairPopOf pairPopWord
    split_ifs
    · exact .inl rfl
    · exact .inr rfl

lemma compressPairs_around (name : Γ → Γ → Γ) {pre mid post : List Γ}
    (hpre : (pre = [] ∧ ∀ d ∈ mid.head?, left d = true) ∨ ∃ b, left b = false ∧ pre = [b])
    (hpost : (post = [] ∧ ∀ c ∈ mid.getLast?, left c = false) ∨ ∃ a, left a = true ∧ post = [a])
    (hm : mid ≠ []) (q E : List Γ) :
    compressPairs left name (q ++ pre ++ mid ++ post ++ E) =
      compressPairs left name (q ++ pre) ++ compressPairs left name mid ++
        compressPairs left name (post ++ E) := by
  obtain ⟨d, m, rfl⟩ := List.exists_cons_of_ne_nil hm
  have b1 : ∀ a b, (q ++ pre).getLast? = some a → (d :: m ++ (post ++ E)).head? = some b →
      ¬IsPair left a b := by
    intro a b ha hb
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hb
    subst hb
    rcases hpre with ⟨-, h⟩ | ⟨c, hc, rfl⟩
    · simp [IsPair, h d rfl]
    · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at ha
      subst ha
      simp [IsPair, hc]
  have b2 : ∀ a b, (d :: m).getLast? = some a → (post ++ E).head? = some b →
      ¬IsPair left a b := by
    intro a b ha hb
    rcases hpost with ⟨rfl, h⟩ | ⟨c, hc, rfl⟩
    · simp [IsPair, h a ha]
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp [IsPair, hc]
  have e1 : q ++ pre ++ d :: m ++ post ++ E = (q ++ pre) ++ (d :: m ++ (post ++ E)) := by simp
  rw [e1, compressPairs_append left name _ _ b1, compressPairs_append left name _ _ b2]
  simp

lemma pairPopWord_spec (name : Γ → Γ → Γ) (x : V.Word) (w : List Γ) :
    pairPopWord left x w = letters w ∨
      ∃ pre post, pairPopWord left x w = letters pre ++ .inr x :: letters post ∧
        w = pre ++ pairMid left w ++ post ∧
        ∀ q E, compressPairs left name (q ++ pre ++ pairMid left w ++ post ++ E) =
          compressPairs left name (q ++ pre) ++ compressPairs left name (pairMid left w) ++
            compressPairs left name (post ++ E) := by
  have h1 := popFirst_append left w
  have h2 := popLast_append left (popFirst left w).2
  have hw : w = (popFirst left w).1 ++ pairMid left w ++ (popLast left (popFirst left w).2).2 := by
    rw [pairMid, List.append_assoc, h2, h1]
  by_cases hm : pairMid left w = []
  · left
    simp only [pairPopWord, ite_eq_left hm]
    conv_rhs => rw [hw]
    simp [hm]
  · right
    refine ⟨_, _, by simp [pairPopWord, hm], hw, compressPairs_around left name ?_ ?_ hm⟩
    · rcases popFirst_cases left w with ⟨hp, h⟩ | ⟨b, -, hb, hp⟩
      · refine .inl ⟨hp, fun d hd ↦ h d ?_⟩
        obtain ⟨d', m, hdm⟩ := List.exists_cons_of_ne_nil hm
        rw [hdm, List.head?_cons, Option.mem_def, Option.some.injEq] at hd
        subst hd
        rw [← h2, show (popLast left (popFirst left w).2).1 = pairMid left w from rfl, hdm]
        simp
      · exact .inr ⟨b, hb, hp⟩
    · rcases popLast_cases left (popFirst left w).2 with ⟨hp, h⟩ | ⟨a, -, ha, hp⟩
      · exact .inl ⟨hp, h⟩
      · exact .inr ⟨a, ha, hp⟩

/-- Stated for any naming of the pairs, since it only reads off the variables. -/
lemma two_le_of_mem_vars_replacePairs (name : Γ → Γ → Γ) (σ : Subst Γ V) {u : Side Γ V}
    {x : V.Word}
    (hx : x ∈ sideVars (mapRuns (compressPairs left name) (substSide (pairPopOf left σ) u))) :
    2 ≤ List.length (σ x) := by
  rw [sideVars_mapRuns] at hx
  obtain ⟨y, -, hy⟩ := mem_sideVars_substSide hx
  unfold pairPopOf pairPopWord at hy
  by_cases hm : pairMid left (σ y) = []
  · simp [hm] at hy
  · simp only [hm, ite_false, sideVars_append, sideVars_letters, sideVars_cons_var,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    by_contra h
    exact hm (pairMid_eq_nil left (by omega))

lemma eval_pairStep_side (name : Γ → Γ → Γ) (σ : Subst Γ V) (u : Side Γ V) :
    compressPairs left name (eval σ u) =
      eval (fun x ↦ compressPairs left name (pairMid left (σ x)))
        (mapRuns (compressPairs left name) (substSide (pairPopOf left σ) u)) := by
  have := eval_mapRuns_substSide (compressPairs left name) (pairPopOf left σ) σ
    (fun x ↦ pairMid left (σ x)) u (fun x _ ↦ pairPopWord_spec left _ x (σ x)) []
  simpa [letters] using this

end Complete

section

variable [DecidableEq Γ] [Fresh Γ]

lemma length_pairLetters (A : List Γ) : (pairLetters A).length = A.length * A.length :=
  length_freshList _ _

lemma nodup_pairLetters (A : List Γ) : (pairLetters A).Nodup :=
  nodup_freshList _ _

lemma notMem_of_mem_pairLetters {A : List Γ} {c : Γ} (h : c ∈ pairLetters A) : c ∉ A :=
  fun hc ↦ notMem_of_mem_freshList h (List.mem_toFinset.2 hc)

lemma pairName_eq_getElem {A : List Γ} {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) :
    ∃ h : (A ×ˢ A).idxOf (a, b) < (pairLetters A).length,
      pairName A a b = (pairLetters A)[(A ×ˢ A).idxOf (a, b)] := by
  have hi : (A ×ˢ A).idxOf (a, b) < (pairLetters A).length := by
    rw [length_pairLetters, ← List.length_product]
    exact List.idxOf_lt_length_of_mem (List.pair_mem_product.2 ⟨ha, hb⟩)
  exact ⟨hi, by simp [pairName, List.getElem?_eq_getElem hi]⟩

lemma pairExpand_pairName {A : List Γ} {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) :
    pairExpand A (pairName A a b) = [a, b] := by
  obtain ⟨hi, h⟩ := pairName_eq_getElem ha hb
  have hp : (a, b) ∈ A ×ˢ A := List.pair_mem_product.2 ⟨ha, hb⟩
  rw [pairExpand, ite_eq_left (h ▸ List.getElem_mem hi), h,
    (nodup_pairLetters A).idxOf_getElem _ hi,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hp), List.getElem_idxOf]
  rfl

lemma pairExpand_of_mem {A : List Γ} {c : Γ} (h : c ∈ A) : pairExpand A c = [c] := by
  rw [pairExpand, ite_eq_right fun hc ↦ notMem_of_mem_pairLetters hc h]

theorem solvable_of_replacePairs {left : Γ → Bool} {g : V.Word → Side Γ V} {e : Eqn Γ V}
    (hg : ∀ x ∈ e.vars, PairPop left e.letters x (g x)) (h : (replacePairs left g e).Solvable) :
    e.Solvable := by
  obtain ⟨τ, hτ⟩ := h
  have hexp : ∀ u, (∀ a ∈ sideLetters u, a ∈ e.letters) → (∀ x ∈ sideVars u, x ∈ e.vars) →
      expandSide (pairExpand e.letters)
        (mapRuns (compressPairs left (pairName e.letters)) (substSide g u)) = substSide g u := by
    intro u hu hv
    refine expandSide_mapRuns (P := (· ∈ e.letters))
      (flatMap_compressPairs left _ (fun _ _ ↦ pairExpand_pairName) fun _ ↦ pairExpand_of_mem) _
      fun a ha ↦ ?_
    rcases mem_sideLetters_substSide ha with ha | ⟨x, hx, ha⟩
    · exact hu a ha
    · exact (hg x (hv x hx)).sideLetters_subset a ha
  have := Eqn.solves_expandSide (pairExpand e.letters) hτ
  simp only [replacePairs, Eqn.map] at this
  rw [hexp e.1 (fun a ha ↦ by simp [Eqn.letters, ha])
      (fun x hx ↦ by simp [Eqn.vars, hx]),
    hexp e.2 (fun a ha ↦ by simp [Eqn.letters, ha])
      (fun x hx ↦ by simp [Eqn.vars, hx])] at this
  exact ⟨_, Eqn.solves_of_substSide (e := e) this⟩

theorem replacePairs_complete (left : Γ → Bool) {e : Eqn Γ V} {σ : Subst Γ V}
    (hσ : e.Solves σ) :
    (replacePairs left (pairPopOf left σ) e).Solves
        (fun x ↦ compressPairs left (pairName e.letters) (pairMid left (σ x))) ∧
      eval (fun x ↦ compressPairs left (pairName e.letters) (pairMid left (σ x)))
          (replacePairs left (pairPopOf left σ) e).1 =
        compressPairs left (pairName e.letters) (eval σ e.1) := by
  simp only [replacePairs, Eqn.map, Eqn.Solves]
  rw [← eval_pairStep_side, ← eval_pairStep_side]
  exact ⟨congrArg _ hσ, rfl⟩

lemma replacePairs_congr {left : Γ → Bool} {g g' : V.Word → Side Γ V} {e : Eqn Γ V}
    (h : ∀ x ∈ e.vars, g x = g' x) : replacePairs left g e = replacePairs left g' e := by
  simp only [replacePairs, Eqn.map]
  rw [substSide_congr fun x hx ↦ h x (by simp [Eqn.vars, hx]),
    substSide_congr (u := e.2) fun x hx ↦ h x (by simp [Eqn.vars, hx])]

end

lemma pairPop_of_mem_pops {left : Γ → Bool} {A : List Γ} {x : V.Word} {s : Side Γ V}
    (h : s ∈ pops left A x) : PairPop left A x s := by
  simp only [pops, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq, List.mem_nil_iff, or_false] at h
  obtain ⟨pre, hpre, post, hpost, hs⟩ := h
  refine ⟨pre, post, ?_, ?_, hs⟩
  · rcases hpre with rfl | ⟨b, ⟨hb, hl⟩, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨b, hb, hl, rfl⟩
  · rcases hpost with rfl | ⟨a, ⟨ha, hl⟩, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨a, ha, hl, rfl⟩

lemma mem_pops_of_pairPop {left : Γ → Bool} {A : List Γ} {x : V.Word} {s : Side Γ V}
    (h : PairPop left A x s) : s ∈ pops left A x := by
  obtain ⟨pre, post, hpre, hpost, hs⟩ := h
  simp only [pops, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq, List.mem_nil_iff, or_false]
  refine ⟨pre, ?_, post, ?_, hs⟩
  · rcases hpre with rfl | ⟨b, hb, hl, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨b, ⟨hb, hl⟩, rfl⟩
  · rcases hpost with rfl | ⟨a, ha, hl, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨a, ⟨ha, hl⟩, rfl⟩

end Accordion.WE.Decidability

end
