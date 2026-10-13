module

public import Accordion.WE.Decidability.Properties.Basic

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

lemma eval_flatten_substLetterVars_map {g : Γ → Γ} {m : Model Γ V} {σ : Subst Γ V}
    {f : V.Letter → Γ} :
    ∀ u : Word Γ V, (∀ a ∈ wordConsts u, g a = a) →
      (∀ x ∈ u.letterVars, f x = g (m.σLetter x)) →
      (∀ y ∈ u.vars, σ y = List.map g (m.σWord y)) →
      eval σ (u.substLetterVars f).flatten = List.map g (m.evalWord u)
  | .empty, _, _, _ => rfl
  | .letter a, h, _, _ => by
      simp [Word.substLetterVars, Word.flatten, Model.evalWord, h a (by simp [wordConsts])]
  | .letterVar x, _, h, _ => by
      simp [Word.substLetterVars, Word.flatten, Model.evalWord, h x (by simp [Word.letterVars])]
  | .var y, _, _, h => by
      simp [Word.substLetterVars, Word.flatten, Model.evalWord, h y (by simp [Word.vars])]
  | .concat p q, h₁, h₂, h₃ => by
      simp only [Word.substLetterVars, Word.flatten, eval_append, Model.evalWord, List.map_append]
      rw [eval_flatten_substLetterVars_map p (fun a ha ↦ h₁ a (by simp [wordConsts, ha]))
          (fun x hx ↦ h₂ x (by simp [Word.letterVars, hx]))
          (fun y hy ↦ h₃ y (by simp [Word.vars, hy])),
        eval_flatten_substLetterVars_map q (fun a ha ↦ h₁ a (by simp [wordConsts, ha]))
          (fun x hx ↦ h₂ x (by simp [Word.letterVars, hx]))
          (fun y hy ↦ h₃ y (by simp [Word.vars, hy]))]

lemma ne_of_ne_at {u v w : List Γ} {a b : Γ} (hab : a ≠ b) : u ++ a :: v ≠ u ++ b :: w := by
  intro h
  exact hab (List.cons.inj (List.append_cancel_left h)).1

lemma exists_diff : ∀ {u v : List Γ}, u ≠ v → ∃ (k : Nat) (a b : Γ) (w s t : List Γ),
    (k = 0 ∧ a ≠ b ∧ u = w ++ a :: s ∧ v = w ++ b :: t) ∨
      (k = 1 ∧ u = v ++ a :: s) ∨ (k = 2 ∧ v = u ++ a :: s)
  | [], [], h => absurd rfl h
  | [], b :: t, _ => ⟨2, b, b, [], t, t, .inr (.inr ⟨rfl, rfl⟩)⟩
  | a :: s, [], _ => ⟨1, a, a, [], s, s, .inr (.inl ⟨rfl, rfl⟩)⟩
  | a :: s, b :: t, h => by
      by_cases hab : a = b
      · subst hab
        obtain ⟨k, a', b', w, s', t', hd⟩ := exists_diff (u := s) (v := t) fun e ↦ h (e ▸ rfl)
        refine ⟨k, a', b', a :: w, s', t', ?_⟩
        rcases hd with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
        · exact .inl ⟨h0, h1, by simp [h2], by simp [h3]⟩
        · exact .inr (.inl ⟨h0, by simp [h1]⟩)
        · exact .inr (.inr ⟨h0, by simp [h1]⟩)
      · exact ⟨0, a, b, [], s, t, .inl ⟨rfl, hab, rfl, rfl⟩⟩

section

variable [DecidableEq Γ]

lemma exists_letterMap {C X F : List Γ} (hA : (C ++ F).Nodup) (hlen : X.length ≤ F.length) :
    ∃ g : Γ → Γ, (∀ x ∈ C, g x = x) ∧ (∀ x ∈ C ++ X, g x ∈ C ++ F) ∧
      ∀ x ∈ C ++ X, ∀ y ∈ C ++ X, g x = g y → x = y := by
  have hlt : ∀ x ∈ C ++ X, (C ++ X).idxOf x < (C ++ F).length := fun x hx ↦ by
    have := List.idxOf_lt_length_of_mem hx
    simp only [List.length_append] at this ⊢
    omega
  have hg : ∀ x (hx : x ∈ C ++ X),
      ((C ++ F)[(C ++ X).idxOf x]?).getD x = (C ++ F)[(C ++ X).idxOf x]'(hlt x hx) :=
    fun x hx ↦ by simp [List.getElem?_eq_getElem (hlt x hx)]
  refine ⟨fun x ↦ ((C ++ F)[(C ++ X).idxOf x]?).getD x, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx y hy hxy ↦ ?_⟩
  · have hi := List.idxOf_lt_length_of_mem hx
    simp [List.idxOf_append_of_mem hx, List.getElem?_append_left hi,
      List.getElem?_eq_getElem hi]
  · simp only [hg x hx]
    exact List.getElem_mem _
  · simp only [hg x hx, hg y hy] at hxy
    exact (List.idxOf_inj hx).1 ((hA.getElem_inj_iff).1 hxy)

variable [Fresh Γ] [DecidableEq V.Word] [DecidableEq V.Letter] [Fresh V.Word]

lemma mem_conjEquations {c : Conj Γ V} {E : System Γ V} :
    E ∈ conjEquations c ↔
      ∃ f ∈ assignments (fun _ ↦ conjLetters c) (fun _ ↦ Fresh.fresh ∅) (conjLetterVars c),
        ∃ dg ∈ assignments (fun _ ↦ disequationCases (conjLetters c))
          (fun _ ↦ (0, Fresh.fresh ∅, Fresh.fresh ∅)) (List.range c.length),
          E = conjEquation c f dg := by
  simp [conjEquations, eq_comm]

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Letter] in
theorem holds_of_conjEquation {c : Conj Γ V} {f : V.Letter → Γ} {dg : Nat → Nat × Γ × Γ}
    (hdg : ∀ i < c.length, (dg i).1 = 0 → (dg i).2.1 ≠ (dg i).2.2)
    (h : (conjEquation c f dg).Solvable) : c.SAT := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨⟨f, σ⟩, fun l hl ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hmem : (c[i], i) ∈ c.zipIdx := List.mem_zipIdx_iff_getElem?.2 (by simp [hi])
  have heqs : ∀ p ∈ literalEquations f (conjFreshVars c) dg (c[i], i), p.Solves σ :=
    fun p hp ↦ hσ p (List.mem_flatMap.2 ⟨_, hmem, hp⟩)
  have hu : eval σ (c[i].2.1.substLetterVars f).flatten = Model.evalWord ⟨f, σ⟩ c[i].2.1 :=
    eval_flatten_substLetterVars ⟨f, σ⟩ _
  have hv : eval σ (c[i].2.2.substLetterVars f).flatten = Model.evalWord ⟨f, σ⟩ c[i].2.2 :=
    eval_flatten_substLetterVars ⟨f, σ⟩ _
  unfold Literal.Holds
  split_ifs with hpos
  · simp only [literalEquations, hpos, ite_true, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Eqn.Solves] at heqs
    rw [← hu, ← hv, heqs]
  · rcases hd : dg i with ⟨k, a, b⟩
    simp only [literalEquations, hpos, Bool.false_eq_true, ite_false, hd] at heqs
    rcases k with _ | _ | k
    · have hab : a ≠ b := by simpa [hd] using hdg i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Eqn.Solves, eval_cons, eval_var, eval_letter, eval_nil] at heqs
      rw [← hu, ← hv, heqs.1, heqs.2]
      simpa using ne_of_ne_at (u := σ (((conjFreshVars c)[3 * i]?).getD (Fresh.fresh ∅))) hab
    · simp only [Nat.zero_add, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Eqn.Solves,
        eval_append, eval_cons, eval_var, eval_letter, eval_nil] at heqs
      rw [← hu, ← hv, heqs]
      simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Eqn.Solves,
        eval_append, eval_cons, eval_var, eval_letter, eval_nil] at heqs
      rw [← hu, ← hv, heqs]
      simp

theorem exists_conjEquation_of_holds {c : Conj Γ V} {m : Model Γ V} (h : ∀ l ∈ c, l.Holds m) :
    ∃ E ∈ conjEquations c, E.Solvable := by
  have H : ∀ i : Fin c.length, ∃ (k : Nat) (a b : Γ) (w s t : List Γ), k < 3 ∧
      (k = 0 → a ≠ b) ∧ (c[i].1 = false →
        (k = 0 ∧ a ≠ b ∧ m.evalWord c[i].2.1 = w ++ a :: s ∧ m.evalWord c[i].2.2 = w ++ b :: t) ∨
          (k = 1 ∧ m.evalWord c[i].2.1 = m.evalWord c[i].2.2 ++ a :: s) ∨
          (k = 2 ∧ m.evalWord c[i].2.2 = m.evalWord c[i].2.1 ++ a :: s)) := by
    intro i
    by_cases hpos : c[i].1 = false
    · have hne := h c[i] (List.getElem_mem i.2)
      simp only [Literal.Holds, hpos, Bool.false_eq_true, ite_false] at hne
      obtain ⟨k, a, b, w, s, t, hd⟩ := exists_diff hne
      refine ⟨k, a, b, w, s, t, ?_, ?_, fun _ ↦ hd⟩
      · rcases hd with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ <;> omega
      · intro h0
        rcases hd with ⟨-, h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · omega
        · omega
    · exact ⟨1, Fresh.fresh ∅, Fresh.fresh ∅, [], [], [], by simp, by simp,
        fun h' ↦ absurd h' hpos⟩
  choose k a b w s t hk3 hk0 hgood using H
  set C := conjConsts c with hCdef
  set F := freshList C.toFinset ((conjLetterVars c).length + 2 * c.length) with hFdef
  set X := (((conjLetterVars c).map m.σLetter ++
    (List.finRange c.length).flatMap fun i ↦ [a i, b i]).filter (· ∉ C)).dedup with hXdef
  have hA : (C ++ F).Nodup := List.nodup_append.2 ⟨List.nodup_dedup _, nodup_freshList _ _,
    fun x hx y hy hxy ↦ notMem_of_mem_freshList hy (List.mem_toFinset.2 (hxy ▸ hx))⟩
  have hXlen : X.length ≤ F.length := by
    have h1 := (List.dedup_sublist ((((conjLetterVars c).map m.σLetter ++
      (List.finRange c.length).flatMap fun i ↦ [a i, b i]).filter (· ∉ C)))).length_le
    have h2 := List.length_filter_le (· ∉ C) ((conjLetterVars c).map m.σLetter ++
      (List.finRange c.length).flatMap fun i ↦ [a i, b i])
    have h3 : ((List.finRange c.length).flatMap fun i ↦ [a i, b i]).length = 2 * c.length := by
      simp [List.length_flatMap, mul_comm]
    simp only [List.length_append, List.length_map, h3] at h1 h2
    simp only [hFdef, length_freshList, hXdef]
    omega
  obtain ⟨g, hgC, hgL, hginj⟩ := exists_letterMap hA hXlen
  have hmemL : ∀ x, x ∈ C ∨ x ∈ (conjLetterVars c).map m.σLetter ∨
      x ∈ (List.finRange c.length).flatMap (fun i ↦ [a i, b i]) → x ∈ C ++ X := by
    intro x hx
    by_cases hC : x ∈ C
    · exact List.mem_append_left _ hC
    · refine List.mem_append_right _ (List.mem_dedup.2 (List.mem_filter.2 ⟨?_, by simpa using hC⟩))
      rcases hx with hx | hx | hx
      · exact absurd hx hC
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ hx
  have ha : ∀ i, a i ∈ C ++ X := fun i ↦ hmemL _ (.inr (.inr (List.mem_flatMap.2
    ⟨i, List.mem_finRange i, by simp⟩)))
  have hb : ∀ i, b i ∈ C ++ X := fun i ↦ hmemL _ (.inr (.inr (List.mem_flatMap.2
    ⟨i, List.mem_finRange i, by simp⟩)))
  let dg₀ : Nat → Nat × Γ × Γ := fun i ↦
    if hi : i < c.length then (k ⟨i, hi⟩, g (a ⟨i, hi⟩), g (b ⟨i, hi⟩))
    else (0, Fresh.fresh ∅, Fresh.fresh ∅)
  obtain ⟨f, hf, hfg⟩ := exists_mem_assignments (opts := fun _ ↦ conjLetters c)
    (d := fun _ ↦ Fresh.fresh ∅) (fun x ↦ g (m.σLetter x)) (conjLetterVars c)
    fun x hx ↦ hgL _ (hmemL _ (.inr (.inl (List.mem_map_of_mem hx))))
  obtain ⟨dg, hdgm, hdgg⟩ := exists_mem_assignments
    (opts := fun _ ↦ disequationCases (conjLetters c))
    (d := fun _ ↦ (0, Fresh.fresh ∅, Fresh.fresh ∅)) dg₀
    (List.range c.length) fun i hi ↦ by
      have hi := List.mem_range.1 hi
      simp only [disequationCases, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
        dg₀, hi, ↓reduceDIte]
      refine ⟨⟨k ⟨i, hi⟩, hk3 _, g (a ⟨i, hi⟩), hgL _ (ha _), g (b ⟨i, hi⟩), hgL _ (hb _), rfl⟩,
        ?_⟩
      by_cases h0 : k ⟨i, hi⟩ = 0
      · simp only [h0, ne_eq, not_true_eq_false, false_or, decide_eq_true_eq]
        exact fun e ↦ hk0 _ h0 (hginj _ (ha _) _ (hb _) e)
      · simp [h0]
  set fv := conjFreshVars c with hfvdef
  have hfvlen : fv.length = 3 * c.length := length_freshList _ _
  have hfvnd : fv.Nodup := nodup_freshList _ _
  let σ : Subst Γ V := fun x ↦
    if x ∈ fv then
      if hi : fv.idxOf x / 3 < c.length then
        List.map g (if fv.idxOf x % 3 = 0 then w ⟨_, hi⟩
          else if fv.idxOf x % 3 = 1 then s ⟨_, hi⟩ else t ⟨_, hi⟩)
      else []
    else List.map g (m.σWord x)
  have hσP : ∀ y ∈ conjVars c, σ y = List.map g (m.σWord y) := fun y hy ↦ by
    have : y ∉ fv := fun hmem ↦ notMem_of_mem_freshList hmem (List.mem_toFinset.2 hy)
    simp only [σ, this, ↓reduceIte]
  have hσW : ∀ (i : Fin c.length) (j : Nat), j < 3 →
      σ ((fv[3 * i + j]?).getD (Fresh.fresh ∅)) =
        List.map g (if j = 0 then w i else if j = 1 then s i else t i) := by
    intro i j hj
    have hlt : 3 * i + j < fv.length := by have := i.2; omega
    have h1 : (fv[3 * i + j]?).getD (Fresh.fresh ∅) = fv[3 * i + j] := by
      simp [List.getElem?_eq_getElem hlt]
    have h2 : fv.idxOf fv[3 * i + j] = 3 * i + j := hfvnd.idxOf_getElem _ hlt
    have h3 : (3 * i + j) / 3 = i := by omega
    have h4 : (3 * i + j) % 3 = j := by omega
    have hi : (3 * i + j) / 3 < c.length := by rw [h3]; exact i.2
    have hwi : (⟨_, hi⟩ : Fin c.length) = i := Fin.ext h3
    simp only [σ, h1, List.getElem_mem, ite_true, h2, hi, ↓reduceDIte, hwi, h4]
  refine ⟨_, mem_conjEquations.2 ⟨f, hf, dg, hdgm, rfl⟩, σ, fun p hp₀ ↦ ?_⟩
  obtain ⟨⟨l, i⟩, hli, hp⟩ := List.mem_flatMap.1 hp₀
  clear hp₀
  obtain ⟨hi, hl⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hli)
  simp only at hi hl
  subst hl
  revert p
  have henc : ∀ u : Word Γ V, (u = c[i].2.1 ∨ u = c[i].2.2) →
      eval σ (u.substLetterVars f).flatten = List.map g (m.evalWord u) := by
    intro u hu
    refine eval_flatten_substLetterVars_map u (fun x hx ↦ hgC x ?_) (fun x hx ↦ hfg x ?_)
      (fun y hy ↦ hσP y ?_)
    · simp only [C, conjConsts, List.mem_dedup, List.mem_flatMap, List.mem_append]
      exact ⟨c[i], List.getElem_mem hi, by rcases hu with rfl | rfl <;> simp [hx]⟩
    · simp only [conjLetterVars, List.mem_dedup, List.mem_flatMap, List.mem_append]
      exact ⟨c[i], List.getElem_mem hi, by rcases hu with rfl | rfl <;> simp [hx]⟩
    · simp only [conjVars, List.mem_dedup, List.mem_flatMap, List.mem_append]
      exact ⟨c[i], List.getElem_mem hi, by rcases hu with rfl | rfl <;> simp [hy]⟩
  have hu := henc _ (.inl rfl)
  have hv := henc _ (.inr rfl)
  by_cases hpos : c[i].1 = true
  · have := h c[i] (List.getElem_mem hi)
    simp only [Literal.Holds, hpos, ite_true] at this
    simp only [literalEquations, hpos, ite_true, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Eqn.Solves]
    rw [hu, hv, this]
  · have hneg : c[i].1 = false := by simpa using hpos
    have hdgi : dg i = dg₀ i := hdgg i (List.mem_range.2 hi)
    have hgood := hgood ⟨i, hi⟩ hneg
    simp only [Fin.getElem_fin] at hgood
    have w0 := hσW ⟨i, hi⟩ 0 (by omega)
    have w1 := hσW ⟨i, hi⟩ 1 (by omega)
    have w2 := hσW ⟨i, hi⟩ 2 (by omega)
    simp only [Nat.add_zero, ite_true, one_ne_zero, ite_false, Nat.reduceEqDiff] at w0 w1 w2
    rw [hfvdef] at w0 w1 w2
    simp only [literalEquations, hpos, Bool.false_eq_true, ite_false, hdgi, dg₀, hi, ↓reduceDIte]
    rcases hgood with ⟨h0, -, hu', hv'⟩ | ⟨h0, hu'⟩ | ⟨h0, hv'⟩
    · simp only [h0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Eqn.Solves, eval_cons, eval_var, eval_letter, eval_nil, hu, hv, hu', hv', w0, w1, w2]
      simp
    · simp only [h0, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Eqn.Solves,
        eval_append, eval_cons, eval_var, eval_letter, eval_nil, hu, hv, hu', w1]
      simp
    · simp only [h0, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Eqn.Solves,
        eval_append, eval_cons, eval_var, eval_letter, eval_nil, hu, hv, hv', w1]
      simp

theorem conjEquations_equisat (c : Conj Γ V) :
    (∃ E ∈ conjEquations c, E.Solvable) ↔ c.SAT := by
  refine ⟨fun ⟨E, hE, h⟩ ↦ ?_, fun ⟨m, hm⟩ ↦ exists_conjEquation_of_holds hm⟩
  obtain ⟨f, -, dg, hdg, rfl⟩ := mem_conjEquations.1 hE
  refine holds_of_conjEquation (fun i hi h0 ↦ ?_) h
  have := mem_assignments hdg i (List.mem_range.2 hi)
  simp only [disequationCases, List.mem_filter, decide_eq_true_eq] at this
  exact this.2.resolve_left (by simpa using h0)

end

end Accordion.WE.Decidability

end
