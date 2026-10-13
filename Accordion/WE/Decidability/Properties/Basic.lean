module

public import Accordion.WE.Decidability.Properties.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Logic.Relation

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

section

variable {α : Type} [DecidableEq α] [Fresh α]

@[simp] lemma length_freshList (s : Finset α) : ∀ n, (freshList s n).length = n
  | 0 => rfl
  | n + 1 => by simp [freshList, length_freshList _ n]

lemma notMem_of_mem_freshList {s : Finset α} {n : Nat} {a : α} (h : a ∈ freshList s n) :
    a ∉ s := by
  induction n generalizing s with
  | zero => simp [freshList] at h
  | succ n ih =>
      rcases List.mem_cons.1 h with rfl | h
      · exact Fresh.fresh_notMem s
      · exact fun ha ↦ ih h (Finset.mem_insert_of_mem ha)

lemma nodup_freshList (s : Finset α) : ∀ n, (freshList s n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => List.nodup_cons.2
      ⟨fun h ↦ notMem_of_mem_freshList h (Finset.mem_insert_self ..), nodup_freshList _ n⟩

end

@[simp] lemma eval_nil (σ : Subst Γ V) : eval σ [] = [] := rfl

@[simp] lemma eval_cons (σ : Subst Γ V) (s : Sym Γ V) (u : Side Γ V) :
    eval σ (s :: u) = s.eval σ ++ eval σ u := by
  simp [eval]

@[simp] lemma eval_append (σ : Subst Γ V) (u v : Side Γ V) :
    eval σ (u ++ v) = eval σ u ++ eval σ v := by
  simp [eval]

@[simp] lemma eval_letter (σ : Subst Γ V) (a : Γ) : Sym.eval σ (.inl a) = [a] := rfl

@[simp] lemma eval_var (σ : Subst Γ V) (x : V.Word) : Sym.eval σ (.inr x) = σ x := rfl

lemma eval_flatten_substLetterVars (m : Model Γ V) (u : Word Γ V) :
    eval m.σWord (u.substLetterVars m.σLetter).flatten = m.evalWord u := by
  induction u with
  | concat u v ihu ihv => simp [Word.substLetterVars, Word.flatten, Model.evalWord, ihu, ihv]
  | _ => simp [Word.substLetterVars, Word.flatten, Model.evalWord]

lemma le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | b :: l, a, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := le_sum_of_mem h
        simp only [List.sum_cons]
        omega

@[simp] lemma eval_letters (σ : Subst Γ V) (w : GroundWord Γ) : eval σ (letters w) = w := by
  induction w <;> simp_all [letters]

@[simp] lemma sideLetters_nil : sideLetters ([] : Side Γ V) = [] := rfl

@[simp] lemma sideLetters_append (u v : Side Γ V) :
    sideLetters (u ++ v) = sideLetters u ++ sideLetters v := by
  simp [sideLetters]

@[simp] lemma sideLetters_cons_letter (a : Γ) (u : Side Γ V) :
    sideLetters (.inl a :: u) = a :: sideLetters u := rfl

@[simp] lemma sideLetters_cons_var (x : V.Word) (u : Side Γ V) :
    sideLetters (.inr x :: u) = sideLetters u := rfl

@[simp] lemma sideLetters_letters (w : GroundWord Γ) :
    sideLetters (letters w : Side Γ V) = w := by
  induction w <;> simp_all [letters]

@[simp] lemma sideVars_nil : sideVars ([] : Side Γ V) = [] := rfl

@[simp] lemma sideVars_append (u v : Side Γ V) :
    sideVars (u ++ v) = sideVars u ++ sideVars v := by
  simp [sideVars]

@[simp] lemma sideVars_cons_letter (a : Γ) (u : Side Γ V) :
    sideVars (.inl a :: u) = sideVars u := rfl

@[simp] lemma sideVars_cons_var (x : V.Word) (u : Side Γ V) :
    sideVars (.inr x :: u) = x :: sideVars u := rfl

@[simp] lemma sideVars_letters (w : GroundWord Γ) : sideVars (letters w : Side Γ V) = [] := by
  induction w <;> simp_all [letters]

lemma length_side (u : Side Γ V) : u.length = (sideLetters u).length + (sideVars u).length := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih] <;> omega

lemma Eqn.size_eq (e : Eqn Γ V) : e.size = e.letterCount + e.varCount := by
  simp only [Eqn.size, Eqn.letterCount, Eqn.letters, Eqn.varCount,
    Eqn.vars, List.length_append, length_side e.1, length_side e.2]
  omega

lemma eval_of_sideVars_eq_nil {σ : Subst Γ V} {u : Side Γ V} (h : sideVars u = []) :
    eval σ u = sideLetters u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a => simp [ih (by simpa using h)]
      | inr x => simp at h

lemma mem_sideLetters_of_mem {u : Side Γ V} {a : Γ} (h : .inl a ∈ u) : a ∈ sideLetters u :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

lemma mem_sideVars_of_mem {u : Side Γ V} {x : V.Word} (h : .inr x ∈ u) : x ∈ sideVars u :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

lemma eval_congr {σ τ : Subst Γ V} {u : Side Γ V} (h : ∀ x ∈ sideVars u, σ x = τ x) :
    eval σ u = eval τ u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a => simp [ih (by simpa using h)]
      | inr x => simp [h x (by simp), ih fun y hy ↦ h y (by simp [hy])]

lemma length_le_eval {σ : Subst Γ V} {u : Side Γ V} {x : V.Word} (hx : x ∈ sideVars u) :
    List.length (σ x) ≤ List.length (eval σ u) := by
  induction u with
  | nil => simp at hx
  | cons s u ih =>
      cases s with
      | inl a =>
          have := ih (by simpa using hx)
          simp only [eval_cons, eval_letter, List.length_append]
          omega
      | inr y =>
          simp only [sideVars_cons_var, List.mem_cons] at hx
          simp only [eval_cons, eval_var, List.length_append]
          rcases hx with rfl | hx
          · omega
          · have := ih hx
            omega

lemma mem_eval {σ : Subst Γ V} {u : Side Γ V} {c : Γ} (hc : c ∈ eval σ u) :
    c ∈ sideLetters u ∨ ∃ x ∈ sideVars u, c ∈ σ x := by
  induction u with
  | nil => simp at hc
  | cons s u ih =>
      cases s with
      | inl a =>
          simp only [eval_cons, eval_letter, List.cons_append, List.nil_append, List.mem_cons] at hc
          rcases hc with rfl | hc
          · simp
          · rcases ih hc with h | ⟨x, hx, h⟩
            · simp [h]
            · exact .inr ⟨x, by simpa using hx, h⟩
      | inr y =>
          simp only [eval_cons, eval_var, List.mem_append] at hc
          rcases hc with hc | hc
          · exact .inr ⟨y, by simp, hc⟩
          · rcases ih hc with h | ⟨x, hx, h⟩
            · simp [h]
            · exact .inr ⟨x, by simp [hx], h⟩

lemma mem_assignments {α β : Type} [DecidableEq α] {opts : α → List β} {d : α → β} :
    ∀ {xs : List α} {g : α → β}, g ∈ assignments opts d xs → ∀ x ∈ xs, g x ∈ opts x
  | [], _, _, x, hx => by simp at hx
  | y :: xs, g, hg, x, hx => by
      simp only [assignments, Guess.mem_bind, Guess.mem_pure, mem_guess] at hg
      obtain ⟨b, hb, g', hg', rfl⟩ := hg
      by_cases hxy : x = y
      · subst hxy
        simpa using hb
      · rw [Function.update_of_ne hxy]
        exact mem_assignments hg' x (by simpa [hxy] using hx)

lemma exists_mem_assignments {α β : Type} [DecidableEq α] {opts : α → List β} {d : α → β}
    (f : α → β) : ∀ xs : List α, (∀ x ∈ xs, f x ∈ opts x) →
      ∃ g ∈ assignments opts d xs, ∀ x ∈ xs, g x = f x
  | [], _ => ⟨d, by simp [assignments], by simp⟩
  | y :: xs, h => by
      obtain ⟨g, hg, hgf⟩ :=
        exists_mem_assignments f xs fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
      refine ⟨Function.update g y (f y), ?_, fun x hx ↦ ?_⟩
      · simp only [assignments, Guess.mem_bind, Guess.mem_pure, mem_guess]
        exact ⟨f y, h y (List.mem_cons_self ..), g, hg, rfl⟩
      · by_cases hxy : x = y
        · subst hxy
          simp
        · rw [Function.update_of_ne hxy]
          exact hgf x (by simpa [hxy] using hx)

lemma mem_vectors {n : Nat} : ∀ {k : Nat} {l : List Nat},
    l ∈ vectors n k ↔ l.length = k ∧ ∀ c ∈ l, c < n
  | 0, l => by cases l <;> simp [vectors]
  | k + 1, l => by
      simp only [vectors, Guess.mem_bind, Guess.mem_pure, mem_guess, List.mem_range]
      constructor
      · rintro ⟨c, hc, l', hl', rfl⟩
        obtain ⟨h1, h2⟩ := mem_vectors.1 hl'
        refine ⟨by simp [h1], fun d hd ↦ ?_⟩
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hc
        · exact h2 d hd
      · rintro ⟨h1, h2⟩
        rcases l with _ | ⟨c, l'⟩
        · simp at h1
        · exact ⟨c, h2 c (by simp), l', mem_vectors.2 ⟨by simpa using h1,
            fun d hd ↦ h2 d (List.mem_cons_of_mem _ hd)⟩, rfl⟩

lemma mem_listsUpTo {α : Type} {syms : List α} : ∀ {k : Nat} {l : List α},
    l.length ≤ k → (∀ s ∈ l, s ∈ syms) → l ∈ listsUpTo syms k
  | 0, l, h, _ => by cases l <;> simp_all [listsUpTo]
  | k + 1, [], _, _ => by simp [listsUpTo]
  | k + 1, s :: l, h, hs => by
      simp only [listsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact .inr ⟨s, hs s (by simp), l,
        mem_listsUpTo (by simpa using h) fun t ht ↦ hs t (List.mem_cons_of_mem _ ht), rfl⟩

lemma mem_of_mem_listsUpTo {α : Type} {syms : List α} :
    ∀ {k : Nat} {l : List α}, l ∈ listsUpTo syms k → ∀ s ∈ l, s ∈ syms
  | 0, l, h => by simp [listsUpTo] at h; simp [h]
  | k + 1, l, h => by
      simp only [listsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map] at h
      rcases h with rfl | ⟨t, ht, l', hl', rfl⟩
      · simp
      · intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · exact ht
        · exact mem_of_mem_listsUpTo hl' s hs

lemma length_listsUpTo {α : Type} (syms : List α) :
    ∀ k, (listsUpTo syms k).length = countUpTo syms.length k
  | 0 => rfl
  | k + 1 => by
      simp [listsUpTo, countUpTo, List.length_flatMap, length_listsUpTo syms k, List.map_const',
        List.sum_replicate, add_comm]

lemma mem_bitVectors {m : Nat} (β : Fin m → Bool) : β ∈ bitVectors m := by
  obtain ⟨g, hg, hgβ⟩ := exists_mem_assignments (opts := fun _ ↦ [false, true])
    (d := fun _ ↦ false) β (List.finRange m) fun i _ ↦ by cases β i <;> simp
  rwa [show g = β from funext fun i ↦ hgβ i (List.mem_finRange i)] at hg

section

variable {α : Type*} [DecidableEq α]

variable {next : α → Finset α} {s U : Finset α}

@[simp] theorem reachWithin_zero : reachWithin next s 0 = s := rfl

theorem reachWithin_succ (k : ℕ) :
    reachWithin next s (k + 1) = reachWithin next s k ∪ (reachWithin next s k).biUnion next :=
  rfl

theorem reachWithin_subset_succ (k : ℕ) : reachWithin next s k ⊆ reachWithin next s (k + 1) := by
  rw [reachWithin_succ]
  exact Finset.subset_union_left

theorem reachWithin_mono {j k : ℕ} (h : j ≤ k) : reachWithin next s j ⊆ reachWithin next s k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (reachWithin_subset_succ k)

theorem next_subset_reachWithin_succ {k : ℕ} {a : α} (ha : a ∈ reachWithin next s k) :
    next a ⊆ reachWithin next s (k + 1) := by
  rw [reachWithin_succ]
  exact (Finset.subset_biUnion_of_mem next ha).trans Finset.subset_union_right

theorem exists_reflTransGen_of_mem_reachWithin {k : ℕ} {b : α} (hb : b ∈ reachWithin next s k) :
    ∃ a ∈ s, Relation.ReflTransGen (fun x y => y ∈ next x) a b := by
  induction k generalizing b with
  | zero => exact ⟨b, hb, .refl⟩
  | succ k ih =>
    rcases Finset.mem_union.1 (reachWithin_succ (next := next) (s := s) k ▸ hb) with hb | hb
    · exact ih hb
    · obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.1 hb
      obtain ⟨a, ha, hac⟩ := ih hc
      exact ⟨a, ha, hac.tail hbc⟩

theorem reachWithin_subset (hs : s ⊆ U) (hU : ∀ a ∈ U, next a ⊆ U) (k : ℕ) :
    reachWithin next s k ⊆ U := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [reachWithin_succ]
    exact Finset.union_subset ih (Finset.biUnion_subset.2 fun a ha => hU a (ih ha))

theorem reachWithin_eq_of_succ_eq {k : ℕ} (h : reachWithin next s (k + 1) = reachWithin next s k)
    {j : ℕ} (hj : k ≤ j) : reachWithin next s j = reachWithin next s k := by
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [reachWithin_succ, ih, ← reachWithin_succ, h]

theorem le_card_reachWithin_or (k : ℕ) :
    k ≤ (reachWithin next s k).card ∨
      ∃ j < k, reachWithin next s (j + 1) = reachWithin next s j := by
  induction k with
  | zero => exact .inl (Nat.zero_le _)
  | succ k ih =>
    by_cases h : reachWithin next s (k + 1) = reachWithin next s k
    · exact .inr ⟨k, Nat.lt_succ_self k, h⟩
    · rcases ih with ih | ⟨j, hj, hj'⟩
      · refine .inl ?_
        have := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨reachWithin_subset_succ k, Ne.symm h⟩)
        omega
      · exact .inr ⟨j, hj.trans (Nat.lt_succ_self k), hj'⟩

theorem reachWithin_succ_eq_of_card_le (hs : s ⊆ U) (hU : ∀ a ∈ U, next a ⊆ U) {n : ℕ}
    (hn : U.card ≤ n) : reachWithin next s (n + 1) = reachWithin next s n := by
  rcases le_card_reachWithin_or (next := next) (s := s) (n + 1) with h | ⟨j, hj, h⟩
  · have := Finset.card_le_card (reachWithin_subset hs hU (n + 1))
    omega
  · rw [reachWithin_eq_of_succ_eq h (by omega : j ≤ n + 1),
      reachWithin_eq_of_succ_eq h (by omega : j ≤ n)]

theorem mem_reachWithin_iff_of_card_le (hs : s ⊆ U) (hU : ∀ a ∈ U, next a ⊆ U) {n : ℕ}
    (hn : U.card ≤ n) {b : α} :
    b ∈ reachWithin next s n ↔ ∃ a ∈ s, Relation.ReflTransGen (fun x y => y ∈ next x) a b := by
  refine ⟨exists_reflTransGen_of_mem_reachWithin, ?_⟩
  rintro ⟨a, ha, hab⟩
  induction hab with
  | refl => exact reachWithin_mono (Nat.zero_le n) ha
  | tail _ hcd ih =>
    rw [← reachWithin_succ_eq_of_card_le hs hU hn]
    exact next_subset_reachWithin_succ ih hcd

theorem mem_reachWithin_card_iff (hs : s ⊆ U) (hU : ∀ a ∈ U, next a ⊆ U) {b : α} :
    b ∈ reachWithin next s U.card ↔
      ∃ a ∈ s, Relation.ReflTransGen (fun x y => y ∈ next x) a b :=
  mem_reachWithin_iff_of_card_le hs hU le_rfl

omit [DecidableEq α] in
theorem ReachIn.succ {k : ℕ} {a b : α} (h : ReachIn next k a b) : ReachIn next (k + 1) a b := by
  induction k generalizing a with
  | zero => exact .inl h
  | succ k ih =>
    rcases h with h | ⟨c, hc, h⟩
    · exact .inl h
    · exact .inr ⟨c, hc, ih h⟩

omit [DecidableEq α] in
theorem ReachIn.snoc {k : ℕ} {a b c : α} (h : ReachIn next k a c) (hb : b ∈ next c) :
    ReachIn next (k + 1) a b := by
  induction k generalizing a with
  | zero =>
    change a = c at h
    subst h
    exact .inr ⟨b, hb, rfl⟩
  | succ k ih =>
    rcases h with rfl | ⟨d, hd, h⟩
    · exact .inr ⟨b, hb, .inl rfl⟩
    · exact .inr ⟨d, hd, ih h⟩

theorem exists_reachIn_of_mem_reachWithin {k : ℕ} {b : α} (hb : b ∈ reachWithin next s k) :
    ∃ a ∈ s, ReachIn next k a b := by
  induction k generalizing b with
  | zero => exact ⟨b, hb, rfl⟩
  | succ k ih =>
    rcases Finset.mem_union.1 (reachWithin_succ (next := next) (s := s) k ▸ hb) with hb | hb
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, ha, h.succ⟩
    · obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.1 hb
      obtain ⟨a, ha, h⟩ := ih hc
      exact ⟨a, ha, h.snoc hbc⟩

omit [DecidableEq α] in
theorem reflTransGen_filter {r : α → α → Prop} [DecidableRel r] (hU : ∀ a ∈ U, ∀ b, r a b → b ∈ U)
    {a b : α} (ha : a ∈ U) (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen (fun x y => y ∈ U.filter (r x)) a b ∧ b ∈ U := by
  induction h with
  | refl => exact ⟨.refl, ha⟩
  | tail _ hcd ih =>
    exact ⟨ih.1.tail (Finset.mem_filter.2 ⟨hU _ ih.2 _ hcd, hcd⟩), hU _ ih.2 _ hcd⟩

theorem reachIn_card_of_reflTransGen {a b : α} (ha : a ∈ U) (hU : ∀ c ∈ U, next c ⊆ U)
    (h : Relation.ReflTransGen (fun x y => y ∈ next x) a b) : ReachIn next U.card a b := by
  obtain ⟨a', ha', h'⟩ := exists_reachIn_of_mem_reachWithin
    ((mem_reachWithin_card_iff (Finset.singleton_subset_iff.2 ha) hU).2
      ⟨a, Finset.mem_singleton_self a, h⟩)
  rw [Finset.mem_singleton] at ha'
  exact ha' ▸ h'

end

end Accordion.WE.Decidability

end
