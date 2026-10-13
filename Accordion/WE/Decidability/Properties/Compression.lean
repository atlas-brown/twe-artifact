module

public import Accordion.WE.Decidability.Properties.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Dedup

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

open scoped List

section Pairs

variable (left : Γ → Bool) (name : Γ → Γ → Γ)

@[simp] lemma compressPairs_nil : compressPairs left name [] = [] := rfl

@[simp] lemma compressPairs_singleton (a : Γ) : compressPairs left name [a] = [a] := rfl

lemma compressPairs_cons_cons (a b : Γ) (w : List Γ) :
    compressPairs left name (a :: b :: w) =
      if IsPair left a b then name a b :: compressPairs left name w
      else a :: compressPairs left name (b :: w) := rfl

lemma compressPairs_cons_of_right {a : Γ} (ha : left a = false) (w : List Γ) :
    compressPairs left name (a :: w) = a :: compressPairs left name w := by
  cases w with
  | nil => rfl
  | cons b w => simp [compressPairs_cons_cons, IsPair, ha]

lemma compressPairs_append (u v : List Γ)
    (h : ∀ a b, u.getLast? = some a → v.head? = some b → ¬IsPair left a b) :
    compressPairs left name (u ++ v) = compressPairs left name u ++ compressPairs left name v := by
  induction u using compressPairs.induct left with
  | case1 a b w hab ih =>
      rw [List.cons_append, List.cons_append, compressPairs_cons_cons, ite_eq_left hab,
        compressPairs_cons_cons, ite_eq_left hab, List.cons_append]
      congr 1
      cases w with
      | nil => simp
      | cons c w => exact ih fun a' b' ha hb ↦ h a' b' (by simpa using ha) hb
  | case2 a b w hab ih =>
      rw [List.cons_append, List.cons_append, compressPairs_cons_cons, ite_eq_right hab,
        compressPairs_cons_cons, ite_eq_right hab, List.cons_append]
      congr 1
      exact ih fun a' b' ha hb ↦ h a' b' (by simpa using ha) hb
  | case3 w hw =>
      match w, hw with
      | _ :: _ :: _, hw => exact (hw _ _ _ rfl).elim
      | [], _ => simp
      | [a], _ =>
          cases v with
          | nil => simp
          | cons b v =>
              simp only [List.cons_append, List.nil_append, compressPairs_cons_cons,
                compressPairs_singleton]
              rw [ite_eq_right (h a b rfl rfl)]

lemma flatMap_compressPairs {expand : Γ → List Γ} {P : Γ → Prop}
    (hname : ∀ a b, P a → P b → expand (name a b) = [a, b]) (hP : ∀ a, P a → expand a = [a]) :
    ∀ w : List Γ, (∀ a ∈ w, P a) → (compressPairs left name w).flatMap expand = w := by
  intro w
  induction w using compressPairs.induct left with
  | case1 a b w hab ih =>
      intro hw
      rw [compressPairs_cons_cons, ite_eq_left hab, List.flatMap_cons,
        hname a b (hw a (by simp)) (hw b (by simp)), ih fun c hc ↦ hw c (by simp [hc])]
      rfl
  | case2 a b w hab ih =>
      intro hw
      rw [compressPairs_cons_cons, ite_eq_right hab, List.flatMap_cons, hP a (hw a (by simp)),
        ih fun c hc ↦ hw c (List.mem_cons_of_mem _ hc)]
      rfl
  | case3 w hw' =>
      intro hw
      match w, hw' with
      | _ :: _ :: _, hw' => exact (hw' _ _ _ rfl).elim
      | [], _ => rfl
      | [a], _ => simp [hP a (hw a (by simp))]

lemma length_compressPairs_le :
    ∀ w : List Γ, List.length (compressPairs left name w) ≤ w.length := by
  intro w
  induction w using compressPairs.induct left with
  | case1 a b w hab ih =>
      rw [compressPairs_cons_cons, ite_eq_left hab]
      simp only [List.length_cons]
      omega
  | case2 a b w hab ih =>
      rw [compressPairs_cons_cons, ite_eq_right hab]
      simpa using ih
  | case3 w hw =>
      match w, hw with
      | _ :: _ :: _, hw => exact (hw _ _ _ rfl).elim
      | [], _ => simp
      | [a], _ => simp

@[simp] lemma adj_nil : adj ([] : List Γ) = [] := rfl

@[simp] lemma adj_singleton (a : Γ) : adj [a] = [] := rfl

@[simp] lemma adj_cons_cons (a b : Γ) (w : List Γ) : adj (a :: b :: w) = (a, b) :: adj (b :: w) :=
  rfl

lemma adj_map (ρ : Γ → Γ) (w : List Γ) :
    adj (w.map ρ) = (adj w).map fun p ↦ (ρ p.1, ρ p.2) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => rfl
      | cons b w =>
          simp only [List.map_cons] at ih ⊢
          rw [adj_cons_cons, ih, adj_cons_cons, List.map_cons]

lemma exists_adj_eq_map (ρ : Γ → Γ) {w : List Γ} (h : ∃ p ∈ adj w, p.1 = p.2) :
    ∃ p ∈ adj (w.map ρ), p.1 = p.2 := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨(ρ p.1, ρ p.2), by rw [adj_map]; exact List.mem_map_of_mem hp, by simp [h]⟩

lemma pairCount_cons_of_right {b : Γ} (hb : left b = false) (w : List Γ) :
    pairCount left (b :: w) = pairCount left w := by
  cases w with
  | nil => rfl
  | cons c w => simp [pairCount, IsPair, hb]

lemma length_compressPairs_add (w : List Γ) :
    List.length (compressPairs left name w) + pairCount left w = w.length := by
  induction w using compressPairs.induct left with
  | case1 a b w hab ih =>
      rw [compressPairs_cons_cons, ite_eq_left hab]
      have h : pairCount left (a :: b :: w) = pairCount left (b :: w) + 1 := by
        simp [pairCount, hab]
      rw [h, pairCount_cons_of_right left hab.2]
      simp only [List.length_cons] at ih ⊢
      omega
  | case2 a b w hab ih =>
      rw [compressPairs_cons_cons, ite_eq_right hab]
      have h : pairCount left (a :: b :: w) = pairCount left (b :: w) := by
        simp [pairCount, hab]
      rw [h]
      simp only [List.length_cons] at ih ⊢
      omega
  | case3 w hw =>
      match w, hw with
      | _ :: _ :: _, hw => exact (hw _ _ _ rfl).elim
      | [], _ => rfl
      | [a], _ => rfl

end Pairs

section Blocks

variable [DecidableEq Γ]

lemma consRun_ne_nil (a : Γ) (r : List (Γ × Nat)) : consRun a r ≠ [] := by
  unfold consRun; split <;> [split_ifs <;> simp; simp]

lemma consRun_append (a : Γ) {X : List (Γ × Nat)} (hX : X ≠ []) (r : List (Γ × Nat)) :
    consRun a (X ++ r) = consRun a X ++ r := by
  obtain ⟨⟨b, k⟩, X, rfl⟩ := List.exists_cons_of_ne_nil hX
  simp only [List.cons_append, consRun]
  split_ifs <;> rfl

lemma runs_ne_nil {w : List Γ} (hw : w ≠ []) : runs w ≠ [] := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  exact consRun_ne_nil a _

lemma runs_head? (w : List Γ) : ((runs w).head?.map Prod.fst) = w.head? := by
  cases w with
  | nil => rfl
  | cons a w =>
      change ((consRun a (runs w)).head?.map Prod.fst) = _
      unfold consRun
      split <;> [split_ifs <;> rfl; rfl]

lemma foldr_consRun (r : List (Γ × Nat)) :
    ∀ u : List Γ, (∀ a, u.getLast? = some a → r.head?.map Prod.fst ≠ some a) →
      u.foldr consRun r = runs u ++ r
  | [], _ => rfl
  | [a], h => by
      have h := h a rfl
      change consRun a r = consRun a [] ++ r
      rcases r with _ | ⟨⟨b, k⟩, r⟩
      · rfl
      · have hab : a ≠ b := fun hab ↦ h (by simp [hab])
        simp [consRun, hab]
  | a :: c :: u, h => by
      rw [List.foldr_cons, foldr_consRun r (c :: u) fun a' ha' ↦ h a' (by simpa using ha')]
      exact consRun_append a (runs_ne_nil (List.cons_ne_nil c u)) r

lemma runs_append (u v : List Γ) (h : ∀ a, u.getLast? = some a → v.head? ≠ some a) :
    runs (u ++ v) = runs u ++ runs v := by
  rw [runs, List.foldr_append]
  exact foldr_consRun (runs v) u fun a ha ↦ by rw [runs_head?]; exact h a ha

lemma compressBlocks_append (name : Γ → Nat → Γ) (u v : List Γ)
    (h : ∀ a, u.getLast? = some a → v.head? ≠ some a) :
    compressBlocks name (u ++ v) = compressBlocks name u ++ compressBlocks name v := by
  simp [compressBlocks, runs_append u v h]

lemma length_compressBlocks (name : Γ → Nat → Γ) (w : List Γ) :
    List.length (compressBlocks name w) = (runs w).length := by
  simp [compressBlocks]

lemma length_runs_add (w : List Γ) :
    (runs w).length + (adj w).countP (fun p ↦ p.1 = p.2) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change (consRun a (runs w)).length + _ = _
      have hh := runs_head? w
      rcases w with _ | ⟨b, w⟩
      · rfl
      · rw [adj_cons_cons, List.countP_cons]
        rcases hr : runs (b :: w) with _ | ⟨⟨c, k⟩, r⟩
        · exact absurd hr (runs_ne_nil (List.cons_ne_nil b w))
        · rw [hr] at hh ih
          have hc : c = b := by simpa using hh
          subst hc
          by_cases hab : a = c
          · subst hab
            have h1 : consRun a ((a, k) :: r) = (a, k + 1) :: r := by simp [consRun]
            rw [h1]
            simp only [List.length_cons, decide_true, ite_true] at ih ⊢
            omega
          · have h1 : consRun a ((c, k) :: r) = (a, 1) :: (c, k) :: r := by simp [consRun, hab]
            rw [h1]
            simp only [List.length_cons, hab, decide_false] at ih ⊢
            simp only [Bool.false_eq_true, ite_false] at ih ⊢
            omega

lemma runs_replicate (a : Γ) {k : Nat} (hk : 0 < k) : runs (List.replicate k a) = [(a, k)] := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases k with _ | k
      · rfl
      · change consRun a (runs (List.replicate (k + 1) a)) = _
        rw [ih (by omega)]
        simp [consRun]

lemma runs_flatMap_replicate :
    ∀ R : List (Γ × Nat), (∀ p ∈ R, 0 < p.2) → R.IsChain (fun p q ↦ p.1 ≠ q.1) →
      runs (R.flatMap fun p ↦ List.replicate p.2 p.1) = R
  | [], _, _ => rfl
  | (a, k) :: R, hpos, hchain => by
      rw [List.flatMap_cons, runs_append, runs_replicate a (hpos _ (by simp)),
        runs_flatMap_replicate R (fun p hp ↦ hpos p (List.mem_cons_of_mem _ hp)) hchain.tail]
      · rfl
      · intro c hc hR
        have hk := hpos _ (List.mem_cons_self ..)
        rw [List.getLast?_replicate] at hc
        simp only [Nat.ne_of_gt hk, ite_false, Option.some.injEq] at hc
        subst hc
        rcases R with _ | ⟨⟨b, j⟩, R⟩
        · simp at hR
        · have hj := hpos (b, j) (by simp)
          have hab := List.isChain_cons.1 hchain |>.1
          rw [List.flatMap_cons, List.head?_append, List.head?_replicate] at hR
          simp only [Nat.ne_of_gt hj, ite_false, Option.some_or, Option.some.injEq] at hR
          exact hab (b, j) rfl hR.symm

lemma compressBlocks_flatMap_replicate (name : Γ → Nat → Γ) (R : List (Γ × Nat))
    (hpos : ∀ p ∈ R, 0 < p.2) (hchain : R.IsChain (fun p q ↦ p.1 ≠ q.1)) :
    compressBlocks name (R.flatMap fun p ↦ List.replicate p.2 p.1) =
      R.map fun p ↦ name p.1 p.2 := by
  rw [compressBlocks, runs_flatMap_replicate R hpos hchain]

lemma length_runs_le (w : List Γ) : (runs w).length ≤ w.length := by
  have := length_runs_add w
  omega

end Blocks

lemma length_compressPairs_le' (left : Γ → Bool) (name : Γ → Γ → Γ) (w : List Γ) :
    List.length (compressPairs left name w) ≤ w.length := by
  have := length_compressPairs_add left name w
  omega

lemma compressPairs_of_right {left : Γ → Bool} (h : ∀ a, left a = false)
    (name : Γ → Γ → Γ) : ∀ w : List Γ, compressPairs left name w = w
  | [] => rfl
  | a :: w => by rw [compressPairs_cons_of_right left name (h a), compressPairs_of_right h name w]

@[simp] lemma substSide_nil (g : V.Word → Side Γ V) : substSide g [] = [] := rfl

@[simp] lemma substSide_cons_letter (g : V.Word → Side Γ V) (a : Γ) (u : Side Γ V) :
    substSide g (.inl a :: u) = .inl a :: substSide g u := rfl

@[simp] lemma substSide_cons_var (g : V.Word → Side Γ V) (x : V.Word) (u : Side Γ V) :
    substSide g (.inr x :: u) = g x ++ substSide g u := rfl

lemma eval_substSide (σ : Subst Γ V) (g : V.Word → Side Γ V) (u : Side Γ V) :
    eval σ (substSide g u) = eval (fun x ↦ eval σ (g x)) u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

lemma Eqn.solves_of_substSide {e : Eqn Γ V} {g : V.Word → Side Γ V} {σ : Subst Γ V}
    (h : (e.map (substSide g)).Solves σ) : e.Solves fun x ↦ eval σ (g x) := by
  simpa [Eqn.Solves, Eqn.map, eval_substSide] using h

lemma mem_sideLetters_substSide {g : V.Word → Side Γ V} {u : Side Γ V} {a : Γ}
    (h : a ∈ sideLetters (substSide g u)) :
    a ∈ sideLetters u ∨ ∃ x ∈ sideVars u, a ∈ sideLetters (g x) := by
  induction u with
  | nil => simp at h
  | cons s u ih =>
      cases s with
      | inl b =>
          simp only [substSide_cons_letter, sideLetters_cons_letter, List.mem_cons] at h
          rcases h with rfl | h
          · simp
          · rcases ih h with h | ⟨x, hx, h⟩
            · simp [h]
            · exact .inr ⟨x, by simpa using hx, h⟩
      | inr y =>
          simp only [substSide_cons_var, sideLetters_append, List.mem_append] at h
          rcases h with h | h
          · exact .inr ⟨y, by simp, h⟩
          · rcases ih h with h | ⟨x, hx, h⟩
            · simp [h]
            · exact .inr ⟨x, by simp [hx], h⟩

lemma mem_sideVars_substSide {g : V.Word → Side Γ V} {u : Side Γ V} {x : V.Word}
    (h : x ∈ sideVars (substSide g u)) : ∃ y ∈ sideVars u, x ∈ sideVars (g y) := by
  induction u with
  | nil => simp at h
  | cons s u ih =>
      cases s with
      | inl b =>
          obtain ⟨y, hy, h⟩ := ih (by simpa using h)
          exact ⟨y, by simpa using hy, h⟩
      | inr y =>
          simp only [substSide_cons_var, sideVars_append, List.mem_append] at h
          rcases h with h | h
          · exact ⟨y, by simp, h⟩
          · obtain ⟨z, hz, h⟩ := ih h
            exact ⟨z, by simp [hz], h⟩

lemma substSide_congr {g g' : V.Word → Side Γ V} {u : Side Γ V}
    (h : ∀ x ∈ sideVars u, g x = g' x) : substSide g u = substSide g' u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a => simp [ih (by simpa using h)]
      | inr x => simp [h x (by simp), ih fun y hy ↦ h y (by simp [hy])]

@[simp] lemma expandSide_nil (h : Γ → List Γ) : expandSide h ([] : Side Γ V) = [] := rfl

@[simp] lemma expandSide_cons_letter (h : Γ → List Γ) (a : Γ) (u : Side Γ V) :
    expandSide h (.inl a :: u) = letters (h a) ++ expandSide h u := rfl

@[simp] lemma expandSide_cons_var (h : Γ → List Γ) (x : V.Word) (u : Side Γ V) :
    expandSide h (.inr x :: u) = .inr x :: expandSide h u := rfl

@[simp] lemma expandSide_append (h : Γ → List Γ) (u v : Side Γ V) :
    expandSide h (u ++ v) = expandSide h u ++ expandSide h v := by
  simp [expandSide]

@[simp] lemma expandSide_letters (h : Γ → List Γ) (w : List Γ) :
    expandSide h (letters w : Side Γ V) = letters (w.flatMap h) := by
  induction w <;> simp_all [letters]

lemma eval_expandSide (τ : Subst Γ V) (h : Γ → List Γ) (u : Side Γ V) :
    eval (fun x ↦ (τ x).flatMap h) (expandSide h u) = (eval τ u).flatMap h := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

lemma Eqn.solves_expandSide {e : Eqn Γ V} {τ : Subst Γ V} (h : Γ → List Γ)
    (hτ : e.Solves τ) : (e.map (expandSide h)).Solves fun x ↦ (τ x).flatMap h := by
  simp only [Eqn.Solves, Eqn.map, eval_expandSide]
  rw [hτ]

@[simp] lemma sideLetters_expandSide (h : Γ → List Γ) (u : Side Γ V) :
    sideLetters (expandSide h u) = (sideLetters u).flatMap h := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

@[simp] lemma sideVars_expandSide (h : Γ → List Γ) (u : Side Γ V) :
    sideVars (expandSide h u) = sideVars u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

theorem side_induction {P : Side Γ V → Prop} (h₁ : ∀ q, P (letters q))
    (h₂ : ∀ q x r, P r → P (letters q ++ .inr x :: r)) (u : Side Γ V) : P u := by
  suffices ∀ q, P (letters q ++ u) by simpa [letters] using this []
  induction u with
  | nil => intro q; simpa using h₁ q
  | cons s u ih =>
      intro q
      cases s with
      | inl a => simpa [letters] using ih (q ++ [a])
      | inr x => exact h₂ q x u (by simpa [letters] using ih [])

lemma mapRunsFrom_letters_append (f : List Γ → List Γ) (q p : List Γ) (u : Side Γ V) :
    mapRunsFrom f q (letters p ++ u) = mapRunsFrom f (q ++ p) u := by
  induction p generalizing q with
  | nil => simp [letters]
  | cons a p ih =>
      change mapRunsFrom f (q ++ [a]) (letters p ++ u) = _
      rw [ih]
      simp

@[simp] lemma mapRuns_letters (f : List Γ → List Γ) (q : List Γ) :
    mapRuns f (letters q : Side Γ V) = letters (f q) := by
  simpa [mapRuns, mapRunsFrom] using mapRunsFrom_letters_append (V := V) f [] q []

@[simp] lemma mapRuns_letters_var (f : List Γ → List Γ) (q : List Γ) (x : V.Word)
    (r : Side Γ V) :
    mapRuns f (letters q ++ .inr x :: r) = letters (f q) ++ .inr x :: mapRuns f r := by
  simp [mapRuns, mapRunsFrom_letters_append, mapRunsFrom]

@[simp] lemma sideVars_mapRuns (f : List Γ → List Γ) (u : Side Γ V) :
    sideVars (mapRuns f u) = sideVars u := by
  induction u using side_induction <;> simp_all

@[simp] lemma adjSide_letters (q : List Γ) : adjSide (letters q : Side Γ V) = adj q := by
  induction q with
  | nil => rfl
  | cons a q ih => cases q <;> simp_all [letters, adjSide]

@[simp] lemma adjSide_letters_var (q : List Γ) (x : V.Word) (r : Side Γ V) :
    adjSide (letters q ++ .inr x :: r) = adj q ++ adjSide r := by
  induction q with
  | nil => rfl
  | cons a q ih => cases q <;> simp_all [letters, adjSide]

lemma adjSide_sublist_cons (s : Sym Γ V) (u : Side Γ V) : adjSide u <+ adjSide (s :: u) := by
  rcases s with a | x
  · rcases u with _ | ⟨_ | _, u⟩ <;> simp [adjSide]
  · rfl

lemma adjSide_append_sublist : ∀ u v : Side Γ V, adjSide u ++ adjSide v <+ adjSide (u ++ v)
  | [], _ => by simp [adjSide]
  | .inr _ :: u, v => adjSide_append_sublist u v
  | [.inl a], v => by simpa [adjSide] using adjSide_sublist_cons (.inl a) v
  | .inl _ :: .inr x :: u, v => adjSide_append_sublist (.inr x :: u) v
  | .inl a :: .inl b :: u, v => by
      simpa [adjSide] using adjSide_append_sublist (.inl b :: u) v

lemma adjSide_sublist_substSide (g : V.Word → Side Γ V) : ∀ u : Side Γ V,
    adjSide u <+ adjSide (substSide g u)
  | [] => by simp
  | .inr x :: u => by
      simpa [adjSide] using (adjSide_sublist_substSide g u).trans
        ((List.sublist_append_right _ _).trans (adjSide_append_sublist (g x) (substSide g u)))
  | [.inl a] => by simp [adjSide]
  | .inl a :: .inr x :: u => by
      simpa [adjSide] using (adjSide_sublist_substSide g (.inr x :: u)).trans
        (adjSide_sublist_cons (.inl a) _)
  | .inl a :: .inl b :: u => by
      simpa [adjSide] using adjSide_sublist_substSide g (.inl b :: u)

lemma length_sideLetters_mapRuns {f : List Γ → List Γ} {R : Γ → Γ → Prop}
    [DecidableRel R] (hf : ∀ q, (f q).length + (adj q).countP (fun p ↦ R p.1 p.2) = q.length)
    (u : Side Γ V) :
    (sideLetters (mapRuns f u)).length + (adjSide u).countP (fun p ↦ R p.1 p.2) =
      (sideLetters u).length := by
  induction u using side_induction with
  | h₁ q => simpa using hf q
  | h₂ q x r ih =>
      have := hf q
      simp only [mapRuns_letters_var, sideLetters_append, sideLetters_letters,
        sideLetters_cons_var, List.length_append, adjSide_letters_var, List.countP_append] at ih ⊢
      omega

lemma length_sideLetters_substSide_le {g : V.Word → Side Γ V} {k : Nat} (u : Side Γ V)
    (hg : ∀ x ∈ sideVars u, (sideLetters (g x)).length ≤ k) :
    (sideLetters (substSide g u)).length ≤ (sideLetters u).length + k * (sideVars u).length := by
  induction u with
  | nil => simp
  | cons s u ih =>
      cases s with
      | inl a =>
          have := ih (by simpa using hg)
          simp only [substSide_cons_letter, sideLetters_cons_letter, List.length_cons,
            sideVars_cons_letter]
          omega
      | inr x =>
          have h1 := hg x (by simp)
          have h2 := ih fun y hy ↦ hg y (by simp [hy])
          simp only [substSide_cons_var, sideLetters_append, List.length_append, sideVars_cons_var,
            sideLetters_cons_var, List.length_cons]
          rw [Nat.mul_succ]
          omega

lemma sideVars_substSide_sublist {g : V.Word → Side Γ V} (u : Side Γ V)
    (hg : ∀ x ∈ sideVars u, sideVars (g x) <+ [x]) : sideVars (substSide g u) <+ sideVars u := by
  induction u with
  | nil => simp
  | cons s u ih =>
      cases s with
      | inl a => simpa using ih (by simpa using hg)
      | inr x =>
          simpa using (hg x (by simp)).append (ih fun y hy ↦ hg y (by simp [hy]))

lemma expandSide_mapRuns {f : List Γ → List Γ} {h : Γ → List Γ} {P : Γ → Prop}
    (hfh : ∀ q, (∀ a ∈ q, P a) → (f q).flatMap h = q) (u : Side Γ V)
    (hu : ∀ a ∈ sideLetters u, P a) : expandSide h (mapRuns f u) = u := by
  induction u using side_induction with
  | h₁ q => simp_all
  | h₂ q x r ih =>
      simp only [sideLetters_append, sideLetters_letters, sideLetters_cons_var, List.mem_append]
        at hu
      simp [hfh q fun a ha ↦ hu a (.inl ha), ih fun a ha ↦ hu a (.inr ha)]

lemma eval_mapRuns_substSide (f : List Γ → List Γ) (g : V.Word → Side Γ V) (σ σ' : Subst Γ V)
    (u : Side Γ V)
    (hg : ∀ x ∈ sideVars u, g x = letters (σ x) ∨
      ∃ pre post, g x = letters pre ++ .inr x :: letters post ∧ σ x = pre ++ σ' x ++ post ∧
        ∀ q E, f (q ++ pre ++ σ' x ++ post ++ E) = f (q ++ pre) ++ f (σ' x) ++ f (post ++ E))
    (p : List Γ) :
    f (p ++ eval σ u) = eval (fun x ↦ f (σ' x)) (mapRuns f (letters p ++ substSide g u)) := by
  induction u generalizing p with
  | nil => simp
  | cons s u ih =>
      cases s with
      | inl a =>
          have := ih (fun x hx ↦ hg x (by simpa using hx)) (p ++ [a])
          simpa [letters] using this
      | inr x =>
          have ih := ih (fun x hx ↦ hg x (by simp [hx]))
          rcases hg x (by simp) with hx | ⟨pre, post, hx, hσ, hf⟩
          · have := ih (p ++ σ x)
            simpa [hx, letters] using this
          · have h1 : letters p ++ substSide g (.inr x :: u) =
                letters (p ++ pre) ++ .inr x :: (letters post ++ substSide g u) := by
              simp [hx, letters]
            rw [h1, mapRuns_letters_var]
            simp only [eval_append, eval_letters, eval_cons, eval_var]
            rw [← ih post, hσ]
            simpa using hf p (eval σ u)

section

variable (ρ : Γ → Γ)

@[simp] lemma renameSide_nil : renameSide ρ ([] : Side Γ V) = [] := rfl

@[simp] lemma renameSide_cons_letter (a : Γ) (u : Side Γ V) :
    renameSide ρ (.inl a :: u) = .inl (ρ a) :: renameSide ρ u := rfl

@[simp] lemma renameSide_cons_var (x : V.Word) (u : Side Γ V) :
    renameSide ρ (.inr x :: u) = .inr x :: renameSide ρ u := rfl

lemma eval_renameSide (σ : Subst Γ V) (u : Side Γ V) :
    eval (fun x ↦ (σ x).map ρ) (renameSide ρ u) = (eval σ u).map ρ := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

@[simp] lemma sideLetters_renameSide (u : Side Γ V) :
    sideLetters (renameSide ρ u) = (sideLetters u).map ρ := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

@[simp] lemma sideVars_renameSide (u : Side Γ V) : sideVars (renameSide ρ u) = sideVars u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

lemma adjSide_renameSide : ∀ u : Side Γ V,
    adjSide (renameSide ρ u) = (adjSide u).map fun p ↦ (ρ p.1, ρ p.2)
  | [] => rfl
  | .inr _ :: u => adjSide_renameSide u
  | [.inl _] => rfl
  | .inl _ :: .inr x :: u => adjSide_renameSide (.inr x :: u)
  | .inl a :: .inl b :: u => by
      simp only [renameSide_cons_letter, adjSide, List.map_cons]
      rw [← renameSide_cons_letter, adjSide_renameSide (.inl b :: u)]

lemma renameSide_renameSide (ρ' : Γ → Γ) {u : Side Γ V}
    (h : ∀ a ∈ sideLetters u, ρ' (ρ a) = a) : renameSide ρ' (renameSide ρ u) = u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a =>
          simp only [sideLetters_cons_letter, List.mem_cons, forall_eq_or_imp] at h
          simp [h.1, ih h.2]
      | inr x => simp [ih (by simpa using h)]

lemma renameSide_eq_self {u : Side Γ V} (h : ∀ a ∈ sideLetters u, ρ a = a) :
    renameSide ρ u = u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a =>
          simp only [sideLetters_cons_letter, List.mem_cons, forall_eq_or_imp] at h
          simp [h.1, ih h.2]
      | inr x => simp [ih (by simpa using h)]

end

namespace Eqn

section

variable (ρ : Γ → Γ) (e : Eqn Γ V)

lemma solves_rename {σ : Subst Γ V} (h : e.Solves σ) :
    (e.rename ρ).Solves fun x ↦ (σ x).map ρ := by
  simp only [Solves, rename, map, eval_renameSide]
  rw [h]

lemma rename_rename (ρ' : Γ → Γ) (h : ∀ a ∈ e.letters, ρ' (ρ a) = a) :
    (e.rename ρ).rename ρ' = e := by
  simp only [rename, map]
  rw [renameSide_renameSide ρ ρ' fun a ha ↦ h a (by simp [letters, ha]),
    renameSide_renameSide ρ ρ' fun a ha ↦ h a (by simp [letters, ha])]

@[simp] lemma letters_rename : (e.rename ρ).letters = e.letters.map ρ := by
  simp [rename, map, letters]

@[simp] lemma vars_rename : (e.rename ρ).vars = e.vars := by
  simp [rename, map, vars]

end

variable [DecidableEq Γ] (e : Eqn Γ V)

lemma letterIndex_inj {a b : Γ} (ha : a ∈ e.letters) (h : e.letterIndex a = e.letterIndex b) :
    a = b :=
  (List.idxOf_inj (List.mem_dedup.2 ha)).1 h

lemma letterIndex_lt {a : Γ} (ha : a ∈ e.letters) : e.letterIndex a < e.letters.length :=
  (List.idxOf_lt_length_of_mem (List.mem_dedup.2 ha)).trans_le (List.dedup_sublist _).length_le

end Eqn

lemma Eqn.exists_solves_letters [DecidableEq Γ] {e : Eqn Γ V} {σ : Subst Γ V}
    (hσ : e.Solves σ) :
    ∃ σ', e.Solves σ' ∧ (∀ x, ∀ a ∈ σ' x, a ∈ e.letters) ∧
      List.length (eval σ' e.1) ≤ List.length (eval σ e.1) ∧
      ((∃ p ∈ Decidability.adj (eval σ e.1), p.1 = p.2) →
        (∃ p ∈ Decidability.adj (eval σ' e.1), p.1 = p.2) ∨
          List.length (eval σ' e.1) < List.length (eval σ e.1)) := by
  rcases hA : e.letters with _ | ⟨a₀, A⟩
  · have hl : sideLetters e.1 = [] ∧ sideLetters e.2 = [] := by
      simpa [Eqn.letters] using hA
    have hnil : ∀ u : Side Γ V, sideLetters u = [] → eval (fun _ ↦ []) u = [] := by
      intro u hu
      induction u with
      | nil => rfl
      | cons s u ih => cases s <;> simp_all
    refine ⟨fun _ ↦ [], ?_, by simp, by simp [hnil _ hl.1], fun ⟨p, hp, _⟩ ↦ ?_⟩
    · simp [Eqn.Solves, hnil _ hl.1, hnil _ hl.2]
    · right
      rw [hnil _ hl.1]
      rcases h : eval σ e.1 with _ | ⟨c, w⟩
      · simp [h] at hp
      · simp
  · let ρ : Γ → Γ := fun c ↦ if c ∈ e.letters then c else a₀
    have hside : ∀ u : Side Γ V, (∀ a ∈ sideLetters u, a ∈ e.letters) → renameSide ρ u = u :=
      fun u hu ↦ renameSide_eq_self ρ fun a ha ↦ by simp [ρ, hu a ha]
    have hl : renameSide ρ e.1 = e.1 := hside _ fun a ha ↦ by simp [Eqn.letters, ha]
    have hρ : e.rename ρ = e := by
      simp only [Eqn.rename, Eqn.map, hl,
        hside e.2 fun a ha ↦ by simp [Eqn.letters, ha]]
    have hval : eval (fun x ↦ (σ x).map ρ) e.1 = (eval σ e.1).map ρ := by
      have := eval_renameSide ρ σ e.1
      rwa [hl] at this
    refine ⟨fun x ↦ (σ x).map ρ, ?_, ?_, by simp [hval], fun h ↦ .inl ?_⟩
    · have := e.solves_rename ρ hσ
      rwa [hρ] at this
    · intro x a ha
      simp only [List.mem_map] at ha
      obtain ⟨c, -, rfl⟩ := ha
      rw [← hA]
      by_cases hc : c ∈ e.letters
      · simp only [ρ, ite_eq_left hc]
        exact hc
      · simp only [ρ, ite_eq_right hc]
        rw [hA]
        exact List.mem_cons_self ..
    · rw [hval]
      exact exists_adj_eq_map ρ h

end Accordion.WE.Decidability

end
