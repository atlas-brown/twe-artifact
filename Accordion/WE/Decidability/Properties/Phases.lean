module

public import Accordion.WE.Decidability.Properties.PairComp
public import Accordion.WE.Decidability.Properties.BlockComp
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Accordion.WE.Decidability

open scoped List

variable {Γ : Type} {V : Vars}

lemma length_adj (w : List Γ) : (adj w).length = w.length - 1 := by
  simp [adj]

lemma length_sideLetters_le (u : Side Γ V) :
    (sideLetters u).length ≤ (adjSide u).length + (sideVars u).length + 1 := by
  induction u using side_induction with
  | h₁ q => simp [length_adj]; omega
  | h₂ q x r ih =>
      simp only [sideLetters_append, sideLetters_letters, sideLetters_cons_var, List.length_append,
        adjSide_letters_var, length_adj, sideVars_append, sideVars_letters, sideVars_cons_var,
        List.length_cons, List.nil_append] at ih ⊢
      omega

lemma Eqn.letterCount_le_adj (e : Eqn Γ V) :
    e.letterCount ≤ e.adj.length + e.varCount + 2 := by
  have h1 := length_sideLetters_le e.1
  have h2 := length_sideLetters_le e.2
  simp only [Eqn.letterCount, Eqn.letters, Eqn.adj, Eqn.varCount, Eqn.vars, List.length_append]
  omega

lemma mem_adj_letters {w : List Γ} {p : Γ × Γ} (hp : p ∈ adj w) : p.1 ∈ w ∧ p.2 ∈ w :=
  ⟨List.of_mem_zip hp |>.1, List.mem_of_mem_tail (List.of_mem_zip hp).2⟩

lemma mem_adjSide_letters : ∀ {u : Side Γ V} {p : Γ × Γ}, p ∈ adjSide u →
    p.1 ∈ sideLetters u ∧ p.2 ∈ sideLetters u
  | [], _, h => by simp [adjSide] at h
  | .inr _ :: u, _, h => by simpa using mem_adjSide_letters (u := u) h
  | [.inl _], _, h => by simp [adjSide] at h
  | .inl _ :: .inr x :: u, _, h => by
      have := mem_adjSide_letters (u := .inr x :: u) h
      simp only [sideLetters_cons_var] at this
      simp [this]
  | .inl a :: .inl b :: u, p, h => by
      simp only [adjSide, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := mem_adjSide_letters (u := .inl b :: u) h
        simp only [sideLetters_cons_letter, List.mem_cons] at this ⊢
        exact ⟨.inr this.1, .inr this.2⟩

lemma Eqn.mem_adj_letters {e : Eqn Γ V} {p : Γ × Γ} (hp : p ∈ e.adj) :
    p.1 ∈ e.letters ∧ p.2 ∈ e.letters := by
  simp only [Eqn.adj, List.mem_append] at hp
  rcases hp with hp | hp
  · have := mem_adjSide_letters hp
    simp [Eqn.letters, this]
  · have := mem_adjSide_letters hp
    simp [Eqn.letters, this]

lemma length_compressPairs_lt (left : Γ → Bool) (name : Γ → Γ → Γ) {w : List Γ}
    (h : ∃ p ∈ adj w, IsPair left p.1 p.2) :
    List.length (compressPairs left name w) < w.length := by
  have := length_compressPairs_add left name w
  have : 0 < pairCount left w := List.countP_pos_iff.2 (by simpa using h)
  omega

lemma exists_mem_adj {w : List Γ} (hw : 2 ≤ w.length) : ∃ p, p ∈ adj w := by
  rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
  · simp at hw
  · simp at hw
  · exact ⟨(a, b), by simp⟩

lemma length_eq_of_sideVars_eq_nil {σ : Subst Γ V} {u : Side Γ V} (h : sideVars u = []) :
    u.length = List.length (eval σ u) := by
  rw [eval_of_sideVars_eq_nil h, length_side, h]
  rfl

lemma countUpTo_le_pow (s : Nat) : ∀ k, countUpTo s k ≤ (s + 1) ^ k
  | 0 => le_rfl
  | k + 1 => by
      have := countUpTo_le_pow s k
      have h1 : 1 ≤ (s + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      calc countUpTo s (k + 1) = 1 + s * countUpTo s k := rfl
        _ ≤ (s + 1) ^ k + s * (s + 1) ^ k := Nat.add_le_add h1 (Nat.mul_le_mul_left _ this)
        _ = (s + 1) ^ (k + 1) := by ring

lemma size_sq_countUpTo_add_two_le (s k : Nat) :
    Nat.size (countUpTo s k ^ 2 + 2) ≤ 2 * k * Nat.size (s + 1) + 3 := by
  rw [Nat.size_le]
  have h1 : countUpTo s k ^ 2 ≤ (2 ^ Nat.size (s + 1)) ^ (2 * k) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left
      ((countUpTo_le_pow s k).trans (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)) 2
  rw [← pow_mul, mul_comm] at h1
  have h2 : 0 < 2 ^ (2 * k * Nat.size (s + 1)) := Nat.two_pow_pos _
  rw [pow_add]
  omega

namespace Eqn

section

variable [DecidableEq Γ]

lemma renumber_apply {L₀ : List Γ} {e : Eqn Γ V} (he : e.letterCount ≤ L₀.length) {a : Γ}
    (ha : a ∈ e.letters) :
    (L₀[e.letterIndex a]?).getD a = L₀[e.letterIndex a]'((e.letterIndex_lt ha).trans_le he) := by
  simp [List.getElem?_eq_getElem ((e.letterIndex_lt ha).trans_le he)]

lemma renumber_injOn {L₀ : List Γ} (hL : L₀.Nodup) {e : Eqn Γ V}
    (he : e.letterCount ≤ L₀.length) {a b : Γ} (ha : a ∈ e.letters) (hb : b ∈ e.letters)
    (h : (L₀[e.letterIndex a]?).getD a = (L₀[e.letterIndex b]?).getD b) : a = b := by
  rw [renumber_apply he ha, renumber_apply he hb] at h
  exact e.letterIndex_inj ha (hL.getElem_inj_iff.1 h)

theorem renumber_solvable_iff {L₀ : List Γ} (hL : L₀.Nodup) {e : Eqn Γ V}
    (he : e.letterCount ≤ L₀.length) : (e.renumber L₀).Solvable ↔ e.Solvable := by
  constructor
  · rintro ⟨τ, hτ⟩
    have := solves_rename (fun c ↦ (e.letters.dedup[L₀.idxOf c]?).getD c) (e.renumber L₀) hτ
    rw [renumber, rename_rename] at this
    · exact ⟨_, this⟩
    · intro a ha
      have h := List.idxOf_lt_length_of_mem (List.mem_dedup.2 ha)
      rw [renumber_apply he ha, hL.idxOf_getElem]
      simp [letterIndex, List.getElem?_eq_getElem h]
  · rintro ⟨σ, hσ⟩
    exact ⟨_, solves_rename _ e hσ⟩

theorem letters_renumber_subset {L₀ : List Γ} {e : Eqn Γ V} (he : e.letterCount ≤ L₀.length) :
    ∀ c ∈ (e.renumber L₀).letters, c ∈ L₀ := by
  intro c hc
  simp only [renumber, letters_rename, List.mem_map] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  rw [renumber_apply he ha]
  exact List.getElem_mem _

@[simp] lemma letterCount_renumber (L₀ : List Γ) (e : Eqn Γ V) :
    (e.renumber L₀).letterCount = e.letterCount := by
  simp [letterCount, renumber]

@[simp] lemma vars_renumber (L₀ : List Γ) (e : Eqn Γ V) : (e.renumber L₀).vars = e.vars := by
  simp [renumber]

@[simp] lemma varCount_renumber (L₀ : List Γ) (e : Eqn Γ V) :
    (e.renumber L₀).varCount = e.varCount := by
  simp [varCount]

@[simp] lemma size_renumber (L₀ : List Γ) (e : Eqn Γ V) : (e.renumber L₀).size = e.size := by
  simp [size_eq]

lemma noSquare_renumber {L₀ : List Γ} (hL : L₀.Nodup) {e : Eqn Γ V}
    (he : e.letterCount ≤ L₀.length) (h : e.NoSquare) : (e.renumber L₀).NoSquare := by
  intro p hp
  simp only [adj, renumber, rename, map, adjSide_renameSide, ← List.map_append,
    List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hq' : q ∈ e.adj := hq
  exact fun h' ↦ h q hq'
    (renumber_injOn hL he (e.mem_adj_letters hq').1 (e.mem_adj_letters hq').2 h')

end

end Eqn

section

variable [DecidableEq Γ]

lemma length_runs_lt {w : List Γ} (h : ∃ p ∈ adj w, p.1 = p.2) :
    (runs w).length < w.length := by
  have := length_runs_add w
  have : 0 < (adj w).countP fun p ↦ p.1 = p.2 := List.countP_pos_iff.2 (by simpa using h)
  omega

open Finset in
lemma card_separating (A : Finset Γ) {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    4 * (A.powerset.filter fun T ↦ a ∈ T ∧ b ∉ T).card = 2 ^ A.card := by
  have himg : (A.powerset.filter fun T ↦ a ∈ T ∧ b ∉ T) =
      ((A.erase a).erase b).powerset.image (insert a) := by
    ext T
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hT, haT, hbT⟩
      refine ⟨T.erase a, ?_, insert_erase haT⟩
      intro c hc
      simp only [mem_erase] at hc ⊢
      exact ⟨fun h ↦ hbT (h ▸ hc.2), hc.1, hT hc.2⟩
    · rintro ⟨U, hU, rfl⟩
      refine ⟨insert_subset ha fun c hc ↦ ?_, mem_insert_self _ _, fun h ↦ ?_⟩
      · exact mem_of_mem_erase (mem_of_mem_erase (hU hc))
      · rcases mem_insert.1 h with h | h
        · exact hab h.symm
        · have := hU h
          simp at this
  have hinj : Set.InjOn (insert a) (((A.erase a).erase b).powerset : Set (Finset Γ)) := by
    intro U hU W hW h
    have hU' : a ∉ U := fun h' ↦ by
      have := (mem_powerset.1 hU) h'
      simp at this
    have hW' : a ∉ W := fun h' ↦ by
      have := (mem_powerset.1 hW) h'
      simp at this
    rw [← erase_insert hU', ← erase_insert hW', h]
  rw [himg, card_image_of_injOn hinj, card_powerset,
    card_erase_of_mem (mem_erase.2 ⟨hab.symm, hb⟩), card_erase_of_mem ha]
  have : 2 ≤ A.card := by
    have : ({a, b} : Finset Γ) ⊆ A := by
      intro c hc
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl <;> assumption
    simpa [card_pair hab] using card_le_card this
  obtain ⟨n, hn⟩ : ∃ n, A.card = n + 2 := ⟨A.card - 2, by omega⟩
  rw [hn, show n + 2 - 1 - 1 = n by omega, pow_add]
  ring

open Finset in
lemma sum_countP_separating (A : Finset Γ) :
    ∀ P : List (Γ × Γ), (∀ p ∈ P, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2) →
      4 * ∑ T ∈ A.powerset, P.countP (fun p ↦ IsPair (fun c ↦ decide (c ∈ T)) p.1 p.2) =
        P.length * 2 ^ A.card
  | [], _ => by simp
  | p :: P, h => by
      have ih := sum_countP_separating A P fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
      obtain ⟨h1, h2, h3⟩ := h p (List.mem_cons_self ..)
      have hp : ∑ T ∈ A.powerset,
          (if decide (IsPair (fun c ↦ decide (c ∈ T)) p.1 p.2) = true then 1 else 0) =
          (A.powerset.filter fun T ↦ p.1 ∈ T ∧ p.2 ∉ T).card := by
        rw [card_eq_sum_ones, sum_filter]
        exact sum_congr rfl fun T _ ↦ by simp [IsPair]
      have := card_separating A h1 h2 h3
      simp only [List.countP_cons, sum_add_distrib, mul_add, ih, List.length_cons]
      rw [hp, this]
      ring

theorem Eqn.exists_partition {e : Eqn Γ V} (h : e.NoSquare) :
    ∃ S ∈ e.letters.dedup.sublists, e.adj.length ≤ 4 * e.pairs fun c ↦ decide (c ∈ S) := by
  set A := e.letters.toFinset
  have hP : ∀ p ∈ e.adj, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 := fun p hp ↦
    ⟨List.mem_toFinset.2 (e.mem_adj_letters hp).1, List.mem_toFinset.2 (e.mem_adj_letters hp).2,
      h p hp⟩
  have hsum := sum_countP_separating A e.adj hP
  obtain ⟨T, hT, hle⟩ : ∃ T ∈ A.powerset,
      e.adj.length ≤ 4 * e.adj.countP (fun p ↦ IsPair (fun c ↦ decide (c ∈ T)) p.1 p.2) := by
    by_contra hne
    simp only [not_exists, not_and, not_le] at hne
    have := Finset.sum_lt_sum_of_nonempty (Finset.powerset_nonempty A) hne
    rw [← Finset.mul_sum, hsum, Finset.sum_const_nat fun _ _ ↦ rfl, Finset.card_powerset,
      mul_comm] at this
    exact lt_irrefl _ this
  refine ⟨e.letters.dedup.filter (· ∈ T), List.mem_sublists.2 (List.filter_sublist), ?_⟩
  convert hle using 2
  refine List.countP_congr fun p hp ↦ ?_
  have h1 := (e.mem_adj_letters hp).1
  have h2 := (e.mem_adj_letters hp).2
  simp [IsPair, List.mem_dedup, h1, h2]

end

theorem exists_isChain_of_reachIn {α : Type} {next : α → Finset α} :
    ∀ {k : Nat} {a b : α}, ReachIn next k a b →
      ∃ es : List α, es.length ≤ k ∧ (a :: es).IsChain (fun x y ↦ y ∈ next x) ∧
        (a :: es).getLast (List.cons_ne_nil _ _) = b
  | 0, a, b, h => ⟨[], le_rfl, List.isChain_singleton _, h⟩
  | k + 1, a, b, h => by
    rcases h with rfl | ⟨c, hc, h⟩
    · exact ⟨[], Nat.zero_le _, List.isChain_singleton _, rfl⟩
    · obtain ⟨es, hlen, hchain, hlast⟩ := exists_isChain_of_reachIn h
      refine ⟨c :: es, by simp only [List.length_cons]; omega,
        List.isChain_cons_cons.2 ⟨hc, hchain⟩, ?_⟩
      rw [List.getLast_cons (List.cons_ne_nil _ _)]
      exact hlast

section

variable [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word]

omit [DecidableEq V.Word] in
lemma Eqn.letterCount_replacePairs {left : Γ → Bool} {g : V.Word → Side Γ V} {e : Eqn Γ V}
    (hg : ∀ x ∈ e.vars, PairPop left e.letters x (g x)) :
    (replacePairs left g e).letterCount + e.pairs left ≤ e.letterCount + 2 * e.varCount := by
  have side : ∀ u : Side Γ V, (∀ x ∈ sideVars u, x ∈ e.vars) →
      (sideLetters (mapRuns (compressPairs left (pairName e.letters)) (substSide g u))).length +
          (adjSide u).countP (fun p ↦ IsPair left p.1 p.2) ≤
        (sideLetters u).length + 2 * (sideVars u).length := by
    intro u hu
    have h1 := length_sideLetters_mapRuns (R := IsPair left)
      (length_compressPairs_add left (pairName e.letters)) (substSide g u)
    have h2 : (adjSide u).countP (fun p ↦ IsPair left p.1 p.2) ≤
        (adjSide (substSide g u)).countP (fun p ↦ IsPair left p.1 p.2) :=
      (adjSide_sublist_substSide g u).countP_le
    have h3 := length_sideLetters_substSide_le (k := 2) u
      fun x hx ↦ (hg x (hu x hx)).length_sideLetters_le
    omega
  have hl := side e.1 fun x hx ↦ by simp [Eqn.vars, hx]
  have hr := side e.2 fun x hx ↦ by simp [Eqn.vars, hx]
  simp only [Eqn.letterCount, Eqn.letters, Eqn.pairs, Eqn.adj, Eqn.varCount, Eqn.vars,
    List.length_append, List.countP_append, replacePairs, Eqn.map] at hl hr ⊢
  omega

omit [DecidableEq V.Word] in
lemma Eqn.vars_replacePairs {left : Γ → Bool} {g : V.Word → Side Γ V} {e : Eqn Γ V}
    (hg : ∀ x ∈ e.vars, PairPop left e.letters x (g x)) :
    (replacePairs left g e).vars <+ e.vars := by
  have side : ∀ u : Side Γ V, (∀ x ∈ sideVars u, x ∈ e.vars) →
      sideVars (mapRuns (compressPairs left (pairName e.letters)) (substSide g u)) <+
        sideVars u :=
    fun u hu ↦ by
      rw [sideVars_mapRuns]
      exact sideVars_substSide_sublist u fun x hx ↦ (hg x (hu x hx)).sideVars_sublist
  exact (side e.1 fun x hx ↦ by simp [Eqn.vars, hx]).append
    (side e.2 fun x hx ↦ by simp [Eqn.vars, hx])

omit [DecidableEq Γ] [Fresh Γ] in
lemma SolvedNaively.solvable {e : Eqn Γ V} (h : SolvedNaively e) : e.Solvable := by
  obtain ⟨g, -, hg⟩ := h
  exact ⟨g, hg⟩

lemma mem_pairComp {L₀ S : List Γ} {e f : Eqn Γ V} :
    f ∈ pairComp L₀ S e ↔
      ∃ g ∈ assignments (pops (fun c ↦ decide (c ∈ S)) e.letters) (fun x ↦ [.inr x]) e.vars,
        f = (replacePairs (fun c ↦ decide (c ∈ S)) g e).renumber L₀ := by
  simp [pairComp, eq_comm]

lemma solvable_of_mem_pairComp {L₀ S : List Γ} (hL : L₀.Nodup) {e f : Eqn Γ V}
    (hf : f ∈ pairComp L₀ S e) (he : f.letterCount ≤ L₀.length) (h : f.Solvable) :
    e.Solvable := by
  obtain ⟨g, hg, rfl⟩ := mem_pairComp.1 hf
  rw [Eqn.letterCount_renumber] at he
  exact solvable_of_replacePairs (fun x hx ↦ pairPop_of_mem_pops (mem_assignments hg x hx))
    ((Eqn.renumber_solvable_iff hL he).1 h)

omit [DecidableEq Γ] [Fresh Γ] in
lemma solvedNaively_of_solves {e : Eqn Γ V} {σ : Subst Γ V} (hσ : e.Solves σ)
    (hA : ∀ x, ∀ a ∈ σ x, a ∈ e.letters) (h : List.length (eval σ e.1) ≤ 1) :
    SolvedNaively e := by
  have hx : ∀ x ∈ e.vars, σ x ∈ naiveValues e.letters := by
    intro x hx
    have hlen : List.length (σ x) ≤ 1 := by
      simp only [Eqn.vars, List.mem_append] at hx
      rcases hx with hx | hx
      · have := length_le_eval (σ := σ) hx
        omega
      · have := length_le_eval (σ := σ) hx
        rw [← hσ] at this
        omega
    rcases hσx : σ x with _ | ⟨a, _ | ⟨b, w⟩⟩
    · simp [naiveValues]
    · simp [naiveValues, hA x a (by simp [hσx])]
    · simp [hσx] at hlen
  obtain ⟨g, hg, hgσ⟩ := exists_mem_assignments (d := fun _ ↦ []) σ e.vars hx
  refine ⟨g, hg, ?_⟩
  simp only [Eqn.Solves]
  rw [eval_congr fun x hx' ↦ hgσ x (by simp [Eqn.vars, hx']),
    eval_congr (u := e.2) fun x hx' ↦ hgσ x (by simp [Eqn.vars, hx'])]
  exact hσ

omit [Fresh Γ] in
lemma solvedNaively_of_short {e : Eqn Γ V} (hs : e.Short) (h : e.Solvable) :
    SolvedNaively e := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨σ₀, hσ₀, hA₀, -, -⟩ := e.exists_solves_letters hσ
  have htake : ∀ u : Side Γ V, u.length ≤ 1 →
      eval (fun x ↦ (σ₀ x).take 1) u = (eval σ₀ u).take 1 := by
    intro u hu
    rcases u with _ | ⟨s, _ | ⟨t, u⟩⟩
    · rfl
    · cases s <;> simp
    · simp at hu
  refine solvedNaively_of_solves (σ := fun x ↦ (σ₀ x).take 1) ?_
    (fun x a ha ↦ hA₀ x a (List.mem_of_mem_take ha)) (by rw [htake _ hs.1]; simp)
  simp only [Eqn.Solves, htake _ hs.1, htake _ hs.2]
  rw [hσ₀]

lemma exists_pair_succ (L₀ : List Γ) {e : Eqn Γ V} {σ : Subst Γ V} (hσ : e.Solves σ)
    (hA : ∀ x, ∀ a ∈ σ x, a ∈ e.letters) (S : List Γ) :
    ∃ e' ∈ pairComp L₀ S e, ∃ σ', e'.Solves σ' ∧
      (∃ ρ : Γ → Γ, eval σ' e'.1 =
        (compressPairs (fun c ↦ decide (c ∈ S)) (pairName e.letters) (eval σ e.1)).map ρ) ∧
      e'.letterCount + e.pairs (fun c ↦ decide (c ∈ S)) ≤ e.letterCount + 2 * e.varCount ∧
      e'.vars <+ e.vars ∧ ∀ x ∈ e'.vars, 2 ≤ List.length (σ x) := by
  set left := fun c ↦ decide (c ∈ S)
  have hpop : ∀ x ∈ e.vars, PairPop left e.letters x (pairPopOf left σ x) :=
    fun x _ ↦ pairPop_pairPopOf left σ x (hA x)
  obtain ⟨g, hg, hgσ⟩ := exists_mem_assignments (opts := pops left e.letters)
    (d := fun x ↦ [.inr x]) (pairPopOf left σ) e.vars
    fun x hx ↦ mem_pops_of_pairPop (hpop x hx)
  obtain ⟨hsol, hval⟩ := replacePairs_complete left hσ
  set f := replacePairs left (pairPopOf left σ) e
  refine ⟨f.renumber L₀, ?_, _, Eqn.solves_rename _ f hsol,
    ⟨fun a ↦ (L₀[f.letterIndex a]?).getD a, ?_⟩, ?_, ?_, ?_⟩
  · refine mem_pairComp.2 ⟨g, hg, ?_⟩
    rw [replacePairs_congr hgσ]
  · simp only [Eqn.renumber, Eqn.rename, Eqn.map, eval_renameSide]
    rw [hval]
  · rw [Eqn.letterCount_renumber]
    exact Eqn.letterCount_replacePairs hpop
  · rw [Eqn.vars_renumber]
    exact Eqn.vars_replacePairs hpop
  · intro x hx
    rw [Eqn.vars_renumber] at hx
    simp only [f, replacePairs, Eqn.map, Eqn.vars, List.mem_append] at hx
    rcases hx with hx | hx <;> exact two_le_of_mem_vars_replacePairs left _ σ hx

lemma mem_boundedEqns {L₀ : List Γ} {M nv : Nat} {X : List V.Word} {e : Eqn Γ V}
    (hL : e.letterCount ≤ M) (hlt : ∀ c ∈ e.letters, c ∈ L₀) (hnv : e.varCount ≤ nv)
    (hV : ∀ x ∈ e.vars, x ∈ X) : e ∈ boundedEqns L₀ (M + nv) X := by
  have side : ∀ u : Side Γ V, (sideLetters u).length ≤ M → (sideVars u).length ≤ nv →
      (∀ c ∈ sideLetters u, c ∈ L₀) → (∀ x ∈ sideVars u, x ∈ X) →
      u ∈ listsUpTo (L₀.map .inl ++ X.map .inr : Side Γ V) (M + nv) := by
    intro u h1 h2 h3 h4
    refine mem_listsUpTo (by rw [length_side]; omega) fun s hs ↦ ?_
    rcases s with c | x
    · simp [h3 c (mem_sideLetters_of_mem hs)]
    · simp [h4 x (mem_sideVars_of_mem hs)]
  simp only [Eqn.letterCount, Eqn.letters, Eqn.varCount, Eqn.vars, List.length_append,
    List.mem_append] at hL hlt hnv hV
  simp only [boundedEqns, Finset.mem_product, List.mem_toFinset]
  exact ⟨side e.1 (by omega) (by omega) (fun c hc ↦ hlt c (.inl hc)) fun x hx ↦ hV x (.inl hx),
    side e.2 (by omega) (by omega) (fun c hc ↦ hlt c (.inr hc)) fun x hx ↦ hV x (.inr hx)⟩

lemma vars_of_mem_boundedEqns {L₀ : List Γ} {K : Nat} {X : List V.Word} {e : Eqn Γ V}
    (h : e ∈ boundedEqns L₀ K X) : ∀ x ∈ e.vars, x ∈ X := by
  simp only [boundedEqns, Finset.mem_product, List.mem_toFinset] at h
  have side : ∀ u ∈ listsUpTo (L₀.map .inl ++ X.map .inr : Side Γ V) K,
      ∀ x ∈ sideVars u, x ∈ X := by
    intro u hu x hx
    obtain ⟨s, hs, hs'⟩ := List.mem_filterMap.1 hx
    rcases s with c | y
    · simp at hs'
    · simp only [Sum.getRight?_inr, Option.some.injEq] at hs'
      subst hs'
      simpa using mem_of_mem_listsUpTo hu _ hs
  intro x hx
  simp only [Eqn.vars, List.mem_append] at hx
  rcases hx with hx | hx
  · exact side _ h.1 x hx
  · exact side _ h.2 x hx

omit [Fresh Γ] in
lemma card_boundedEqns_le (L₀ : List Γ) (K : Nat) (X : List V.Word) :
    (boundedEqns L₀ K X).card ≤ countUpTo (L₀.length + X.length) K ^ 2 := by
  unfold boundedEqns
  rw [Finset.card_product, sq]
  have h := List.toFinset_card_le (listsUpTo (L₀.map .inl ++ X.map .inr : Side Γ V) K)
  rw [length_listsUpTo] at h
  simp only [List.length_append, List.length_map] at h
  exact Nat.mul_le_mul h h

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma length_blocks_symSide_le (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (u : Side Γ V) :
    (blocks (symbolicSide sh idx u)).length ≤
      (sideLetters u).length + 2 * (sideVars u).length := by
  induction u with
  | nil => simp
  | cons s u ih =>
      rcases s with a | x
      · simp only [symbolicSide_cons_letter, blocks_cons_block, sideLetters_cons_letter,
          List.length_cons, sideVars_cons_letter]
        omega
      · have : (blocks (prefSuffSyms (idx x) x (sh x))).length ≤ 2 := by
          rcases sh x <;> simp [prefSuffSyms]
        simp only [symbolicSide_cons_var, blocks_append, List.length_append, sideLetters_cons_var,
          sideVars_cons_var, List.length_cons]
        omega

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma itemVars_symSide_sublist (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (u : Side Γ V) :
    itemVars (symbolicSide sh idx u) <+ sideVars u := by
  induction u with
  | nil => simp [itemVars]
  | cons s u ih =>
      rcases s with a | x
      · simpa [itemVars] using ih
      · have : itemVars (prefSuffSyms (idx x) x (sh x)) <+ [x] := by
          rcases sh x <;> simp [prefSuffSyms, itemVars]
        have e1 : itemVars (prefSuffSyms (idx x) x (sh x) ++ symbolicSide sh idx u) =
            itemVars (prefSuffSyms (idx x) x (sh x)) ++ itemVars (symbolicSide sh idx u) := by
          simp [itemVars]
        simpa [e1] using this.append ih

lemma Eqn.letterCount_replaceBlocks (sh : V.Word → PrefSuff Γ) (cls : List Nat) (e : Eqn Γ V) :
    (replaceBlocks sh cls e).letterCount ≤ e.letterCount + 2 * e.varCount := by
  have h1 := length_blocks_symSide_le sh e.vars.idxOf e.1
  have h2 := length_blocks_symSide_le sh e.vars.idxOf e.2
  have h3 := length_blocks_merge_le (symbolicSide sh e.vars.idxOf e.1)
  have h4 := length_blocks_merge_le (symbolicSide sh e.vars.idxOf e.2)
  rw [replaceBlocks_eq]
  simp only [Eqn.letterCount, Eqn.letters, Eqn.varCount, Eqn.vars, List.length_append,
    length_sideLetters_label, symbolicSides] at h1 h2 h3 h4 ⊢
  omega

lemma Eqn.vars_replaceBlocks (sh : V.Word → PrefSuff Γ) (cls : List Nat) (e : Eqn Γ V) :
    (replaceBlocks sh cls e).vars <+ e.vars := by
  rw [replaceBlocks_eq]
  simp only [Eqn.vars, sideVars_label, symbolicSides, itemVars_merge]
  exact (itemVars_symSide_sublist sh _ e.1).append (itemVars_symSide_sublist sh _ e.2)

lemma Eqn.noSquare_replaceBlocks {sh : V.Word → PrefSuff Γ} {cls : List Nat} {e : Eqn Γ V}
    (hlen : cls.length = (allBlocks sh e.vars.idxOf e).length)
    (hlt : ∀ c ∈ cls, c < (allBlocks sh e.vars.idxOf e).length)
    (hl : SameLetters cls (allBlocks sh e.vars.idxOf e)) : (replaceBlocks sh cls e).NoSquare := by
  have hk : (blocks (symbolicSides sh e.vars.idxOf e).1).length ≤ cls.length := by
    simp [hlen, allBlocks]
  have hzip : cls.zip (allBlocks sh e.vars.idxOf e) =
      (cls.take (blocks (symbolicSides sh e.vars.idxOf e).1).length).zip
          (blocks (symbolicSides sh e.vars.idxOf e).1) ++
        (cls.drop (blocks (symbolicSides sh e.vars.idxOf e).1).length).zip
          (blocks (symbolicSides sh e.vars.idxOf e).2) := by
    conv_lhs => rw [← List.take_append_drop (blocks (symbolicSides sh e.vars.idxOf e).1).length cls]
    rw [allBlocks, List.zip_append (by simp [hk])]
  have key : ∀ (cs : List Nat) (Bs : List (Γ × Length)),
      (∀ p ∈ cs.zip Bs, p ∈ cls.zip (allBlocks sh e.vars.idxOf e)) →
      ∀ p ∈ (cs.map (blockLetter e (allBlocks sh e.vars.idxOf e).length)).zip Bs,
      ∀ q ∈ (cs.map (blockLetter e (allBlocks sh e.vars.idxOf e).length)).zip Bs,
        p.1 = q.1 → p.2.1 = q.2.1 := by
    intro cs Bs hsub p hp q hq hpq
    rw [List.zip_map_left, List.mem_map] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    have hp'' := hsub p' hp'
    have hq'' := hsub q' hq'
    exact hl p' hp'' q' hq''
      (blockLetter_inj (hlt _ (List.of_mem_zip hp'').1) (hlt _ (List.of_mem_zip hq'').1) hpq)
  have h1 : label (cls.map (blockLetter e (allBlocks sh e.vars.idxOf e).length))
        (symbolicSides sh e.vars.idxOf e).1 =
      label ((cls.take (blocks (symbolicSides sh e.vars.idxOf e).1).length).map
        (blockLetter e (allBlocks sh e.vars.idxOf e).length))
        (symbolicSides sh e.vars.idxOf e).1 := by
    conv_lhs =>
      rw [← List.take_append_drop (blocks (symbolicSides sh e.vars.idxOf e).1).length cls,
        List.map_append]
    exact label_append _ _ _ (by simp [hk])
  intro p hp
  rw [replaceBlocks_eq] at hp
  simp only [Eqn.adj, List.mem_append] at hp
  rw [h1] at hp
  rcases hp with hp | hp
  · exact adjSide_label_ne _ _ (merged_merge _)
      (by rw [List.length_map, List.length_take, Nat.min_eq_left hk]; rfl)
      (key _ _ fun q hq ↦ by rw [hzip]; exact List.mem_append_left _ hq) p hp
  · exact adjSide_label_ne _ _ (merged_merge _)
      (by rw [List.length_map, List.length_drop, hlen, allBlocks, List.length_append,
        Nat.add_sub_cancel_left]; rfl)
      (key _ _ fun q hq ↦ by rw [hzip]; exact List.mem_append_right _ hq) p hp

lemma mem_blockComp {L₀ : List Γ} {e f : Eqn Γ V} :
    f ∈ blockComp L₀ e ↔
      ∃ sh ∈ assignments (fun _ ↦ prefSuffs e.letters) (fun _ ↦ .empty) e.vars,
        ∃ cls ∈ vectors (allBlocks sh e.vars.idxOf e).length (allBlocks sh e.vars.idxOf e).length,
          (∃ ℓ, Consistent cls (allBlocks sh e.vars.idxOf e) ℓ) ∧
            f = (replaceBlocks sh cls e).renumber L₀ := by
  simp only [blockComp, Guess.mem_bind, Guess.mem_guard, Guess.mem_pure, exists_const,
    ← blockComp_check_iff, and_assoc]
  refine exists_congr fun sh ↦ and_congr_right fun _ ↦ exists_congr fun cls ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun ⟨_, h, rfl, hf⟩ ↦ ⟨h, hf⟩, fun ⟨h, hf⟩ ↦ ⟨_, h, rfl, hf⟩⟩

lemma mem_phase {L₀ : List Γ} {e f : Eqn Γ V} :
    f ∈ phase L₀ e ↔ ∃ e₁ ∈ blockComp L₀ e, ∃ S₁ ∈ e₁.letters.dedup.sublists,
      ∃ e₂ ∈ pairComp L₀ S₁ e₁, ∃ S₂ ∈ e₂.letters.dedup.sublists, f ∈ pairComp L₀ S₂ e₂ := by
  simp only [phase, Guess.mem_bind, Guess.mem_sublist]

lemma solvable_of_mem_blockComp {L₀ : List Γ} (hL : L₀.Nodup) {e f : Eqn Γ V}
    (hf : f ∈ blockComp L₀ e) (he : f.letterCount ≤ L₀.length) (h : f.Solvable) :
    e.Solvable := by
  obtain ⟨sh, -, cls, hcls, ⟨ℓ, hℓ⟩, rfl⟩ := mem_blockComp.1 hf
  rw [Eqn.letterCount_renumber] at he
  exact solvable_of_replaceBlocks (mem_vectors.1 hcls).1 (mem_vectors.1 hcls).2 hℓ
    ((Eqn.renumber_solvable_iff hL he).1 h)

lemma exists_block_succ {L₀ : List Γ} (hL : L₀.Nodup) {e : Eqn Γ V} {σ : Subst Γ V}
    (hσ : e.Solves σ) (hA : ∀ x, ∀ a ∈ σ x, a ∈ e.letters)
    (he : e.letterCount + 2 * e.varCount ≤ L₀.length) :
    ∃ e' ∈ blockComp L₀ e, ∃ σ', e'.Solves σ' ∧
      List.length (eval σ' e'.1) = (runs (eval σ e.1)).length ∧
      e'.letterCount ≤ e.letterCount + 2 * e.varCount ∧ e'.vars <+ e.vars ∧ e'.NoSquare := by
  obtain ⟨hlen, hlt, hcons, hsol, hval⟩ := replaceBlocks_complete hσ
  obtain ⟨sh, hsh, hshσ⟩ := exists_mem_assignments (opts := fun _ ↦ prefSuffs e.letters)
    (d := fun _ ↦ .empty) (prefSuffsOf σ) e.vars fun x _ ↦ prefSuffOf_mem_prefSuffs (hA x)
  have hsides := symbolicSides_congr (idx := e.vars.idxOf) hshσ
  have hB : allBlocks sh e.vars.idxOf e = allBlocks (prefSuffsOf σ) e.vars.idxOf e := by
    simp [allBlocks, hsides]
  have hstep : replaceBlocks sh (classesOf σ e) e =
      replaceBlocks (prefSuffsOf σ) (classesOf σ e) e := by
    simp only [replaceBlocks_eq, hsides, hB]
  have hf : (replaceBlocks (prefSuffsOf σ) (classesOf σ e) e).letterCount ≤ L₀.length :=
    (Eqn.letterCount_replaceBlocks _ _ _).trans he
  refine ⟨(replaceBlocks (prefSuffsOf σ) (classesOf σ e) e).renumber L₀, ?_, _,
    Eqn.solves_rename _ _ hsol, ?_, ?_, ?_, ?_⟩
  · refine mem_blockComp.2 ⟨sh, hsh, classesOf σ e,
      mem_vectors.2 ⟨by rw [hB, hlen], fun c hc ↦ hB ▸ hlt c hc⟩, ⟨lengthsOf σ e, hB ▸ hcons⟩, ?_⟩
    rw [hstep]
  · simp only [Eqn.renumber, Eqn.rename, Eqn.map, eval_renameSide, List.length_map]
    rw [hval, length_compressBlocks]
  · rw [Eqn.letterCount_renumber]
    exact Eqn.letterCount_replaceBlocks _ _ _
  · rw [Eqn.vars_renumber]
    exact Eqn.vars_replaceBlocks _ _ _
  · exact Eqn.noSquare_renumber hL hf (Eqn.noSquare_replaceBlocks hlen hlt
      fun p hp q hq hpq ↦ (hcons p hp q hq hpq).1)

theorem exists_phase {L₀ : List Γ} (hL : L₀.Nodup) {B : Nat} {e : Eqn Γ V} {σ : Subst Γ V}
    (hσ : e.Solves σ) (hB : e.size ≤ B) (hv : 24 * e.varCount + 2 ≤ B)
    (hL₀ : B + e.varCount ≤ L₀.length) :
    ∃ e' ∈ phase L₀ e, ∃ σ', e'.Solves σ' ∧ e'.size ≤ B ∧ e'.vars <+ e.vars ∧
      List.length (eval σ' e'.1) ≤ List.length (eval σ e.1) ∧
      ((∃ p ∈ adj (eval σ e.1), p.1 = p.2) →
        List.length (eval σ' e'.1) < List.length (eval σ e.1)) ∧
      (List.length (eval σ' e'.1) < List.length (eval σ e.1) ∨ e'.Short ∨
        ∃ p ∈ adj (eval σ' e'.1), p.1 = p.2) := by
  have hsize := e.size_eq
  obtain ⟨σ₀, hσ₀, hA₀, hm₀, hsq₀⟩ := e.exists_solves_letters hσ
  obtain ⟨e₁, he₁, σ₁, hσ₁, hv₁, hL₁, hV₁, hsq₁⟩ := exists_block_succ hL hσ₀ hA₀ (by omega)
  obtain ⟨σ₁', hσ₁', hA₁, hm₁', -⟩ := e₁.exists_solves_letters hσ₁
  obtain ⟨S, hS, hpairs⟩ := e₁.exists_partition hsq₁
  obtain ⟨e₂, he₂, σ₂, hσ₂, ⟨ρ₂, hv₂⟩, hL₂, hV₂, -⟩ := exists_pair_succ L₀ hσ₁' hA₁ S
  obtain ⟨σ₂', hσ₂', hA₂, hm₂', hsq₂'⟩ := e₂.exists_solves_letters hσ₂
  have hadj := e₁.letterCount_le_adj
  have n₁ := hV₁.length_le
  have n₂ := hV₂.length_le
  have hw₁ := length_runs_le (eval σ₀ e.1)
  have hw₂ := length_compressPairs_le' (fun c ↦ decide (c ∈ S)) (pairName e₁.letters)
    (eval σ₁' e₁.1)
  rw [hv₂, List.length_map] at hm₂'
  have hle : List.length (eval σ₂' e₂.1) ≤ List.length (eval σ e.1) := by
    omega
  have hsq : (∃ p ∈ adj (eval σ e.1), p.1 = p.2) →
      List.length (eval σ₂' e₂.1) < List.length (eval σ e.1) := by
    intro h
    rcases hsq₀ h with h | h
    · have := length_runs_lt h
      omega
    · omega
  have pair₂ : ∀ S' ∈ e₂.letters.dedup.sublists, ∃ e' ∈ phase L₀ e, ∃ σ', e'.Solves σ' ∧
      (∃ ρ : Γ → Γ, eval σ' e'.1 =
        (compressPairs (fun c ↦ decide (c ∈ S')) (pairName e₂.letters) (eval σ₂' e₂.1)).map ρ) ∧
      e'.size ≤ B ∧ e'.vars <+ e₂.vars ∧ e'.vars <+ e.vars ∧
      ∀ x ∈ e'.vars, 2 ≤ List.length (σ₂' x) := by
    intro S' hS'
    obtain ⟨e₃, he₃, σ₃, hσ₃, hv₃, hL₃, hV₃, h2⟩ := exists_pair_succ L₀ hσ₂' hA₂ S'
    refine ⟨e₃, mem_phase.2 ⟨e₁, he₁, S, hS, e₂, he₂, S', hS', he₃⟩, σ₃, hσ₃, hv₃, ?_, hV₃,
      hV₃.trans (hV₂.trans hV₁), h2⟩
    have n₃ := hV₃.length_le
    have := e₃.size_eq
    simp only [Eqn.varCount] at *
    omega
  by_cases hshort : List.length (eval σ₂' e₂.1) ≤ 1
  · obtain ⟨e₃, he₃, σ₃, hσ₃, ⟨ρ, hv₃⟩, hB₃, hV₃₂, hV₃, h2⟩ := pair₂ [] (by simp)
    have hlen : List.length (eval σ₃ e₃.1) ≤ List.length (eval σ₂' e₂.1) := by
      rw [hv₃, List.length_map]
      exact length_compressPairs_le' _ _ _
    have hnil : e₃.vars = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun x hx ↦ ?_
      have h2 := h2 x hx
      have hx₂ := hV₃₂.subset hx
      simp only [Eqn.vars, List.mem_append] at hx₂
      rcases hx₂ with hx₂ | hx₂
      · have := length_le_eval (σ := σ₂') hx₂
        omega
      · have := length_le_eval (σ := σ₂') hx₂
        rw [← hσ₂'] at this
        omega
    simp only [Eqn.vars, List.append_eq_nil_iff] at hnil
    have hl₃ := length_eq_of_sideVars_eq_nil (σ := σ₃) hnil.1
    have hr₃ := length_eq_of_sideVars_eq_nil (σ := σ₃) hnil.2
    rw [← hσ₃] at hr₃
    refine ⟨e₃, he₃, σ₃, hσ₃, hB₃, hV₃, by omega, fun h ↦ ?_, .inr (.inl ⟨?_, ?_⟩)⟩
    · have := hsq h
      omega
    · omega
    · omega
  by_cases hd : ∃ p ∈ adj (eval σ₂' e₂.1), p.1 ≠ p.2
  · obtain ⟨p, hp, hne⟩ := hd
    have ha : p.1 ∈ e₂.letters := by
      rcases mem_eval (mem_adj_letters hp).1 with h | ⟨x, -, h⟩
      · simp [Eqn.letters, h]
      · exact hA₂ x _ h
    obtain ⟨e₃, he₃, σ₃, hσ₃, ⟨ρ, hv₃⟩, hB₃, -, hV₃, -⟩ := pair₂ [p.1]
      (List.mem_sublists.2 (List.singleton_sublist.2 (List.mem_dedup.2 ha)))
    have hlt : List.length (eval σ₃ e₃.1) < List.length (eval σ₂' e₂.1) := by
      rw [hv₃, List.length_map]
      exact length_compressPairs_lt _ _ ⟨p, hp, by simp [IsPair, Ne.symm hne]⟩
    exact ⟨e₃, he₃, σ₃, hσ₃, hB₃, hV₃, by omega, fun h ↦ by have := hsq h; omega,
      .inl (by omega)⟩
  · obtain ⟨p, hp⟩ := exists_mem_adj (by omega : 2 ≤ List.length (eval σ₂' e₂.1))
    have heq : p.1 = p.2 := by
      by_contra h
      exact hd ⟨p, hp, h⟩
    obtain ⟨e₃, he₃, σ₃, hσ₃, ⟨ρ, hv₃⟩, hB₃, -, hV₃, -⟩ := pair₂ [] (by simp)
    rw [compressPairs_of_right (by simp)] at hv₃
    have hlen : List.length (eval σ₃ e₃.1) = List.length (eval σ₂' e₂.1) := by
      rw [hv₃, List.length_map]
    refine ⟨e₃, he₃, σ₃, hσ₃, hB₃, hV₃, by omega, fun h ↦ by have := hsq h; omega,
      .inr (.inr ?_)⟩
    rw [hv₃]
    exact exists_adj_eq_map ρ ⟨p, hp, heq⟩

theorem reach_short {L₀ : List Γ} (hL : L₀.Nodup) {B : Nat} :
    ∀ (m : Nat) (e : Eqn Γ V) (σ : Subst Γ V), e.Solves σ → List.length (eval σ e.1) ≤ m →
      e.size ≤ B → 24 * e.varCount + 2 ≤ B → B + e.varCount ≤ L₀.length →
      ∃ f, Relation.ReflTransGen (PhaseStep L₀ B) e f ∧ f.Short ∧
        SolvedNaively f := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro e σ hσ hm hB hv hL₀
  by_cases hs : e.Short
  · exact ⟨e, .refl, hs, solvedNaively_of_short hs ⟨σ, hσ⟩⟩
  obtain ⟨e₁, he₁, σ₁, hσ₁, hB₁, hV₁, hle₁, -, hcases⟩ := exists_phase hL hσ hB hv hL₀
  have hv₁ : 24 * e₁.varCount + 2 ≤ B ∧ B + e₁.varCount ≤ L₀.length := by
    have := hV₁.length_le
    simp only [Eqn.varCount] at *
    omega
  have step₁ : PhaseStep L₀ B e e₁ := ⟨he₁, hs, hB₁⟩
  by_cases hs₁ : e₁.Short
  · exact ⟨e₁, .single step₁, hs₁, solvedNaively_of_short hs₁ ⟨σ₁, hσ₁⟩⟩
  rcases hcases with hlt | hs₁' | hsq
  · obtain ⟨f, hf, hfs, hfm⟩ := ih _ (by omega) e₁ σ₁ hσ₁ le_rfl hB₁ hv₁.1 hv₁.2
    exact ⟨f, .head step₁ hf, hfs, hfm⟩
  · exact absurd hs₁' hs₁
  · obtain ⟨e₂, he₂, σ₂, hσ₂, hB₂, hV₂, -, hsq₂, -⟩ := exists_phase hL hσ₁ hB₁ hv₁.1 hv₁.2
    have hv₂ : 24 * e₂.varCount + 2 ≤ B ∧ B + e₂.varCount ≤ L₀.length := by
      have := hV₂.length_le
      have := hv₁
      simp only [Eqn.varCount] at *
      omega
    have step₂ : PhaseStep L₀ B e₁ e₂ := ⟨he₂, hs₁, hB₂⟩
    obtain ⟨f, hf, hfs, hfm⟩ :=
      ih _ (by have := hsq₂ hsq; omega) e₂ σ₂ hσ₂ le_rfl hB₂ hv₂.1 hv₂.2
    exact ⟨f, .head step₁ (.head step₂ hf), hfs, hfm⟩

lemma vars_of_mem_phase {L₀ : List Γ} {e f : Eqn Γ V} (hf : f ∈ phase L₀ e) :
    f.vars <+ e.vars := by
  have pair : ∀ {S : List Γ} {a b : Eqn Γ V}, b ∈ pairComp L₀ S a → b.vars <+ a.vars := by
    intro S a b hb
    obtain ⟨g, hg, rfl⟩ := mem_pairComp.1 hb
    rw [Eqn.vars_renumber]
    exact Eqn.vars_replacePairs fun x hx ↦ pairPop_of_mem_pops (mem_assignments hg x hx)
  obtain ⟨e₁, h₁, S₁, -, e₂, h₂, S₂, -, h₃⟩ := mem_phase.1 hf
  obtain ⟨sh, -, cls, -, -, rfl⟩ := mem_blockComp.1 h₁
  refine (pair h₃).trans ((pair h₂).trans ?_)
  rw [Eqn.vars_renumber]
  exact Eqn.vars_replaceBlocks _ _ _

lemma letters_of_mem_phase {L₀ : List Γ} {e f : Eqn Γ V} (hf : f ∈ phase L₀ e)
    (hle : f.letterCount ≤ L₀.length) : ∀ c ∈ f.letters, c ∈ L₀ := by
  obtain ⟨e₁, -, S₁, -, e₂, -, S₂, -, h₃⟩ := mem_phase.1 hf
  obtain ⟨g, -, rfl⟩ := mem_pairComp.1 h₃
  rw [Eqn.letterCount_renumber] at hle
  exact Eqn.letters_renumber_subset hle

theorem phases_reach_short_of_le {L₀ : List Γ} (hL : L₀.Nodup) {B : Nat} {e : Eqn Γ V}
    (h : e.Solvable) (hB : e.size ≤ B) (hv : 24 * e.varCount + 2 ≤ B)
    (hL₀ : B + e.varCount ≤ L₀.length) :
    ∃ es : List (Eqn Γ V),
      es.length ≤ countUpTo (L₀.length + e.vars.length) (2 * B) ^ 2 + 1 ∧
      (e :: es).IsChain (fun x y ↦ ¬x.Short ∧
        (∃ x₁ ∈ blockComp L₀ x, ∃ S₁ ∈ x₁.letters.dedup.sublists, ∃ x₂ ∈ pairComp L₀ S₁ x₁,
          ∃ S₂ ∈ x₂.letters.dedup.sublists, y ∈ pairComp L₀ S₂ x₂) ∧ y.size ≤ B) ∧
      ((e :: es).getLast (List.cons_ne_nil _ _)).Short ∧
        SolvedNaively ((e :: es).getLast (List.cons_ne_nil _ _)) := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨f, hpath, hfs, hfm⟩ := reach_short hL _ e σ hσ le_rfl hB hv hL₀
  classical
  have hU : ∀ a ∈ insert e (boundedEqns L₀ (B + B) e.vars), ∀ b, PhaseStep L₀ B a b →
      b ∈ insert e (boundedEqns L₀ (B + B) e.vars) := by
    rintro a ha b ⟨hb, -, hbB⟩
    have haV : ∀ x ∈ a.vars, x ∈ e.vars := by
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact fun x hx ↦ hx
      · exact vars_of_mem_boundedEqns ha
    have hb' := b.size_eq
    exact Finset.mem_insert_of_mem (mem_boundedEqns (by omega)
      (letters_of_mem_phase hb (by omega)) (by omega)
      fun x hx ↦ haV x ((vars_of_mem_phase hb).subset hx))
  have hreach := reachIn_card_of_reflTransGen (Finset.mem_insert_self e _)
    (fun _ _ ↦ Finset.filter_subset _ _) (reflTransGen_filter hU (Finset.mem_insert_self e _) hpath).1
  have h1 := Finset.card_insert_le e (boundedEqns L₀ (B + B) e.vars)
  have h2 := card_boundedEqns_le L₀ (B + B) e.vars
  obtain ⟨es, hlen, hchain, hlast⟩ := exists_isChain_of_reachIn hreach
  refine ⟨es, by rw [two_mul]; omega, hchain.imp fun x y hxy ↦ ?_, hlast ▸ hfs, hlast ▸ hfm⟩
  obtain ⟨hxy, hx, hy⟩ := (Finset.mem_filter.1 hxy).2
  exact ⟨hx, mem_phase.1 hxy, hy⟩

theorem phases_reach_short {e : Eqn Γ V} (h : e.Solvable) :
    ∃ es : List (Eqn Γ V),
      es.length ≤
        countUpTo (e.letterList.length + e.vars.length) (2 * e.lengthBound) ^ 2 + 1 ∧
      (e.renumber e.letterList :: es).IsChain (fun x y ↦ ¬x.Short ∧
        (∃ x₁ ∈ blockComp e.letterList x, ∃ S₁ ∈ x₁.letters.dedup.sublists,
          ∃ x₂ ∈ pairComp e.letterList S₁ x₁, ∃ S₂ ∈ x₂.letters.dedup.sublists,
            y ∈ pairComp e.letterList S₂ x₂) ∧ y.size ≤ e.lengthBound) ∧
      ((e.renumber e.letterList :: es).getLast (List.cons_ne_nil _ _)).Short ∧
        SolvedNaively ((e.renumber e.letterList :: es).getLast (List.cons_ne_nil _ _)) := by
  obtain ⟨σ, hσ⟩ := h
  have hsol : (e.renumber e.letterList).Solvable := ⟨_, Eqn.solves_rename _ e hσ⟩
  by_cases hs : (e.renumber e.letterList).Short
  · exact ⟨[], Nat.zero_le _, List.isChain_singleton _, hs, solvedNaively_of_short hs hsol⟩
  have hsize : 2 ≤ e.size := by
    have := Eqn.size_renumber e.letterList e
    simp only [Eqn.Short, Eqn.size, not_and_or, not_le] at hs this ⊢
    omega
  have hcount := e.size_eq
  have hlen : e.letterList.length = e.lengthBound + 6 * e.varCount := length_freshList _ _
  have hbound : e.lengthBound = 79 * e.size := rfl
  obtain ⟨es, h1, h2⟩ := phases_reach_short_of_le (L₀ := e.letterList) (nodup_freshList _ _)
    (B := e.lengthBound) hsol (by rw [Eqn.size_renumber]; omega)
    (by rw [Eqn.varCount_renumber]; omega) (by rw [Eqn.varCount_renumber]; omega)
  rw [Eqn.vars_renumber] at h1
  exact ⟨es, h1, h2⟩

omit [DecidableEq V.Word] in
lemma Eqn.size_phaseBound_le (e : Eqn Γ V) :
    Nat.size e.phaseBound ≤
      2 * (2 * e.lengthBound) * Nat.size (e.letterList.length + e.vars.length + 1) + 3 :=
  size_sq_countUpTo_add_two_le _ _

lemma le_of_mem_pairComp {L₀ S : List Γ} {e f : Eqn Γ V} (hf : f ∈ pairComp L₀ S e) :
    f.letterCount ≤ e.letterCount + 2 * e.varCount ∧ f.varCount ≤ e.varCount := by
  obtain ⟨g, hg, rfl⟩ := mem_pairComp.1 hf
  have hp := fun x hx ↦ pairPop_of_mem_pops (mem_assignments hg x hx)
  have h := Eqn.letterCount_replacePairs hp
  rw [Eqn.letterCount_renumber, Eqn.varCount_renumber]
  exact ⟨by omega, (Eqn.vars_replacePairs hp).length_le⟩

lemma le_of_mem_blockComp {L₀ : List Γ} {e f : Eqn Γ V} (hf : f ∈ blockComp L₀ e) :
    f.letterCount ≤ e.letterCount + 2 * e.varCount ∧ f.varCount ≤ e.varCount := by
  obtain ⟨sh, -, cls, -, -, rfl⟩ := mem_blockComp.1 hf
  rw [Eqn.letterCount_renumber, Eqn.varCount_renumber]
  exact ⟨Eqn.letterCount_replaceBlocks sh cls e, (Eqn.vars_replaceBlocks sh cls e).length_le⟩

end

end Accordion.WE.Decidability

end
