module

public import Accordion.WE.Decidability.Properties.Compression
public import Accordion.WE.Decidability.Properties.Diophantine
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

namespace Length

@[simp] lemma eval_add (ℓ : Nat → Nat) (E F : Length) : (E + F).eval ℓ = E.eval ℓ + F.eval ℓ := by
  change E.const + F.const + ((E.vars ++ F.vars).map ℓ).sum = _
  simp [eval]
  omega

lemma add_const (E F : Length) : (E + F).const = E.const + F.const := rfl

end Length

section

@[simp] lemma instantiate_nil (ℓ : Nat → Nat) : instantiate ℓ ([] : List (BlockSym Γ V)) = [] := rfl

@[simp] lemma instantiate_cons_block (ℓ : Nat → Nat) (a : Γ) (E : Length)
    (M : List (BlockSym Γ V)) :
    instantiate ℓ (.block a E :: M) = letters (List.replicate (E.eval ℓ) a) ++ instantiate ℓ M :=
  rfl

@[simp] lemma instantiate_cons_var (ℓ : Nat → Nat) (x : V.Word) (M : List (BlockSym Γ V)) :
    instantiate ℓ (.var x :: M) = .inr x :: instantiate ℓ M := rfl

@[simp] lemma instantiate_append (ℓ : Nat → Nat) (M N : List (BlockSym Γ V)) :
    instantiate ℓ (M ++ N) = instantiate ℓ M ++ instantiate ℓ N := by
  simp [instantiate]

@[simp] lemma blocks_nil : blocks ([] : List (BlockSym Γ V)) = [] := rfl

@[simp] lemma blocks_cons_block (a : Γ) (E : Length) (M : List (BlockSym Γ V)) :
    blocks (.block a E :: M) = (a, E) :: blocks M := rfl

@[simp] lemma blocks_cons_var (x : V.Word) (M : List (BlockSym Γ V)) :
    blocks (.var x :: M) = blocks M := rfl

@[simp] lemma blocks_append (M N : List (BlockSym Γ V)) :
    blocks (M ++ N) = blocks M ++ blocks N := by
  simp [blocks]

@[simp] lemma sideVars_instantiate (ℓ : Nat → Nat) (M : List (BlockSym Γ V)) :
    sideVars (instantiate ℓ M) = itemVars M := by
  induction M with
  | nil => rfl
  | cons i M ih => cases i <;> simp [ih, itemVars]

@[simp] lemma sideVars_label (ls : List Γ) (M : List (BlockSym Γ V)) :
    sideVars (label ls M) = itemVars M := by
  induction M generalizing ls with
  | nil => rfl
  | cons i M ih =>
      rcases i with ⟨a, E⟩ | x <;> rcases ls with _ | ⟨c, ls⟩ <;> simp [label, ih, itemVars]

@[simp] lemma length_sideLetters_label (ls : List Γ) (M : List (BlockSym Γ V)) :
    (sideLetters (label ls M)).length = (blocks M).length := by
  induction M generalizing ls with
  | nil => rfl
  | cons i M ih => rcases i with ⟨a, E⟩ | x <;> rcases ls with _ | ⟨c, ls⟩ <;> simp [label, ih]

lemma label_append (ls ls' : List Γ) (M : List (BlockSym Γ V))
    (h : (blocks M).length ≤ ls.length) : label (ls ++ ls') M = label ls M := by
  induction M generalizing ls with
  | nil => rfl
  | cons i M ih =>
      rcases i with ⟨a, E⟩ | x
      · rcases ls with _ | ⟨c, ls⟩
        · simp at h
        · simp only [List.cons_append, label]
          rw [ih ls (by simpa using h)]
      · simp only [label]
        rw [ih ls (by simpa using h)]

lemma expandSide_label (h : Γ → List Γ) (ℓ : Nat → Nat) :
    ∀ (M : List (BlockSym Γ V)) (ls : List Γ), ls.length = (blocks M).length →
      (∀ p ∈ ls.zip (blocks M), h p.1 = List.replicate (p.2.2.eval ℓ) p.2.1) →
      expandSide h (label ls M) = instantiate ℓ M
  | [], _, _, _ => rfl
  | .var x :: M, ls, hl, hh => by
      simp only [label, expandSide_cons_var, instantiate_cons_var]
      rw [expandSide_label h ℓ M ls (by simpa using hl) (by simpa using hh)]
  | .block a E :: M, [], hl, _ => by simp at hl
  | .block a E :: M, c :: ls, hl, hh => by
      simp only [label, expandSide_cons_letter, instantiate_cons_block]
      rw [hh (c, (a, E)) (by simp), expandSide_label h ℓ M ls (by simpa using hl)
        fun p hp ↦ hh p (by simp [hp])]

lemma adjSide_label_ne :
    ∀ (M : List (BlockSym Γ V)) (ls : List Γ), Merged M → ls.length = (blocks M).length →
      (∀ p ∈ ls.zip (blocks M), ∀ q ∈ ls.zip (blocks M), p.1 = q.1 → p.2.1 = q.2.1) →
      ∀ p ∈ adjSide (label ls M), p.1 ≠ p.2
  | [], _, _, _, _ => by simp [label, adjSide]
  | .var x :: M, ls, hM, hl, hc => by
      simp only [label, adjSide]
      exact adjSide_label_ne M ls (List.isChain_cons.1 hM).2 (by simpa using hl) (by simpa using hc)
  | .block a E :: M, [], _, hl, _ => by simp at hl
  | .block a E :: M, c :: ls, hM, hl, hc => by
      have ih := adjSide_label_ne M ls (List.isChain_cons.1 hM).2 (by simpa using hl)
        fun p hp q hq ↦ hc p (by simp [hp]) q (by simp [hq])
      rcases M with _ | ⟨⟨b, F⟩ | x, M⟩
      · simp [label, adjSide]
      · rcases ls with _ | ⟨d, ls⟩
        · simp at hl
        · simp only [label, adjSide, List.mem_cons, forall_eq_or_imp]
          refine ⟨fun hcd ↦ ?_, by simpa [label] using ih⟩
          have := hc (c, (a, E)) (by simp) (d, (b, F)) (by simp) hcd
          exact (List.isChain_cons.1 hM).1 _ rfl a E b F rfl rfl this
      · simpa [label, adjSide] using ih

variable [DecidableEq Γ]

@[simp] lemma merge_nil : merge ([] : List (BlockSym Γ V)) = [] := rfl

@[simp] lemma merge_cons (i : BlockSym Γ V) (M : List (BlockSym Γ V)) :
    merge (i :: M) = consBlockSym i (merge M) := rfl

lemma instantiate_consBlockSym (ℓ : Nat → Nat) (i : BlockSym Γ V) (M : List (BlockSym Γ V)) :
    instantiate ℓ (consBlockSym i M) = instantiate ℓ (i :: M) := by
  unfold consBlockSym
  split
  · split_ifs with h
    · subst h
      simp only [instantiate_cons_block, Length.eval_add, List.replicate_add, letters,
        List.map_append, List.append_assoc]
    · rfl
  · rfl

@[simp] lemma instantiate_merge (ℓ : Nat → Nat) (M : List (BlockSym Γ V)) :
    instantiate ℓ (merge M) = instantiate ℓ M := by
  induction M with
  | nil => rfl
  | cons i M ih =>
      rw [merge_cons, instantiate_consBlockSym]
      cases i <;> simp [ih]

lemma merged_consBlockSym (i : BlockSym Γ V) {M : List (BlockSym Γ V)} (hM : Merged M) :
    Merged (consBlockSym i M) := by
  unfold Merged at *
  rcases i with ⟨a, E⟩ | x
  · rcases M with _ | ⟨⟨b, F⟩ | y, M⟩
    · exact List.isChain_singleton _
    · simp only [consBlockSym]
      split_ifs with hab
      · subst hab
        refine List.isChain_cons.2 ⟨fun j hj c G d H h1 h2 ↦ ?_, (List.isChain_cons.1 hM).2⟩
        cases h1
        exact (List.isChain_cons.1 hM).1 j hj a F d H rfl h2
      · refine List.isChain_cons.2 ⟨fun j hj c G d H h1 h2 ↦ ?_, hM⟩
        cases h1
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hj
        subst hj
        cases h2
        exact hab
    · exact List.isChain_cons.2 ⟨by simp, hM⟩
  · exact List.isChain_cons.2 ⟨by simp, hM⟩

lemma merged_merge (M : List (BlockSym Γ V)) : Merged (merge M) := by
  induction M with
  | nil => exact List.isChain_nil
  | cons i M ih => exact merged_consBlockSym i ih

lemma positive_consBlockSym {i : BlockSym Γ V} {M : List (BlockSym Γ V)}
    (hi : ∀ a E, i = .block a E → 0 < E.const) (hM : Positive M) :
    Positive (consBlockSym i M) := by
  unfold consBlockSym
  split
  · split_ifs
    · intro c G h
      rcases List.mem_cons.1 h with h | h
      · cases h
        have := hi _ _ rfl
        rw [Length.add_const]
        omega
      · exact hM c G (List.mem_cons_of_mem _ h)
    · intro c G h
      rcases List.mem_cons.1 h with h | h
      · exact hi c G h.symm
      · exact hM c G h
  · intro c G h
    rcases List.mem_cons.1 h with h | h
    · exact hi c G h.symm
    · exact hM c G h

lemma positive_merge {M : List (BlockSym Γ V)} (hM : Positive M) : Positive (merge M) := by
  induction M with
  | nil => intro a E h; cases h
  | cons i M ih =>
      exact positive_consBlockSym (fun a E h ↦ hM a E (h ▸ List.mem_cons_self ..))
        (ih fun a E h ↦ hM a E (List.mem_cons_of_mem _ h))

lemma length_blocks_consBlockSym (i : BlockSym Γ V) (M : List (BlockSym Γ V)) :
    (blocks (consBlockSym i M)).length ≤ (blocks (i :: M)).length := by
  unfold consBlockSym
  split
  · split_ifs <;> simp
  · rfl

lemma length_blocks_merge_le (M : List (BlockSym Γ V)) :
    (blocks (merge M)).length ≤ (blocks M).length := by
  induction M with
  | nil => rfl
  | cons i M ih =>
      refine (length_blocks_consBlockSym i _).trans ?_
      have ih : (blocks (List.foldr consBlockSym [] M)).length ≤ (blocks M).length := ih
      cases i <;> simp only [blocks_cons_block, blocks_cons_var, List.length_cons] <;> omega

@[simp] lemma itemVars_merge (M : List (BlockSym Γ V)) : itemVars (merge M) = itemVars M := by
  rw [← sideVars_instantiate (fun _ ↦ 0), ← sideVars_instantiate (fun _ ↦ 0), instantiate_merge]

lemma mapRuns_compressBlocks_instantiate_aux (nm : Γ → Nat → Γ) (ℓ : Nat → Nat) :
    ∀ (M : List (BlockSym Γ V)) (R : List (Γ × Nat)), Merged M → Positive M →
      (∀ p ∈ R, 0 < p.2) → R.IsChain (fun p q ↦ p.1 ≠ q.1) →
      (∀ c k a E, R.getLast? = some (c, k) → M.head? = some (.block a E) → c ≠ a) →
      mapRuns (compressBlocks nm) (letters (R.flatMap fun p ↦ List.replicate p.2 p.1) ++
          instantiate ℓ M) =
        letters (R.map fun p ↦ nm p.1 p.2) ++
          label ((blocks M).map fun p ↦ nm p.1 (p.2.eval ℓ)) M
  | [], R, _, _, hpos, hR, _ => by
      simp [compressBlocks_flatMap_replicate nm R hpos hR, label]
  | .block a E :: M, R, hM, hMpos, hpos, hR, hlast => by
      have hE : 0 < E.eval ℓ := by
        have := hMpos a E (List.mem_cons_self ..)
        unfold Length.eval
        omega
      have ih := mapRuns_compressBlocks_instantiate_aux nm ℓ M (R ++ [(a, E.eval ℓ)])
        (List.isChain_cons.1 hM).2 (fun b F h ↦ hMpos b F (List.mem_cons_of_mem _ h))
        (fun p hp ↦ by
          rcases List.mem_append.1 hp with hp | hp
          · exact hpos p hp
          · simp only [List.mem_singleton] at hp
            subst hp
            exact hE)
        (hR.append (List.isChain_singleton _) fun x hx y hy ↦ by
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact hlast x.1 x.2 a E hx rfl)
        (fun c k b F h1 h2 ↦ by
          have hc : c = a := by
            simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
              Option.some.injEq, Prod.mk.injEq] at h1
            exact h1.1.symm
          rw [hc]
          exact (List.isChain_cons.1 hM).1 _ h2 a E b F rfl rfl)
      simp only [List.flatMap_append, List.flatMap_singleton, letters, List.map_append,
        List.append_assoc, List.map_cons, List.map_nil] at ih
      simp only [instantiate_cons_block, blocks_cons_block, List.map_cons, label, letters]
      simpa using ih
  | .var x :: M, R, hM, hMpos, hpos, hR, _ => by
      have ih := mapRuns_compressBlocks_instantiate_aux nm ℓ M [] (List.isChain_cons.1 hM).2
        (fun b F h ↦ hMpos b F (List.mem_cons_of_mem _ h)) (by simp) List.isChain_nil (by simp)
      simp only [List.flatMap_nil, letters, List.map_nil, List.nil_append] at ih
      simp only [instantiate_cons_var, blocks_cons_var, label]
      rw [mapRuns_letters_var, compressBlocks_flatMap_replicate nm R hpos hR, ih]

lemma mapRuns_compressBlocks_instantiate (nm : Γ → Nat → Γ) (ℓ : Nat → Nat)
    (M : List (BlockSym Γ V)) (hM : Merged M) (hpos : Positive M) :
    mapRuns (compressBlocks nm) (instantiate ℓ M) =
      label ((blocks M).map fun p ↦ nm p.1 (p.2.eval ℓ)) M := by
  simpa [letters] using
    mapRuns_compressBlocks_instantiate_aux nm ℓ M [] hM hpos (by simp) List.isChain_nil (by simp)

end

section

open scoped List

variable [DecidableEq Γ]

lemma classExpand_of_mem {name : Nat → Γ} {cls : List Nat} {B : List (Γ × Length)}
    {ℓ : Nat → Nat} (hc : Consistent cls B ℓ)
    (hinj : ∀ p ∈ cls.zip B, ∀ q ∈ cls.zip B, name p.1 = name q.1 → p.1 = q.1)
    {p : Nat × (Γ × Length)} (hp : p ∈ cls.zip B) :
    classExpand name cls B ℓ (name p.1) = List.replicate (p.2.2.eval ℓ) p.2.1 := by
  unfold classExpand
  split
  · rename_i q hq
    have h1 := List.mem_of_find?_eq_some hq
    have h2 : name q.1 = name p.1 := by simpa using List.find?_some hq
    obtain ⟨e1, e2⟩ := hc q h1 p hp (hinj q h1 p hp h2)
    rw [e1, e2]
  · rename_i hq
    exact absurd hp (by simpa using List.find?_eq_none.1 hq p)

lemma splitBlock_spec (a : Γ) (w : GroundWord Γ) :
    List.replicate (splitBlock a w).1 a ++ (splitBlock a w).2 = w ∧
      (splitBlock a w).2.head? ≠ some a := by
  induction w with
  | nil => simp [splitBlock]
  | cons b w ih =>
      by_cases h : b = a
      · subst h
        simpa [splitBlock, List.replicate_succ] using ih
      · simp [splitBlock, h]

lemma splitBlock_pos {a : Γ} {w : GroundWord Γ} : 0 < (splitBlock a (a :: w)).1 := by
  simp [splitBlock]

variable [Fresh Γ]

lemma pieces_front (w : GroundWord Γ) :
    List.replicate (pieces w).p (pieces w).a ++ (pieces w).rest = w :=
  (splitBlock_spec _ w).1

lemma pieces_back (w : GroundWord Γ) :
    (pieces w).mid ++ List.replicate (pieces w).q (pieces w).b = (pieces w).rest := by
  have := congrArg List.reverse (splitBlock_spec (pieces w).b (pieces w).rest.reverse).1
  simpa [pieces] using this

lemma pieces_p_pos {w : GroundWord Γ} (hw : w ≠ []) : 0 < (pieces w).p := by
  obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  exact splitBlock_pos

lemma pieces_q_pos {w : GroundWord Γ} (hr : (pieces w).rest ≠ []) : 0 < (pieces w).q := by
  have : (pieces w).rest.reverse = (pieces w).b :: ((pieces w).rest.reverse.tail) := by
    rcases h : (pieces w).rest.reverse with _ | ⟨c, r⟩
    · simp_all
    · have : (pieces w).b = c := by
        simp only [pieces, List.getLastD_eq_getLast?] at h ⊢
        rw [← List.head?_reverse, h]
        rfl
      simp [this]
  change 0 < (splitBlock (pieces w).b (pieces w).rest.reverse).1
  rw [this]
  exact splitBlock_pos

lemma pieces_mid_head {w : GroundWord Γ} (hm : (pieces w).mid ≠ []) :
    (pieces w).mid.head? ≠ some (pieces w).a := by
  have h1 : (pieces w).rest.head? ≠ some (pieces w).a := (splitBlock_spec _ w).2
  rw [← pieces_back, List.head?_append, List.head?_eq_some_head hm, Option.some_or] at h1
  rwa [List.head?_eq_some_head hm]

lemma pieces_mid_last (w : GroundWord Γ) : (pieces w).mid.getLast? ≠ some (pieces w).b := by
  simpa [pieces, List.getLast?_reverse] using
    (splitBlock_spec (pieces w).b (pieces w).rest.reverse).2

lemma pieces_a_mem {w : GroundWord Γ} (hw : w ≠ []) : (pieces w).a ∈ w := by
  obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [pieces]

lemma pieces_b_mem {w : GroundWord Γ} (hr : (pieces w).rest ≠ []) : (pieces w).b ∈ w := by
  have hb : (pieces w).b = (pieces w).rest.getLast hr := by
    change (pieces w).rest.getLastD (Fresh.fresh ∅) = _
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hr]
    rfl
  have := List.mem_append_right (List.replicate (pieces w).p (pieces w).a)
    (hb ▸ List.getLast_mem hr)
  rwa [pieces_front] at this

lemma prefSuffOf_mem_prefSuffs {A w : List Γ} (h : ∀ a ∈ w, a ∈ A) :
    prefSuffOf w ∈ prefSuffs A := by
  unfold prefSuffOf
  split_ifs with h1 h2 h3
  · simp [prefSuffs]
  · simp [prefSuffs, h (pieces w).a (pieces_a_mem h1)]
  · simp [prefSuffs, h (pieces w).a (pieces_a_mem h1), h (pieces w).b (pieces_b_mem h2)]
  · simp [prefSuffs, h (pieces w).a (pieces_a_mem h1), h (pieces w).b (pieces_b_mem h2)]

variable [DecidableEq V.Word]

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma instantiate_symbolicSide (ℓ : Nat → Nat) (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat)
    (u : Side Γ V) :
    instantiate ℓ (symbolicSide sh idx u) =
      substSide (fun x ↦ instantiate ℓ (prefSuffSyms (idx x) x (sh x))) u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp_all [symbolicSide, substSide, Length.eval, letters]

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma positive_prefSuffSyms (i : Nat) (x : V.Word) (s : PrefSuff Γ) :
    Positive (prefSuffSyms i x s) := by
  intro a E h
  rcases s with _ | b | ⟨b, c⟩ | ⟨b, c⟩
  · simp [prefSuffSyms] at h
  · simp only [prefSuffSyms, List.mem_singleton, BlockSym.block.injEq] at h
    rw [h.2]
    exact Nat.one_pos
  · simp only [prefSuffSyms, List.mem_cons, BlockSym.block.injEq, List.mem_nil_iff, or_false] at h
    rcases h with h | h <;> rw [h.2] <;> exact Nat.one_pos
  · simp only [prefSuffSyms, List.mem_cons, BlockSym.block.injEq, reduceCtorEq, false_or,
      List.mem_nil_iff, or_false] at h
    rcases h with h | h <;> rw [h.2] <;> exact Nat.one_pos

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma positive_symbolicSide (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (u : Side Γ V) :
    Positive (symbolicSide sh idx u) := by
  intro a E h
  simp only [symbolicSide, List.mem_flatMap] at h
  obtain ⟨s, -, hs⟩ := h
  rcases s with b | x
  · simp only [List.mem_singleton, BlockSym.block.injEq] at hs
    rw [hs.2]
    exact Nat.one_pos
  · exact positive_prefSuffSyms _ x (sh x) a E hs

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
@[simp] lemma symbolicSide_nil (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) :
    symbolicSide sh idx [] = [] := rfl

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
@[simp] lemma symbolicSide_cons_letter (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (a : Γ)
    (u : Side Γ V) :
    symbolicSide sh idx (.inl a :: u) = .block a ⟨1, []⟩ :: symbolicSide sh idx u := rfl

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
@[simp] lemma symbolicSide_cons_var (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (x : V.Word)
    (u : Side Γ V) :
    symbolicSide sh idx (.inr x :: u) = prefSuffSyms (idx x) x (sh x) ++ symbolicSide sh idx u :=
  rfl

omit [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word] in
lemma symbolicSide_congr {sh sh' : V.Word → PrefSuff Γ} {idx : V.Word → Nat} {u : Side Γ V}
    (h : ∀ x ∈ sideVars u, sh x = sh' x) : symbolicSide sh idx u = symbolicSide sh' idx u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
      cases s with
      | inl a => simp [ih (by simpa using h)]
      | inr x => simp [h x (by simp), ih fun y hy ↦ h y (by simp [hy])]

omit [Fresh Γ] [DecidableEq V.Word] in
lemma symbolicSides_congr {sh sh' : V.Word → PrefSuff Γ} {idx : V.Word → Nat} {e : Eqn Γ V}
    (h : ∀ x ∈ e.vars, sh x = sh' x) : symbolicSides sh idx e = symbolicSides sh' idx e := by
  simp only [symbolicSides]
  rw [symbolicSide_congr fun x hx ↦ h x (by simp [Eqn.vars, hx]),
    symbolicSide_congr (u := e.2) fun x hx ↦ h x (by simp [Eqn.vars, hx])]

omit [DecidableEq V.Word] in
lemma blockLetter_inj {e : Eqn Γ V} {n c d : Nat} (hc : c < n) (hd : d < n)
    (h : blockLetter e n c = blockLetter e n d) : c = d := by
  have hnd : (blockLetters e n).Nodup := nodup_freshList _ _
  have hc' : c < (blockLetters e n).length := by simpa [blockLetters] using hc
  have hd' : d < (blockLetters e n).length := by simpa [blockLetters] using hd
  simp only [blockLetter, List.getElem?_eq_getElem hc', List.getElem?_eq_getElem hd',
    Option.getD_some] at h
  exact (hnd.getElem_inj_iff).1 h

lemma replaceBlocks_eq (sh : V.Word → PrefSuff Γ) (cls : List Nat) (e : Eqn Γ V) :
    replaceBlocks sh cls e =
      (label (cls.map (blockLetter e (allBlocks sh e.vars.idxOf e).length))
          (symbolicSides sh e.vars.idxOf e).1,
        label ((cls.drop (blocks (symbolicSides sh e.vars.idxOf e).1).length).map
          (blockLetter e (allBlocks sh e.vars.idxOf e).length))
          (symbolicSides sh e.vars.idxOf e).2) := rfl

theorem solvable_of_replaceBlocks {sh : V.Word → PrefSuff Γ} {cls : List Nat} {e : Eqn Γ V}
    {ℓ : Nat → Nat} (hlen : cls.length = (allBlocks sh e.vars.idxOf e).length)
    (hlt : ∀ c ∈ cls, c < (allBlocks sh e.vars.idxOf e).length)
    (hc : Consistent cls (allBlocks sh e.vars.idxOf e) ℓ)
    (h : (replaceBlocks sh cls e).Solvable) : e.Solvable := by
  obtain ⟨τ, hτ⟩ := h
  rw [replaceBlocks_eq] at hτ
  generalize hname : blockLetter e (allBlocks sh e.vars.idxOf e).length = name at hτ
  have hinj : ∀ p ∈ cls.zip (allBlocks sh e.vars.idxOf e),
      ∀ q ∈ cls.zip (allBlocks sh e.vars.idxOf e), name p.1 = name q.1 → p.1 = q.1 :=
    fun p hp q hq h ↦ blockLetter_inj (hlt _ (List.of_mem_zip hp).1)
      (hlt _ (List.of_mem_zip hq).1) (hname ▸ h)
  have hB : allBlocks sh e.vars.idxOf e =
      blocks (symbolicSides sh e.vars.idxOf e).1 ++ blocks (symbolicSides sh e.vars.idxOf e).2 :=
    rfl
  generalize hL : (symbolicSides sh e.vars.idxOf e).1 = L at hτ hB
  generalize hR : (symbolicSides sh e.vars.idxOf e).2 = R at hτ hB
  have hn : (blocks L).length ≤ cls.length := by simp [hlen, hB]
  have hzip : cls.zip (allBlocks sh e.vars.idxOf e) =
      (cls.take (blocks L).length).zip (blocks L) ++
        (cls.drop (blocks L).length).zip (blocks R) := by
    conv_lhs => rw [← List.take_append_drop (blocks L).length cls]
    rw [hB, List.zip_append (by simp [hn])]
  have hstep : label (cls.map name) L = label ((cls.take (blocks L).length).map name) L := by
    conv_lhs => rw [← List.take_append_drop (blocks L).length cls, List.map_append]
    exact label_append _ _ _ (by simp [hn])
  have hexp : ∀ (M : List (BlockSym Γ V)) (ls : List Nat), ls.length = (blocks M).length →
      (∀ p ∈ ls.zip (blocks M), p ∈ cls.zip (allBlocks sh e.vars.idxOf e)) →
      expandSide (classExpand name cls (allBlocks sh e.vars.idxOf e) ℓ) (label (ls.map name) M) =
        instantiate ℓ M := by
    intro M ls hl hs
    refine expandSide_label _ ℓ M (ls.map name) (by simpa using hl) fun p hp ↦ ?_
    rw [List.zip_map_left, List.mem_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    exact classExpand_of_mem hc hinj (hs p' hp')
  have := Eqn.solves_expandSide (classExpand name cls (allBlocks sh e.vars.idxOf e) ℓ) hτ
  rw [hstep] at this
  simp only [Eqn.map] at this
  rw [hexp L _ (by simp [hn]) (fun p hp ↦ by rw [hzip]; exact List.mem_append_left _ hp),
    hexp R _ (by simp [hlen, hB]) (fun p hp ↦ by rw [hzip]; exact List.mem_append_right _ hp)]
    at this
  simp only [symbolicSides] at hL hR
  rw [← hL, ← hR, instantiate_merge, instantiate_merge, instantiate_symbolicSide,
    instantiate_symbolicSide] at this
  exact ⟨_, Eqn.solves_of_substSide (e := e) this⟩

private lemma getElem?_idxOf_of_mem {l : List V.Word} {x : V.Word} (hx : x ∈ l) :
    l[l.idxOf x]? = some x := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

lemma lengthsOf_even (σ : Subst Γ V) {e : Eqn Γ V} {x : V.Word} (hx : x ∈ e.vars) :
    lengthsOf σ e (2 * e.vars.idxOf x) = (pieces (σ x)).p - 1 := by
  have h2 : 2 * e.vars.idxOf x / 2 = e.vars.idxOf x := by omega
  simp [lengthsOf, h2, getElem?_idxOf_of_mem hx]

lemma lengthsOf_odd (σ : Subst Γ V) {e : Eqn Γ V} {x : V.Word} (hx : x ∈ e.vars) :
    lengthsOf σ e (2 * e.vars.idxOf x + 1) = (pieces (σ x)).q - 1 := by
  have h2 : (2 * e.vars.idxOf x + 1) / 2 = e.vars.idxOf x := by omega
  simp [lengthsOf, h2, getElem?_idxOf_of_mem hx]

lemma eval_front (σ : Subst Γ V) {e : Eqn Γ V} {x : V.Word} (hx : x ∈ e.vars) (h : σ x ≠ []) :
    Length.eval (lengthsOf σ e) ⟨1, [2 * e.vars.idxOf x]⟩ = (pieces (σ x)).p := by
  have := pieces_p_pos h
  simp only [Length.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    lengthsOf_even σ hx]
  omega

lemma eval_back (σ : Subst Γ V) {e : Eqn Γ V} {x : V.Word} (hx : x ∈ e.vars)
    (h : (pieces (σ x)).rest ≠ []) :
    Length.eval (lengthsOf σ e) ⟨1, [2 * e.vars.idxOf x + 1]⟩ = (pieces (σ x)).q := by
  have := pieces_q_pos h
  simp only [Length.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    lengthsOf_odd σ hx]
  omega

lemma prefSuffOf_pop (name : Γ → Nat → Γ) (σ : Subst Γ V) {e : Eqn Γ V} {x : V.Word}
    (hx : x ∈ e.vars) :
    instantiate (lengthsOf σ e) (prefSuffSyms (e.vars.idxOf x) x (prefSuffOf (σ x))) =
        letters (σ x) ∨
      ∃ pre post, instantiate (lengthsOf σ e)
            (prefSuffSyms (e.vars.idxOf x) x (prefSuffOf (σ x))) =
          letters pre ++ .inr x :: letters post ∧
        σ x = pre ++ blockMid σ x ++ post ∧
        ∀ q E, compressBlocks name (q ++ pre ++ blockMid σ x ++ post ++ E) =
          compressBlocks name (q ++ pre) ++ compressBlocks name (blockMid σ x) ++
            compressBlocks name (post ++ E) := by
  have hf := pieces_front (σ x)
  have hb := pieces_back (σ x)
  unfold prefSuffOf
  split_ifs with h1 h2 h3
  · left
    simp [prefSuffSyms, h1, letters]
  · left
    simp only [prefSuffSyms, instantiate_cons_block, instantiate_nil, List.append_nil,
      eval_front σ hx h1]
    conv_rhs => rw [← hf, h2, List.append_nil]
  · left
    simp only [prefSuffSyms, instantiate_cons_block, instantiate_nil, List.append_nil,
      eval_front σ hx h1, eval_back σ hx h2]
    conv_rhs => rw [← hf, ← hb, h3]
    simp [letters]
  · right
    have hp := pieces_p_pos h1
    have hq := pieces_q_pos h2
    refine ⟨List.replicate (pieces (σ x)).p (pieces (σ x)).a,
      List.replicate (pieces (σ x)).q (pieces (σ x)).b, ?_, ?_, fun q E ↦ ?_⟩
    · simp [prefSuffSyms, eval_front σ hx h1, eval_back σ hx h2]
    · rw [blockMid, List.append_assoc, hb, hf]
    · rw [blockMid]
      have e1 : q ++ List.replicate (pieces (σ x)).p (pieces (σ x)).a ++ (pieces (σ x)).mid ++
          List.replicate (pieces (σ x)).q (pieces (σ x)).b ++ E =
          (q ++ List.replicate (pieces (σ x)).p (pieces (σ x)).a) ++
            ((pieces (σ x)).mid ++ (List.replicate (pieces (σ x)).q (pieces (σ x)).b ++ E)) := by
        simp
      have b2 : ∀ c, (pieces (σ x)).mid.getLast? = some c →
          (List.replicate (pieces (σ x)).q (pieces (σ x)).b ++ E).head? ≠ some c := by
        intro c hc hc'
        obtain ⟨n, hn⟩ : ∃ n, (pieces (σ x)).q = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
        rw [hn] at hc'
        simp only [List.replicate_succ, List.cons_append, List.head?_cons,
          Option.some.injEq] at hc'
        exact pieces_mid_last (σ x) (hc' ▸ hc)
      have b1 : ∀ c, (q ++ List.replicate (pieces (σ x)).p (pieces (σ x)).a).getLast? = some c →
          ((pieces (σ x)).mid ++ (List.replicate (pieces (σ x)).q (pieces (σ x)).b ++ E)).head? ≠
            some c := by
        intro c hc hc'
        obtain ⟨n, hn⟩ : ∃ n, (pieces (σ x)).p = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
        rw [hn, List.getLast?_append, List.getLast?_replicate] at hc
        simp only [Nat.add_one_ne_zero, ite_false, Option.some_or, Option.some.injEq] at hc
        subst hc
        rw [List.head?_append, List.head?_eq_some_head h3, Option.some_or] at hc'
        exact pieces_mid_head h3 (by rw [List.head?_eq_some_head h3]; exact hc')
      rw [e1, compressBlocks_append _ _ _ b1, compressBlocks_append _ _ _ b2]
      simp

lemma eval_blockStep_side (σ : Subst Γ V) (e : Eqn Γ V) (u : Side Γ V)
    (hu : ∀ x ∈ sideVars u, x ∈ e.vars) :
    compressBlocks (blockName σ e) (eval σ u) =
      eval (fun x ↦ compressBlocks (blockName σ e) (blockMid σ x))
        (label ((blocks (merge (symbolicSide (prefSuffsOf σ) e.vars.idxOf u))).map
          fun p ↦ blockName σ e p.1 (p.2.eval (lengthsOf σ e)))
          (merge (symbolicSide (prefSuffsOf σ) e.vars.idxOf u))) := by
  have := eval_mapRuns_substSide (compressBlocks (blockName σ e))
    (fun x ↦ instantiate (lengthsOf σ e) (prefSuffSyms (e.vars.idxOf x) x (prefSuffsOf σ x))) σ
    (blockMid σ) u (fun x hx ↦ prefSuffOf_pop _ σ (hu x hx)) []
  rw [← mapRuns_compressBlocks_instantiate _ _ _ (merged_merge _)
    (positive_merge (positive_symbolicSide _ _ _)), instantiate_merge, instantiate_symbolicSide]
  simpa [letters] using this

omit [DecidableEq Γ] [Fresh Γ] in
lemma mem_zip_map_self {f : Γ × Length → Nat} {B : List (Γ × Length)} {p : Nat × (Γ × Length)}
    (hp : p ∈ (B.map f).zip B) : p.2 ∈ B ∧ p.1 = f p.2 := by
  induction B with
  | nil => simp at hp
  | cons b B ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact ⟨List.mem_cons_of_mem _ (ih hp).1, (ih hp).2⟩

theorem replaceBlocks_complete {e : Eqn Γ V} {σ : Subst Γ V} (hσ : e.Solves σ) :
    (classesOf σ e).length = (allBlocks (prefSuffsOf σ) e.vars.idxOf e).length ∧
      (∀ c ∈ classesOf σ e, c < (allBlocks (prefSuffsOf σ) e.vars.idxOf e).length) ∧
      Consistent (classesOf σ e) (allBlocks (prefSuffsOf σ) e.vars.idxOf e) (lengthsOf σ e) ∧
      (replaceBlocks (prefSuffsOf σ) (classesOf σ e) e).Solves
        (fun x ↦ compressBlocks (blockName σ e) (blockMid σ x)) ∧
      eval (fun x ↦ compressBlocks (blockName σ e) (blockMid σ x))
          (replaceBlocks (prefSuffsOf σ) (classesOf σ e) e).1 =
        compressBlocks (blockName σ e) (eval σ e.1) := by
  refine ⟨by simp [classesOf], fun c hc ↦ ?_, fun p hp q hq hpq ↦ ?_, ?_⟩
  · simp only [classesOf, List.mem_map] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    have : (b.1, b.2.eval (lengthsOf σ e)) ∈ blockValues σ e :=
      List.mem_map.2 ⟨b, hb, rfl⟩
    have := List.idxOf_lt_length_of_mem this
    simpa [blockClass, blockValues] using this
  · obtain ⟨hp, hp'⟩ := mem_zip_map_self hp
    obtain ⟨hq, hq'⟩ := mem_zip_map_self hq
    rw [hp', hq'] at hpq
    simp only [blockClass] at hpq
    have := (List.idxOf_inj (l := blockValues σ e)
      (List.mem_map.2 ⟨p.2, hp, rfl⟩)).1 hpq
    simp only [Prod.mk.injEq] at this
    exact this
  · have hsplit : classesOf σ e =
        (blocks (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).1).map
            (fun p ↦ blockClass σ e p.1 (p.2.eval (lengthsOf σ e))) ++
          (blocks (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).2).map
            (fun p ↦ blockClass σ e p.1 (p.2.eval (lengthsOf σ e))) := by
      simp [classesOf, allBlocks]
    have hl : replaceBlocks (prefSuffsOf σ) (classesOf σ e) e =
        (label ((blocks (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).1).map
            (fun p ↦ blockName σ e p.1 (p.2.eval (lengthsOf σ e))))
            (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).1,
          label ((blocks (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).2).map
            (fun p ↦ blockName σ e p.1 (p.2.eval (lengthsOf σ e))))
            (symbolicSides (prefSuffsOf σ) e.vars.idxOf e).2) := by
      rw [replaceBlocks_eq, hsplit, List.drop_left' (by simp), List.map_append,
        label_append _ _ _ (by simp), List.map_map, List.map_map]
      rfl
    rw [hl]
    simp only [Eqn.Solves, symbolicSides]
    rw [← eval_blockStep_side _ _ _ fun x hx ↦ by simp [Eqn.vars, hx],
      ← eval_blockStep_side _ _ _ fun x hx ↦ by simp [Eqn.vars, hx]]
    exact ⟨congrArg _ hσ, rfl⟩

end

section

lemma extend_getElem {U : List Nat} (hU : U.Nodup) (v : Fin U.length → Nat) (i : Fin U.length) :
    extend U v U[i] = v i := by
  have h : U.idxOf U[i] = i := hU.idxOf_getElem _ _
  simp only [extend, h, i.2, ↓reduceDIte]

lemma sum_count_mul {U : List Nat} (hU : U.Nodup) (v : Fin U.length → Nat) :
    ∀ vs : List Nat, (∀ x ∈ vs, x ∈ U) →
      ∑ i : Fin U.length, (vs.count U[i] : ℤ) * (v i : ℤ) = ((vs.map (extend U v)).sum : ℤ)
  | [], _ => by simp
  | x :: vs, h => by
      have hx : x ∈ U := h x (by simp)
      have ih := sum_count_mul hU v vs fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
      set j : Fin U.length := ⟨U.idxOf x, List.idxOf_lt_length_of_mem hx⟩
      have hj : U[j] = x := List.getElem_idxOf _
      have h1 : ∑ i : Fin U.length, ((if (x == U[i]) = true then 1 else 0 : Nat) : ℤ) * (v i : ℤ) =
          (v j : ℤ) := by
        rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro i _ hi
          have hne : x ≠ U[(i : Nat)] := by
            intro e
            refine hi (Fin.ext ?_)
            show (i : Nat) = U.idxOf x
            rw [e]
            exact (hU.idxOf_getElem _ i.2).symm
          simp [hne]
        · simp
      have hext : extend U v x = v j := by rw [← hj, extend_getElem hU]
      simp only [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, h1,
        List.map_cons, List.sum_cons, hext]
      push_cast
      ring

lemma mem_lenVars {eqs : List (Length × Length)} {p : Length × Length} (hp : p ∈ eqs) {x : Nat}
    (hx : x ∈ p.1.vars ∨ x ∈ p.2.vars) : x ∈ lenVars eqs :=
  List.mem_dedup.2 (List.mem_flatMap.2 ⟨p, hp, List.mem_append.2 hx⟩)

lemma lenSystem_solves_iff {eqs : List (Length × Length)} (v : Fin (lenVars eqs).length → Nat) :
    (lenSystem eqs).Solves v ↔
      ∀ p ∈ eqs, p.1.eval (extend _ v) = p.2.eval (extend _ v) := by
  have hU : (lenVars eqs).Nodup := List.nodup_dedup _
  have key : ∀ r : Fin eqs.length,
      ∑ i, (lenSystem eqs).A r i * (v i : ℤ) = (lenSystem eqs).b r ↔
        (eqs.get r).1.eval (extend _ v) = (eqs.get r).2.eval (extend _ v) := by
    intro r
    have hm := List.get_mem eqs r
    simp only [lenSystem, sub_mul, Finset.sum_sub_distrib]
    rw [sum_count_mul hU v _ fun x hx ↦ mem_lenVars hm (.inl hx),
      sum_count_mul hU v _ fun x hx ↦ mem_lenVars hm (.inr hx)]
    simp only [Length.eval]
    omega
  simp only [LinSystem.Solves, key]
  constructor
  · intro h p hp
    obtain ⟨r, rfl⟩ := List.get_of_mem hp
    exact h r
  · intro h r
    exact h _ (List.get_mem eqs r)

lemma lenSystem_solvable_iff (eqs : List (Length × Length)) :
    (lenSystem eqs).Solvable ↔ LenSolvable eqs := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨extend _ v, (lenSystem_solves_iff v).1 hv⟩
  · rintro ⟨ℓ, hℓ⟩
    refine ⟨fun i ↦ ℓ (lenVars eqs)[i], (lenSystem_solves_iff _).2 fun p hp ↦ ?_⟩
    have hE : ∀ E : Length, (∀ x ∈ E.vars, x ∈ lenVars eqs) →
        E.eval (extend _ fun i : Fin (lenVars eqs).length ↦ ℓ (lenVars eqs)[i]) = E.eval ℓ := by
      intro E hE
      simp only [Length.eval]
      congr 2
      refine List.map_congr_left fun x hx ↦ ?_
      have hx := hE x hx
      have hlt := List.idxOf_lt_length_of_mem hx
      simp only [extend, hlt, ↓reduceDIte]
      exact congrArg ℓ (List.getElem_idxOf hlt)
    rw [hE p.1 fun x hx ↦ mem_lenVars hp (.inl hx), hE p.2 fun x hx ↦ mem_lenVars hp (.inr hx)]
    exact hℓ p hp

lemma exists_consistent_iff (cls : List Nat) (B : List (Γ × Length)) :
    (∃ ℓ, Consistent cls B ℓ) ↔ SameLetters cls B ∧ LenSolvable (classEquations cls B) := by
  constructor
  · rintro ⟨ℓ, h⟩
    refine ⟨fun p hp q hq hpq ↦ (h p hp q hq hpq).1, ℓ, fun e he ↦ ?_⟩
    simp only [classEquations, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq] at he
    obtain ⟨p, hp, q, hq, hpq, rfl⟩ := he
    exact (h p hp q hq hpq).2
  · rintro ⟨hl, ℓ, h⟩
    refine ⟨ℓ, fun p hp q hq hpq ↦ ⟨hl p hp q hq hpq, h (p.2.2, q.2.2) ?_⟩⟩
    simp only [classEquations, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq]
    exact ⟨p, hp, q, hq, hpq, rfl⟩

lemma blockComp_check_iff [DecidableEq Γ] (cls : List Nat) (B : List (Γ × Length)) :
    SameLetters cls B ∧ true ∈ (wordToDioph cls B).verify ↔ ∃ ℓ, Consistent cls B ℓ := by
  rw [exists_consistent_iff, ← lenSystem_solvable_iff, ← LinSystem.true_mem_verify_iff]
  rfl

end

end Accordion.WE.Decidability

end
