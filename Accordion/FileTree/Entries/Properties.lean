module

public import Accordion.FileTree.Entries
public import Mathlib.Data.Finmap

@[expose] public section

namespace Accordion

namespace FileTree

namespace Entries

variable {Γ β : Type} [Ord Γ]

@[simp] theorem canonical_empty : (empty : Entries Γ β).Canonical := by
  simp [Canonical, empty]

@[simp] theorem lookup_empty (a : Γ) : (∅ : Entries Γ β).lookup a = none := rfl

theorem lookup_erase_self (m : Entries Γ β) (a : Γ) : (m.erase a).lookup a = none := by
  simp [erase, lookup, List.findSome?_eq_none_iff]

private theorem insList_mem_or {l : List (Γ × β)} {a : Γ} {b : β} {x : Γ × β}
    (hx : x ∈ insList a b l) : x = (a, b) ∨ (∃ y ∈ l, x = (y.1, b)) ∨ x ∈ l := by
  induction l with
  | nil =>
      simp only [insList, List.mem_singleton] at hx
      exact Or.inl hx
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      cases hak : compare a k with
      | lt =>
          simp only [insList, hak, List.mem_cons] at hx
          rcases hx with hx | hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inr (hx ▸ List.mem_cons_self ..))
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx))
      | eq =>
          simp only [insList, hak, List.mem_cons] at hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl ⟨(k, v), List.mem_cons_self .., hx⟩)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx))
      | gt =>
          simp only [insList, hak, List.mem_cons] at hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inr (hx ▸ List.mem_cons_self ..))
          · rcases ih hx with hx' | ⟨y, hy, hxy⟩ | hx'
            · exact Or.inl hx'
            · exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, hxy⟩)
            · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx'))

theorem mem_insert_iff {m : Entries Γ β} {a : Γ} {b : β} {x : Γ × β}
    (hx : x ∈ (m.insert a b).map) : x.2 = b ∨ x ∈ m.map := by
  rcases insList_mem_or hx with h | ⟨_, _, hxy⟩ | h
  · exact Or.inl (by rw [h])
  · exact Or.inl (by rw [hxy])
  · exact Or.inr h

private theorem insList_pairwise [Std.TransCmp (compare : Γ → Γ → Ordering)]
    {l : List (Γ × β)} (h : l.Pairwise (fun p q => compare p.1 q.1 = .lt)) (a : Γ) (b : β) :
    (insList a b l).Pairwise (fun p q => compare p.1 q.1 = .lt) := by
  induction l with
  | nil => simp [insList]
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      have htl := h.of_cons
      have hrel : ∀ {x : Γ × β}, x ∈ tl → compare k x.1 = .lt :=
        fun hx => List.rel_of_pairwise_cons h hx
      cases hak : compare a k with
      | lt =>
          simp only [insList, hak]
          refine List.Pairwise.cons ?_ h
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · exact hx ▸ hak
          · exact Std.TransCmp.lt_trans hak (hrel hx)
      | eq =>
          simp only [insList, hak]
          exact List.Pairwise.cons (fun x hx => hrel hx) htl
      | gt =>
          simp only [insList, hak]
          refine List.Pairwise.cons ?_ (ih htl)
          intro x hx
          rcases insList_mem_or hx with hx | ⟨y, hy, hxy⟩ | hx
          · exact hx ▸ Std.OrientedCmp.lt_of_gt hak
          · have h := hrel hy; rw [hxy]; exact h
          · exact hrel hx

theorem canonical_insert [Std.TransCmp (compare : Γ → Γ → Ordering)]
    {m : Entries Γ β} (h : m.Canonical) (a : Γ) (b : β) : (m.insert a b).Canonical := by
  exact insList_pairwise h a b

theorem canonical_erase {m : Entries Γ β} (h : m.Canonical) (a : Γ) : (m.erase a).Canonical := by
  exact List.Pairwise.sublist List.filter_sublist h

theorem lookup_insList_self [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]
    (l : List (Γ × β)) (a : Γ) (b : β) :
    (insList a b l).findSome? (fun p => if compare a p.1 = .eq then some p.2 else none)
      = some b := by
  induction l with
  | nil => simp [insList]
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      cases hak : compare a k with
      | lt => simp [insList, hak]
      | eq => simp [insList, hak]
      | gt => simp [insList, hak, ih]

private theorem lookup_insList_ne [Std.TransCmp (compare : Γ → Γ → Ordering)]
    (l : List (Γ × β)) (a q : Γ) (b : β) (haq : compare a q ≠ .eq) :
    (insList a b l).findSome? (fun p => if compare q p.1 = .eq then some p.2 else none)
      = l.findSome? (fun p => if compare q p.1 = .eq then some p.2 else none) := by
  have hqa : compare q a ≠ .eq := fun h => haq (Std.OrientedCmp.eq_symm h)
  induction l with
  | nil => simp [insList, hqa]
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      cases hak : compare a k with
      | lt => simp [insList, hak, hqa]
      | eq =>
          have hqk : compare q k ≠ .eq := by
            intro hqk
            exact haq (Std.TransCmp.eq_trans hak (Std.OrientedCmp.eq_symm hqk))
          simp [insList, hak, hqk]
      | gt => simp [insList, hak, List.findSome?_cons, ih]

private theorem lookup_erase_list_ne [Std.TransCmp (compare : Γ → Γ → Ordering)]
    (l : List (Γ × β)) (a q : Γ) (haq : compare a q ≠ .eq) :
    (l.filter (fun p => compare a p.1 != .eq)).findSome?
        (fun p => if compare q p.1 = .eq then some p.2 else none)
      = l.findSome? (fun p => if compare q p.1 = .eq then some p.2 else none) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      by_cases hak : compare a k = .eq
      · have hqk : compare q k ≠ .eq := by
          intro hqk
          exact haq (Std.TransCmp.eq_trans hak (Std.OrientedCmp.eq_symm hqk))
        simp [hak, hqk, ih]
      · simp [hak, List.findSome?_cons, ih]

theorem lookup_insert_self [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]
    (m : Entries Γ β) (a : Γ) (b : β) : (m.insert a b).lookup a = some b :=
  lookup_insList_self m.map a b

theorem lookup_insert_ne [Std.TransCmp (compare : Γ → Γ → Ordering)]
    (m : Entries Γ β) (a q : Γ) (b : β) (haq : compare a q ≠ .eq) :
    (m.insert a b).lookup q = m.lookup q :=
  lookup_insList_ne m.map a q b haq

theorem lookup_erase_ne [Std.TransCmp (compare : Γ → Γ → Ordering)]
    (m : Entries Γ β) (a q : Γ) (haq : compare a q ≠ .eq) :
    (m.erase a).lookup q = m.lookup q :=
  lookup_erase_list_ne m.map a q haq

private theorem findSome_none_of_forall_lt (l : List (Γ × β)) (c : Γ)
    (H : ∀ x ∈ l, compare c x.1 = .lt) :
    l.findSome? (fun p => if compare c p.1 = .eq then some p.2 else none) = none := by
  rw [List.findSome?_eq_none_iff]
  intro x hx
  rw [ite_eq_right]
  intro hh
  have hlt := H x hx
  rw [hh] at hlt
  simp at hlt

private theorem list_ext [Std.TransCmp (compare : Γ → Γ → Ordering)]
    [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)] :
    ∀ (l l' : List (Γ × β)),
      l.Pairwise (fun p q => compare p.1 q.1 = .lt) →
      l'.Pairwise (fun p q => compare p.1 q.1 = .lt) →
      (∀ a, l.findSome? (fun p => if compare a p.1 = .eq then some p.2 else none)
          = l'.findSome? (fun p => if compare a p.1 = .eq then some p.2 else none)) →
      l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' _ _ h
      cases l' with
      | nil => rfl
      | cons hd r' =>
          obtain ⟨k, v⟩ := hd
          have hk := h k
          simp at hk
  | cons hd tl ih =>
      obtain ⟨k, d⟩ := hd
      intro l' hp hp' h
      cases l' with
      | nil =>
          have hk := h k
          simp at hk
      | cons hd' r' =>
          obtain ⟨k', d'⟩ := hd'
          have hrel : ∀ {x : Γ × β}, x ∈ tl → compare k x.1 = .lt :=
            fun hx => List.rel_of_pairwise_cons hp hx
          have hrel' : ∀ {x : Γ × β}, x ∈ r' → compare k' x.1 = .lt :=
            fun hx => List.rel_of_pairwise_cons hp' hx
          have htl := hp.of_cons
          have hr' := hp'.of_cons
          cases hkk' : compare k k' with
          | lt =>
              exfalso
              have hk := h k
              have hlhs : ((k, d) :: tl).findSome?
                  (fun p => if compare k p.1 = .eq then some p.2 else none) = some d := by
                simp
              have hrhs : ((k', d') :: r').findSome?
                  (fun p => if compare k p.1 = .eq then some p.2 else none) = none := by
                apply findSome_none_of_forall_lt
                intro x hx
                rcases List.mem_cons.mp hx with hx | hx
                · rw [hx]; exact hkk'
                · exact Std.TransCmp.lt_trans hkk' (hrel' hx)
              rw [hlhs, hrhs] at hk
              exact absurd hk (by simp)
          | eq =>
              have hkeq : k = k' := Std.LawfulEqCmp.eq_of_compare hkk'
              subst hkeq
              have hk := h k
              simp only [List.findSome?_cons] at hk
              rw [ite_eq_left hkk', ite_eq_left (Std.ReflCmp.compare_self (a := k))] at hk
              have hdeq : d = d' := by
                simpa using hk
              subst hdeq
              have htail : tl = r' := by
                apply ih _ htl hr'
                intro a
                cases hak : compare a k with
                | eq =>
                    have hlnone : tl.findSome?
                        (fun p => if compare a p.1 = .eq then some p.2 else none) = none := by
                      apply findSome_none_of_forall_lt
                      intro x hx
                      exact Std.TransCmp.lt_of_eq_of_lt hak (hrel hx)
                    have hrnone : r'.findSome?
                        (fun p => if compare a p.1 = .eq then some p.2 else none) = none := by
                      apply findSome_none_of_forall_lt
                      intro x hx
                      exact Std.TransCmp.lt_of_eq_of_lt hak (hrel' hx)
                    rw [hlnone, hrnone]
                | lt | gt =>
                    have hane : compare a k ≠ .eq := by rw [hak]; decide
                    have ha := h a
                    simp only [List.findSome?_cons, ite_eq_right hane] at ha
                    exact ha
              rw [htail]
          | gt =>
              exfalso
              have hk' := h k'
              have hrhs : ((k', d') :: r').findSome?
                  (fun p => if compare k' p.1 = .eq then some p.2 else none) = some d' := by
                simp
              have hlhs : ((k, d) :: tl).findSome?
                  (fun p => if compare k' p.1 = .eq then some p.2 else none) = none := by
                apply findSome_none_of_forall_lt
                intro x hx
                rcases List.mem_cons.mp hx with hx | hx
                · rw [hx]; exact Std.OrientedCmp.lt_of_gt hkk'
                · exact Std.TransCmp.lt_trans (Std.OrientedCmp.lt_of_gt hkk') (hrel hx)
              rw [hlhs, hrhs] at hk'
              exact absurd hk' (by simp)

theorem ext [Std.TransCmp (compare : Γ → Γ → Ordering)]
    [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]
    {m m' : Entries Γ β} (hm : m.Canonical) (hm' : m'.Canonical)
    (h : ∀ a, m.lookup a = m'.lookup a) : m = m' := by
  cases m with
  | mk map =>
  cases m' with
  | mk map' =>
  congr 1
  exact list_ext map map' hm hm' h

@[simp] theorem getElem?_eq_lookup (m : Entries Γ β) (a : Γ) : m[a]? = m.lookup a := rfl

theorem mem_iff_lookup_isSome {m : Entries Γ β} {a : Γ} : a ∈ m ↔ (m.lookup a).isSome := by
  constructor
  · rintro ⟨p, hp, hap⟩
    have : (m.lookup a).isSome = true := by
      rw [lookup, List.findSome?_isSome_iff]
      exact ⟨p, hp, by simp [hap]⟩
    simpa using this
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨p, hp, hv⟩ := List.exists_of_findSome?_eq_some hb
    refine ⟨p, hp, ?_⟩
    cases hap : compare a p.1 with
    | eq => rfl
    | lt => simp [hap] at hv
    | gt => simp [hap] at hv

theorem mem_insert_self [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]
    (m : Entries Γ β) (a : Γ) (b : β) : a ∈ m.insert a b :=
  mem_iff_lookup_isSome.mpr (by rw [lookup, insert, lookup_insList_self]; rfl)

theorem not_mem_erase (m : Entries Γ β) (a : Γ) : a ∉ m.erase a := by
  rintro ⟨p, hp, hap⟩
  have := (List.mem_filter.mp hp).2
  simp [hap] at this

theorem insert_erase [Std.TransCmp (compare : Γ → Γ → Ordering)]
    [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]
    {m : Entries Γ β} (h : m.Canonical) {a : Γ} {b : β} (hb : m.lookup a = some b) :
    (m.erase a).insert a b = m := by
  refine ext (canonical_insert (canonical_erase h a) a b) h (fun q => ?_)
  by_cases hq : compare a q = .eq
  · have hqa : q = a := (Std.LawfulEqCmp.eq_of_compare hq).symm
    subst hqa
    exact (lookup_insList_self (m.erase q).map q b).trans hb.symm
  · rw [lookup_insert_ne _ _ _ _ hq, lookup_erase_ne _ _ _ hq]

section Finmap

variable [DecidableEq Γ] [Std.TransCmp (compare : Γ → Γ → Ordering)]
  [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)]

omit [DecidableEq Γ] [Std.TransCmp (compare : Γ → Γ → Ordering)] in
theorem compare_eq_iff {a b : Γ} : compare a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqCmp.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self⟩

def ofSigmas : List ((_ : Γ) × β) → Entries Γ β
  | [] => empty
  | s :: r => (ofSigmas r).insert s.1 s.2

omit [DecidableEq Γ] [Std.LawfulEqCmp (compare : Γ → Γ → Ordering)] in
theorem canonical_ofSigmas (l : List ((_ : Γ) × β)) : (ofSigmas l).Canonical := by
  induction l with
  | nil => exact canonical_empty
  | cons s r ih => exact canonical_insert ih s.1 s.2

theorem lookup_ofSigmas (l : List ((_ : Γ) × β)) (a : Γ) :
    (ofSigmas l).lookup a = l.dlookup a := by
  induction l with
  | nil => simp [ofSigmas, lookup, empty]
  | cons s r ih =>
      obtain ⟨k, v⟩ := s
      by_cases hs : a = k
      · subst hs
        rw [ofSigmas, lookup, insert, lookup_insList_self, List.dlookup_cons_eq]
      · have hne : compare k a ≠ .eq := fun hc => hs (compare_eq_iff.mp hc).symm
        rw [ofSigmas, lookup_insert_ne _ _ _ _ hne, ih,
          List.dlookup_cons_ne _ _ hs]

omit [DecidableEq Γ] [Std.TransCmp (compare : Γ → Γ → Ordering)] in
theorem nodupKeys_sigmas {m : Entries Γ β} (h : m.Canonical) :
    (m.map.map (fun p => (⟨p.1, p.2⟩ : (_ : Γ) × β))).NodupKeys :=
  List.nodupKeys_iff_pairwise.mpr
    (h.map _ (fun p q hpq hc => by rw [compare_eq_iff.mpr hc] at hpq; simp at hpq))

def toFinmap (m : {m : Entries Γ β // m.Canonical}) : Finmap (fun _ : Γ => β) :=
  AList.toFinmap ⟨m.1.map.map (fun p => ⟨p.1, p.2⟩), nodupKeys_sigmas m.2⟩

omit [Std.TransCmp (compare : Γ → Γ → Ordering)] in
theorem lookup_toFinmap (m : {m : Entries Γ β // m.Canonical}) (a : Γ) :
    (toFinmap m).lookup a = m.1.lookup a := by
  rw [toFinmap, Finmap.lookup_toFinmap]
  show (m.1.map.map (fun p => (⟨p.1, p.2⟩ : (_ : Γ) × β))).dlookup a = _
  obtain ⟨⟨l⟩, h⟩ := m
  induction l with
  | nil => simp [lookup]
  | cons p r ih =>
      obtain ⟨k, v⟩ := p
      by_cases hp : a = k
      · subst hp
        simp [lookup, List.dlookup_cons_eq]
      · rw [List.map_cons, List.dlookup_cons_ne _ _ hp, lookup,
          List.findSome?_cons, ite_eq_right (fun hc => hp (compare_eq_iff.mp hc))]
        exact ih h.of_cons

theorem toFinmap_injective : Function.Injective (toFinmap (Γ := Γ) (β := β)) :=
  fun m m' h => Subtype.ext (ext m.2 m'.2 (fun a => by
    rw [← lookup_toFinmap m, ← lookup_toFinmap m', h]))

def ofFinmap (f : Finmap (fun _ : Γ => β)) : {m : Entries Γ β // m.Canonical} :=
  f.liftOn (fun l => ⟨ofSigmas l.entries, canonical_ofSigmas _⟩) (fun l l' h => by
    refine Subtype.ext (ext (canonical_ofSigmas _) (canonical_ofSigmas _) (fun a => ?_))
    rw [lookup_ofSigmas, lookup_ofSigmas]
    exact List.perm_dlookup a l.nodupKeys h)

theorem lookup_ofFinmap (f : Finmap (fun _ : Γ => β)) (a : Γ) :
    (ofFinmap f).1.lookup a = f.lookup a := by
  induction f using Finmap.induction_on with
  | _ l =>
      rw [ofFinmap, Finmap.liftOn_toFinmap, Finmap.lookup_toFinmap, lookup_ofSigmas]
      rfl

theorem toFinmap_ofFinmap (f : Finmap (fun _ : Γ => β)) : toFinmap (ofFinmap f) = f :=
  Finmap.ext_lookup (fun a => by rw [lookup_toFinmap, lookup_ofFinmap])

/-- Canonical `Entries` are mathlib's `Finmap`. -/
def equivFinmap : {m : Entries Γ β // m.Canonical} ≃ Finmap (fun _ : Γ => β) where
  toFun := toFinmap
  invFun := ofFinmap
  left_inv _ := toFinmap_injective (toFinmap_ofFinmap _)
  right_inv := toFinmap_ofFinmap

end Finmap

end Entries

end FileTree

end Accordion

end
