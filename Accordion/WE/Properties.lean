module

public import Accordion.WE

@[expose] public section

namespace Accordion

variable {Γ : Type}

namespace WE

@[simp] theorem Word.append_eq {V : Vars} (u v : Word Γ V) : u ++ v = .concat u v := rfl

namespace Model

variable {V : Vars} (M : Model Γ V)

@[simp] theorem sat_wordEq_iff (u v : Word Γ V) :
    Sat.sat M (Atom.wordEq u v) ↔ M.evalWord u = M.evalWord v := Iff.rfl

@[simp] theorem evalWord_concat (u v : Word Γ V) :
    M.evalWord (.concat u v) = M.evalWord u ++ M.evalWord v := rfl

theorem evalWord_append (u v : Word Γ V) :
    M.evalWord (u ++ v) = M.evalWord u ++ M.evalWord v := rfl

end Model

namespace GroundWord

theorem not_prefix_iff_exists (p q : GroundWord Γ) :
    ¬p <+: q ↔
      (∃ a k, p = q ++ a :: k) ∨
      ∃ j a k b k', p = j ++ a :: k ∧ q = j ++ b :: k' ∧ a ≠ b := by
  induction p generalizing q with
  | nil => simp [List.IsPrefix]
  | cons a p ih =>
      rcases q with _ | ⟨b, q⟩
      · simp
      by_cases hab : a = b
      · subst b
        rw [List.prefix_cons_inj, ih q]
        constructor
        · rintro (⟨c, k, rfl⟩ | ⟨j, c, k, d, k', rfl, rfl, hcd⟩)
          · exact Or.inl ⟨c, k, rfl⟩
          · exact Or.inr ⟨a :: j, c, k, d, k', rfl, rfl, hcd⟩
        · rintro (⟨c, k, hp⟩ | ⟨_ | ⟨e, j⟩, c, k, d, k', hp, hq, hcd⟩)
          · exact Or.inl ⟨c, k, (List.cons.inj hp).2⟩
          · exact absurd ((List.cons.inj hp).1.symm.trans (List.cons.inj hq).1) hcd
          · exact Or.inr ⟨j, c, k, d, k', (List.cons.inj hp).2, (List.cons.inj hq).2, hcd⟩
      · exact ⟨fun _ => Or.inr ⟨[], a, p, b, q, rfl, rfl, hab⟩,
          fun _ hpref => hab (List.cons_prefix_cons.mp hpref).1⟩

end GroundWord

end WE

end Accordion

end
