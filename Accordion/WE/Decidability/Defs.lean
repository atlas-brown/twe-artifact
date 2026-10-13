module

public import Accordion.WE
public import Accordion.Guess
public import Accordion.Fresh
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace Accordion.WE

variable {Γ : Type} {V : Vars}

def Word.substLetterVars (f : V.Letter → Γ) : Word Γ V → Word Γ V
  | .empty => .empty
  | .letter a => .letter a
  | .letterVar x => .letter (f x)
  | .var x => .var x
  | .concat u v => .concat (u.substLetterVars f) (v.substLetterVars f)

namespace Decidability

abbrev Sym (Γ : Type) (V : Vars) := Γ ⊕ V.Word
abbrev Side (Γ : Type) (V : Vars) := List (Sym Γ V)
abbrev Eqn (Γ : Type) (V : Vars) := Side Γ V × Side Γ V
abbrev System (Γ : Type) (V : Vars) := List (Eqn Γ V)
abbrev Subst (Γ : Type) (V : Vars) := V.Word → GroundWord Γ

def Sym.eval (σ : Subst Γ V) : Sym Γ V → GroundWord Γ
  | .inl a => [a]
  | .inr x => σ x

def eval (σ : Subst Γ V) (u : Side Γ V) : GroundWord Γ :=
  u.flatMap (Sym.eval σ)

def letters (w : GroundWord Γ) : Side Γ V :=
  w.map .inl

def Eqn.Solves (σ : Subst Γ V) (e : Eqn Γ V) : Prop :=
  eval σ e.1 = eval σ e.2

instance [DecidableEq Γ] (σ : Subst Γ V) (e : Eqn Γ V) : Decidable (e.Solves σ) :=
  inferInstanceAs (Decidable (_ = _))

def Eqn.Solvable (e : Eqn Γ V) : Prop :=
  ∃ σ, e.Solves σ

def System.Solvable (E : System Γ V) : Prop :=
  ∃ σ, ∀ e ∈ E, e.Solves σ

end Decidability

/-- Letter variables are substituted away before flattening, so `letterVar` is unreachable. -/
def Word.flatten : Word Γ V → Decidability.Side Γ V
  | .empty => []
  | .letter a => [.inl a]
  | .letterVar _ => []
  | .var x => [.inr x]
  | .concat u v => u.flatten ++ v.flatten

namespace Decidability

def freshList {α : Type} [DecidableEq α] [Fresh α] (s : Finset α) : Nat → List α
  | 0 => []
  | n + 1 => Fresh.fresh s :: freshList (insert (Fresh.fresh s) s) n

def sideLetters (u : Side Γ V) : List Γ :=
  u.filterMap Sum.getLeft?

def sideVars (u : Side Γ V) : List V.Word :=
  u.filterMap Sum.getRight?

def Eqn.size (e : Eqn Γ V) : Nat :=
  e.1.length + e.2.length

def Eqn.map (f : Side Γ V → Side Γ V) (e : Eqn Γ V) : Eqn Γ V :=
  (f e.1, f e.2)

def Eqn.letters (e : Eqn Γ V) : List Γ :=
  sideLetters e.1 ++ sideLetters e.2

def Eqn.vars (e : Eqn Γ V) : List V.Word :=
  sideVars e.1 ++ sideVars e.2

def Eqn.varCount (e : Eqn Γ V) : Nat :=
  e.vars.length

def substSide (g : V.Word → Side Γ V) (u : Side Γ V) : Side Γ V :=
  u.flatMap fun
    | .inl a => [.inl a]
    | .inr x => g x

def IsPair (left : Γ → Bool) (a b : Γ) : Prop :=
  left a = true ∧ left b = false

instance (left : Γ → Bool) (a b : Γ) : Decidable (IsPair left a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def compressPairs (left : Γ → Bool) (name : Γ → Γ → Γ) : GroundWord Γ → GroundWord Γ
  | a :: b :: w =>
      if IsPair left a b then name a b :: compressPairs left name w
      else a :: compressPairs left name (b :: w)
  | w => w

def mapRunsFrom (f : GroundWord Γ → GroundWord Γ) (q : GroundWord Γ) : Side Γ V → Side Γ V
  | [] => letters (f q)
  | .inl a :: u => mapRunsFrom f (q ++ [a]) u
  | .inr x :: u => letters (f q) ++ .inr x :: mapRunsFrom f [] u

def mapRuns (f : GroundWord Γ → GroundWord Γ) (u : Side Γ V) : Side Γ V :=
  mapRunsFrom f [] u

structure Length where
  const : Nat
  vars : List Nat
  deriving DecidableEq, Repr

namespace Length

def eval (ℓ : Nat → Nat) (E : Length) : Nat :=
  E.const + (E.vars.map ℓ).sum

instance : Add Length :=
  ⟨fun E F ↦ ⟨E.const + F.const, E.vars ++ F.vars⟩⟩

end Length

inductive BlockSym (Γ : Type) (V : Vars) where
  | block (a : Γ) (E : Length)
  | var (x : V.Word)

instance [DecidableEq Γ] [DecidableEq V.Word] : DecidableEq (BlockSym Γ V)
  | .block a E, .block b F => decidable_of_iff (a = b ∧ E = F) (by simp)
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .block .., .var _ => isFalse (by simp)
  | .var _, .block .. => isFalse (by simp)

def blocks (M : List (BlockSym Γ V)) : List (Γ × Length) :=
  M.filterMap fun
    | .block a E => some (a, E)
    | .var _ => none

def consBlockSym [DecidableEq Γ] : BlockSym Γ V → List (BlockSym Γ V) → List (BlockSym Γ V)
  | .block a E, .block b F :: M =>
      if a = b then .block a (E + F) :: M else .block a E :: .block b F :: M
  | i, M => i :: M

def merge [DecidableEq Γ] (M : List (BlockSym Γ V)) : List (BlockSym Γ V) :=
  M.foldr consBlockSym []

/-- A block beyond the end of `cls` keeps its own letter. -/
def label : List Γ → List (BlockSym Γ V) → Side Γ V
  | _, [] => []
  | cls, .var x :: M => .inr x :: label cls M
  | c :: cls, .block _ _ :: M => .inl c :: label cls M
  | [], .block a _ :: M => .inl a :: label [] M

structure LinSystem (k m : ℕ) where
  A : Fin k → Fin m → ℤ
  b : Fin k → ℤ

namespace LinSystem

variable {k m : ℕ}

def Solves (S : LinSystem k m) (v : Fin m → ℕ) : Prop :=
  ∀ r, ∑ i, S.A r i * v i = S.b r

def Solvable (S : LinSystem k m) : Prop :=
  ∃ v, S.Solves v

def rest (A : Fin k → Fin m → ℤ) (c : Fin k → ℤ) (β : Fin m → Bool) (r : Fin k) : ℤ :=
  c r - ∑ i, A r i * (β i).toNat

def bound (S : LinSystem k m) : ℤ :=
  ∑ r, (|S.b r| + ∑ i, |S.A r i|)

end LinSystem

def renameSide (ρ : Γ → Γ) (u : Side Γ V) : Side Γ V :=
  u.map fun
    | .inl a => .inl (ρ a)
    | .inr x => .inr x

def Eqn.rename (ρ : Γ → Γ) (e : Eqn Γ V) : Eqn Γ V :=
  e.map (renameSide ρ)

def Eqn.letterIndex [DecidableEq Γ] (e : Eqn Γ V) (a : Γ) : Nat :=
  e.letters.dedup.idxOf a

/-- The renaming is injective only when `L₀` has at least as many distinct letters as `e`. -/
def Eqn.renumber [DecidableEq Γ] (L₀ : List Γ) (e : Eqn Γ V) : Eqn Γ V :=
  e.rename fun a ↦ (L₀[e.letterIndex a]?).getD a

/-- A function with a value guessed from `opts x` at every `x` of the list, and `d` elsewhere. -/
def assignments {α β : Type} [DecidableEq α] (opts : α → List β) (d : α → β) :
    List α → Guess (α → β)
  | [] => pure d
  | x :: xs => do
    let b ← guess (opts x)
    let g ← assignments opts d xs
    pure (Function.update g x b)

def vectors (n : Nat) : Nat → Guess (List Nat)
  | 0 => pure []
  | k + 1 => do
    let c ← guess (List.range n)
    let v ← vectors n k
    pure (c :: v)

def countUpTo (s : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + s * countUpTo s k

def bitVectors (m : Nat) : Guess (Fin m → Bool) :=
  assignments (fun _ ↦ [false, true]) (fun _ ↦ false) (List.finRange m)

/-- An equation `u = v` (`true`) or a disequation `u ≠ v` (`false`). -/
abbrev Literal (Γ : Type) (V : Vars) := Bool × Word Γ V × Word Γ V

def Literal.Holds (m : Model Γ V) (l : Literal Γ V) : Prop :=
  if l.1 then m.evalWord l.2.1 = m.evalWord l.2.2 else m.evalWord l.2.1 ≠ m.evalWord l.2.2

abbrev Conj (Γ : Type) (V : Vars) := List (Literal Γ V)

def Conj.SAT (c : Conj Γ V) : Prop :=
  ∃ m : Model Γ V, ∀ l ∈ c, l.Holds m

def wordConsts : Word Γ V → List Γ
  | .empty | .letterVar _ | .var _ => []
  | .letter a => [a]
  | .concat u v => wordConsts u ++ wordConsts v

def conjConsts [DecidableEq Γ] (c : Conj Γ V) : List Γ :=
  (c.flatMap fun l ↦ wordConsts l.2.1 ++ wordConsts l.2.2).dedup

def conjLetterVars [DecidableEq V.Letter] (c : Conj Γ V) : List V.Letter :=
  (c.flatMap fun l ↦ l.2.1.letterVars ++ l.2.2.letterVars).dedup

def conjVars [DecidableEq V.Word] (c : Conj Γ V) : List V.Word :=
  (c.flatMap fun l ↦ l.2.1.vars ++ l.2.2.vars).dedup

end Decidability

end Accordion.WE

end
