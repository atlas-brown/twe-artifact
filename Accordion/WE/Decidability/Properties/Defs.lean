module

public import Accordion.WE.Decidability.Steps
public import Accordion.Guess.Properties

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars}

def Eqn.letterCount (e : Eqn Γ V) : Nat :=
  e.letters.length

def expandSide (h : Γ → GroundWord Γ) (u : Side Γ V) : Side Γ V :=
  u.flatMap fun
    | .inl a => letters (h a)
    | .inr x => [.inr x]

def consRun [DecidableEq Γ] (a : Γ) : List (Γ × Nat) → List (Γ × Nat)
  | (b, k) :: r => if a = b then (a, k + 1) :: r else (a, 1) :: (b, k) :: r
  | [] => [(a, 1)]

def runs [DecidableEq Γ] (w : GroundWord Γ) : List (Γ × Nat) :=
  w.foldr consRun []

def compressBlocks [DecidableEq Γ] (name : Γ → Nat → Γ) (w : GroundWord Γ) : GroundWord Γ :=
  (runs w).map fun p ↦ name p.1 p.2

def adj (w : GroundWord Γ) : List (Γ × Γ) :=
  w.zip w.tail

def adjSide : Side Γ V → List (Γ × Γ)
  | [] => []
  | .inr _ :: u => adjSide u
  | [.inl _] => []
  | .inl _ :: .inr x :: u => adjSide (.inr x :: u)
  | .inl a :: .inl b :: u => (a, b) :: adjSide (.inl b :: u)

def pairCount (left : Γ → Bool) (w : GroundWord Γ) : Nat :=
  (adj w).countP fun p ↦ IsPair left p.1 p.2

def Eqn.adj (e : Eqn Γ V) : List (Γ × Γ) :=
  adjSide e.1 ++ adjSide e.2

def Eqn.NoSquare (e : Eqn Γ V) : Prop :=
  ∀ p ∈ e.adj, p.1 ≠ p.2

def Eqn.pairs (left : Γ → Bool) (e : Eqn Γ V) : Nat :=
  e.adj.countP fun p ↦ IsPair left p.1 p.2

def instantiate (ℓ : Nat → Nat) (M : List (BlockSym Γ V)) : Side Γ V :=
  M.flatMap fun
    | .block a E => letters (List.replicate (E.eval ℓ) a)
    | .var x => [.inr x]

namespace LinSystem

variable {k m : ℕ}

def halve (A : Fin k → Fin m → ℤ) (c : Fin k → ℤ) : Finset (Fin k → ℤ) :=
  ((Finset.univ : Finset (Fin m → Bool)).filter fun β => ∀ r, 2 ∣ rest A c β r).image
    fun β r => rest A c β r / 2

def states (S : LinSystem k m) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-S.bound) S.bound

end LinSystem

def listsUpTo {α : Type} (syms : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => [] :: syms.flatMap fun s ↦ (listsUpTo syms k).map (s :: ·)

def boundedEqns [DecidableEq Γ] [DecidableEq V.Word] (L₀ : List Γ) (K : Nat) (X : List V.Word) :
    Finset (Eqn Γ V) :=
  (listsUpTo (L₀.map .inl ++ X.map .inr : Side Γ V) K).toFinset ×ˢ
    (listsUpTo (L₀.map .inl ++ X.map .inr : Side Γ V) K).toFinset

def reachWithin {α : Type*} [DecidableEq α] (next : α → Finset α) (s : Finset α) : ℕ → Finset α
  | 0 => s
  | k + 1 =>
    let t := reachWithin next s k
    t ∪ t.biUnion next

def ReachIn {α : Type*} (next : α → Finset α) : ℕ → α → α → Prop
  | 0, a, b => a = b
  | k + 1, a, b => a = b ∨ ∃ c ∈ next a, ReachIn next k c b

def PairPop (left : Γ → Bool) (A : List Γ) (x : V.Word) (s : Side Γ V) : Prop :=
  ∃ pre post : List Γ, (pre = [] ∨ ∃ b ∈ A, left b = false ∧ pre = [b]) ∧
    (post = [] ∨ ∃ a ∈ A, left a = true ∧ post = [a]) ∧
    (s = letters (pre ++ post) ∨ s = letters pre ++ .inr x :: letters post)

def popFirst (left : Γ → Bool) : List Γ → List Γ × List Γ
  | b :: w => if left b = false then ([b], w) else ([], b :: w)
  | [] => ([], [])

def popLast (left : Γ → Bool) (w : List Γ) : List Γ × List Γ :=
  match w.getLast? with
  | some a => if left a = true then (w.dropLast, [a]) else (w, [])
  | none => (w, [])

def pairMid (left : Γ → Bool) (w : List Γ) : List Γ :=
  (popLast left (popFirst left w).2).1

def pairPopWord (left : Γ → Bool) (x : V.Word) (w : List Γ) : Side Γ V :=
  let pre := (popFirst left w).1
  let post := (popLast left (popFirst left w).2).2
  if pairMid left w = [] then letters (pre ++ post) else letters pre ++ .inr x :: letters post

def pairPopOf (left : Γ → Bool) (σ : Subst Γ V) (x : V.Word) : Side Γ V :=
  pairPopWord left x (σ x)

def Merged (M : List (BlockSym Γ V)) : Prop :=
  M.IsChain fun i j ↦ ∀ a E b F, i = .block a E → j = .block b F → a ≠ b

def Positive (M : List (BlockSym Γ V)) : Prop :=
  ∀ a E, BlockSym.block a E ∈ M → 0 < E.const

def itemVars (M : List (BlockSym Γ V)) : List V.Word :=
  M.filterMap fun
    | .block _ _ => none
    | .var x => some x

def Consistent (cls : List Nat) (B : List (Γ × Length)) (ℓ : Nat → Nat) : Prop :=
  ∀ p ∈ cls.zip B, ∀ q ∈ cls.zip B, p.1 = q.1 → p.2.1 = q.2.1 ∧ p.2.2.eval ℓ = q.2.2.eval ℓ

def classExpand [DecidableEq Γ] (name : Nat → Γ) (cls : List Nat) (B : List (Γ × Length))
    (ℓ : Nat → Nat) (c : Γ) : GroundWord Γ :=
  match (cls.zip B).find? (fun p ↦ name p.1 == c) with
  | some p => List.replicate (p.2.2.eval ℓ) p.2.1
  | none => [c]

def splitBlock [DecidableEq Γ] (a : Γ) : GroundWord Γ → Nat × GroundWord Γ
  | b :: w => if b = a then ((splitBlock a w).1 + 1, (splitBlock a w).2) else (0, b :: w)
  | [] => (0, [])

/-- A word as `aᵖ · mid · b^q` with maximal blocks; `rest` is `mid · b^q`. -/
structure Pieces (Γ : Type) where
  a : Γ
  p : Nat
  b : Γ
  q : Nat
  rest : GroundWord Γ
  mid : GroundWord Γ

def pieces [DecidableEq Γ] [Fresh Γ] (w : GroundWord Γ) : Pieces Γ :=
  let a := w.headD (Fresh.fresh ∅)
  let rest := (splitBlock a w).2
  let b := rest.getLastD (Fresh.fresh ∅)
  ⟨a, (splitBlock a w).1, b, (splitBlock b rest.reverse).1, rest,
    (splitBlock b rest.reverse).2.reverse⟩

/-- For the `i`-th variable `x`, the unknown `2 * i` is one less than the length of the front block
of `σ x` and `2 * i + 1` one less than that of its back block. -/
def lengthsOf [DecidableEq Γ] [Fresh Γ] (σ : Subst Γ V) (e : Eqn Γ V) (v : Nat) : Nat :=
  match e.vars[v / 2]? with
  | some x => if v % 2 = 0 then (pieces (σ x)).p - 1 else (pieces (σ x)).q - 1
  | none => 0

def blockMid [DecidableEq Γ] [Fresh Γ] (σ : Subst Γ V) (x : V.Word) : GroundWord Γ :=
  (pieces (σ x)).mid

def LenSolvable (eqs : List (Length × Length)) : Prop :=
  ∃ ℓ : Nat → Nat, ∀ p ∈ eqs, p.1.eval ℓ = p.2.eval ℓ

def extend (U : List Nat) (v : Fin U.length → Nat) (x : Nat) : Nat :=
  if h : U.idxOf x < U.length then v ⟨U.idxOf x, h⟩ else 0

def sepBy (a : Γ) (us : List (GroundWord Γ)) : GroundWord Γ :=
  us.flatMap (· ++ [a])

variable [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word]

/-- A pair letter is decoded by its position among the pair letters. -/
def pairExpand (A : List Γ) (c : Γ) : List Γ :=
  if c ∈ pairLetters A then
    ((A ×ˢ A)[(pairLetters A).idxOf c]?).elim [c] fun p ↦ [p.1, p.2]
  else [c]

def prefSuffOf (w : GroundWord Γ) : PrefSuff Γ :=
  if w = [] then .empty
  else if (pieces w).rest = [] then .oneBlock (pieces w).a
  else if (pieces w).mid = [] then .twoBlocks (pieces w).a (pieces w).b
  else .cut (pieces w).a (pieces w).b

def prefSuffsOf (σ : Subst Γ V) (x : V.Word) : PrefSuff Γ :=
  prefSuffOf (σ x)

def blockLetter (e : Eqn Γ V) (n c : Nat) : Γ :=
  ((blockLetters e n)[c]?).getD (Fresh.fresh e.letters.toFinset)

def blockValues (σ : Subst Γ V) (e : Eqn Γ V) : List (Γ × Nat) :=
  (allBlocks (prefSuffsOf σ) e.vars.idxOf e).map fun p ↦ (p.1, p.2.eval (lengthsOf σ e))

/-- The class of a block of letter `a` and length `k`: the first block with the same value. -/
def blockClass (σ : Subst Γ V) (e : Eqn Γ V) (a : Γ) (k : Nat) : Nat :=
  (blockValues σ e).idxOf (a, k)

def blockName (σ : Subst Γ V) (e : Eqn Γ V) (a : Γ) (k : Nat) : Γ :=
  blockLetter e (allBlocks (prefSuffsOf σ) e.vars.idxOf e).length (blockClass σ e a k)

def classesOf (σ : Subst Γ V) (e : Eqn Γ V) : List Nat :=
  (allBlocks (prefSuffsOf σ) e.vars.idxOf e).map fun p ↦
    blockClass σ e p.1 (p.2.eval (lengthsOf σ e))

def SolvedNaively (e : Eqn Γ V) : Prop :=
  ∃ g ∈ naiveSolutions e, e.Solves g

def PhaseStep (L₀ : List Γ) (B : Nat) (e f : Eqn Γ V) : Prop :=
  f ∈ phase L₀ e ∧ ¬e.Short ∧ f.size ≤ B

end Accordion.WE.Decidability

end
