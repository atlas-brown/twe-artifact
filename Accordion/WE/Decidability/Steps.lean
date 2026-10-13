module

public import Accordion.WE.Decidability.Defs

@[expose] public section

namespace Accordion.WE.Decidability

variable {Γ : Type} {V : Vars} [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Word]

def pairLetters (A : List Γ) : List Γ :=
  freshList A.toFinset (A.length * A.length)

/-- The letter of the pair `ab` is fresh, at the position of `(a, b)` among the pairs of `A`. -/
def pairName (A : List Γ) (a b : Γ) : Γ :=
  ((pairLetters A)[(A ×ˢ A).idxOf (a, b)]?).getD a

def pops (left : Γ → Bool) (A : List Γ) (x : V.Word) : List (Side Γ V) :=
  ([] :: (A.filter fun b ↦ left b = false).map fun b ↦ [b]).flatMap fun pre ↦
    ([] :: (A.filter fun a ↦ left a = true).map fun a ↦ [a]).flatMap fun post ↦
      [letters (pre ++ post), letters pre ++ .inr x :: letters post]

def replacePairs (left : Γ → Bool) (g : V.Word → Side Γ V) (e : Eqn Γ V) : Eqn Γ V :=
  e.map fun u ↦ mapRuns (compressPairs left (pairName e.letters)) (substSide g u)

def pairComp (L₀ : List Γ) (S : List Γ) (e : Eqn Γ V) : Guess (Eqn Γ V) := do
  let left := fun c ↦ decide (c ∈ S)
  let g ← assignments (pops left e.letters) (fun x ↦ [.inr x]) e.vars
  pure ((replacePairs left g e).renumber L₀)

inductive PrefSuff (Γ : Type) where
  | empty
  | oneBlock (a : Γ)
  | twoBlocks (a b : Γ)
  | cut (a b : Γ)
  deriving DecidableEq

def prefSuffs (A : List Γ) : List (PrefSuff Γ) :=
  .empty :: A.map .oneBlock ++ A.flatMap fun a ↦ A.flatMap fun b ↦ [.twoBlocks a b, .cut a b]

/-- The variable with index `i` has the unknown lengths `2 * i` and `2 * i + 1`. -/
def prefSuffSyms (i : Nat) (x : V.Word) : PrefSuff Γ → List (BlockSym Γ V)
  | .empty => []
  | .oneBlock a => [.block a ⟨1, [2 * i]⟩]
  | .twoBlocks a b => [.block a ⟨1, [2 * i]⟩, .block b ⟨1, [2 * i + 1]⟩]
  | .cut a b => [.block a ⟨1, [2 * i]⟩, .var x, .block b ⟨1, [2 * i + 1]⟩]

def symbolicSide (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (u : Side Γ V) :
    List (BlockSym Γ V) :=
  u.flatMap fun
    | .inl a => [.block a ⟨1, []⟩]
    | .inr x => prefSuffSyms (idx x) x (sh x)

def symbolicSides (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (e : Eqn Γ V) :
    List (BlockSym Γ V) × List (BlockSym Γ V) :=
  (merge (symbolicSide sh idx e.1), merge (symbolicSide sh idx e.2))

def allBlocks (sh : V.Word → PrefSuff Γ) (idx : V.Word → Nat) (e : Eqn Γ V) : List (Γ × Length) :=
  blocks (symbolicSides sh idx e).1 ++ blocks (symbolicSides sh idx e).2

def blockLetters (e : Eqn Γ V) (n : Nat) : List Γ :=
  freshList e.letters.toFinset n

def replaceBlocks (sh : V.Word → PrefSuff Γ) (cls : List Nat) (e : Eqn Γ V) : Eqn Γ V :=
  let B := symbolicSides sh e.vars.idxOf e
  let L := blockLetters e (allBlocks sh e.vars.idxOf e).length
  let name := fun c ↦ (L[c]?).getD (Fresh.fresh e.letters.toFinset)
  (label (cls.map name) B.1, label ((cls.drop (blocks B.1).length).map name) B.2)

def classEquations (cls : List Nat) (B : List (Γ × Length)) : List (Length × Length) :=
  (cls.zip B).flatMap fun p ↦
    (cls.zip B).filterMap fun q ↦ if p.1 = q.1 then some (p.2.2, q.2.2) else none

def lenVars (eqs : List (Length × Length)) : List Nat :=
  (eqs.flatMap fun p ↦ p.1.vars ++ p.2.vars).dedup

def lenSystem (eqs : List (Length × Length)) : LinSystem eqs.length (lenVars eqs).length where
  A r i := ((eqs.get r).1.vars.count (lenVars eqs)[i] : ℤ) -
    ((eqs.get r).2.vars.count (lenVars eqs)[i] : ℤ)
  b r := ((eqs.get r).2.const : ℤ) - (eqs.get r).1.const

def SameLetters (cls : List Nat) (B : List (Γ × Length)) : Prop :=
  ∀ p ∈ cls.zip B, ∀ q ∈ cls.zip B, p.1 = q.1 → p.2.1 = q.2.1

instance (cls : List Nat) (B : List (Γ × Length)) : Decidable (SameLetters cls B) :=
  inferInstanceAs (Decidable (∀ p ∈ cls.zip B, ∀ q ∈ cls.zip B, p.1 = q.1 → p.2.1 = q.2.1))

def wordToDioph (cls : List Nat) (B : List (Γ × Length)) :=
  lenSystem (classEquations cls B)

namespace LinSystem

variable {k m : ℕ}

def verifyDiophantine (A : Fin k → Fin m → ℤ) : ℕ → (Fin k → ℤ) → Guess Bool
  | 0, _ => pure false
  | n + 1, c =>
    if c = 0 then pure true else do
      let β ← bitVectors m
      if ∀ r, 2 ∣ rest A c β r then verifyDiophantine A n (fun r => rest A c β r / 2)
      else pure false

def verify (S : LinSystem k m) : Guess Bool :=
  verifyDiophantine S.A ((2 * S.bound + 1).toNat ^ k + 1) S.b

end LinSystem

/-- A run is rejected unless the guessed classes agree on letters and a guessed solution of their
length equations is verified. -/
def blockComp (L₀ : List Γ) (e : Eqn Γ V) : Guess (Eqn Γ V) := do
  let sh ← assignments (fun _ ↦ prefSuffs e.letters) (fun _ ↦ .empty) e.vars
  let B := allBlocks sh e.vars.idxOf e
  let cls ← vectors B.length B.length
  guard (SameLetters cls B)
  let solved ← (wordToDioph cls B).verify
  guard solved
  pure ((replaceBlocks sh cls e).renumber L₀)

def Eqn.Short (e : Eqn Γ V) : Prop :=
  e.1.length ≤ 1 ∧ e.2.length ≤ 1

instance (e : Eqn Γ V) : Decidable e.Short :=
  inferInstanceAs (Decidable (_ ∧ _))

def naiveValues (A : List Γ) : List (GroundWord Γ) :=
  [] :: A.map fun a ↦ [a]

def naiveSolutions (e : Eqn Γ V) : Guess (Subst Γ V) :=
  assignments (fun _ ↦ naiveValues e.letters) (fun _ ↦ []) e.vars

def phase (L₀ : List Γ) (e : Eqn Γ V) : Guess (Eqn Γ V) := do
  let e₁ ← blockComp L₀ e
  let S₁ ← Guess.sublist e₁.letters.dedup
  let e₂ ← pairComp L₀ S₁ e₁
  let S₂ ← Guess.sublist e₂.letters.dedup
  pairComp L₀ S₂ e₂

/-- A run stops when a phase ends in an equation longer than `bound` or when its fuel runs out. -/
def wordEqSat (L₀ : List Γ) (bound : Nat) : Nat → Eqn Γ V → Guess Bool
  | 0, _ => pure false
  | fuel + 1, e =>
    if e.Short then do
      let g ← naiveSolutions e
      pure (decide (e.Solves g))
    else do
      let e' ← phase L₀ e
      if e'.size ≤ bound then wordEqSat L₀ bound fuel e' else pure false

def Eqn.lengthBound (e : Eqn Γ V) : Nat :=
  79 * e.size

/-- The letters of a run: an equation is renumbered into them after every step. -/
def Eqn.letterList (e : Eqn Γ V) : List Γ :=
  freshList e.letters.toFinset (e.lengthBound + 6 * e.varCount)

def Eqn.phaseBound (e : Eqn Γ V) : Nat :=
  countUpTo (e.letterList.length + e.vars.length) (2 * e.lengthBound) ^ 2 + 2

def eqnSat? (e : Eqn Γ V) : Bool :=
  (wordEqSat e.letterList e.lengthBound e.phaseBound (e.renumber e.letterList)).any id

/-- A guess is a conjunction of at most one literal per equation of the formula; the disjunctive
normal form is never built. -/
def guessConj (φ : Formula Γ V) : Guess (Conj Γ V) :=
  positive φ
where
  positive : Formula Γ V → Guess (Conj Γ V)
    | .top => pure []
    | .bot => failure
    | .atom (.wordEq u v) => pure [(true, u, v)]
    | .conj φ ψ => do
        let c ← positive φ
        let d ← positive ψ
        pure (c ++ d)
    | .disj φ ψ => do
        let left ← guess [true, false]
        if left then positive φ else positive ψ
    | .neg φ => negative φ
  negative : Formula Γ V → Guess (Conj Γ V)
    | .top => failure
    | .bot => pure []
    | .atom (.wordEq u v) => pure [(false, u, v)]
    | .conj φ ψ => do
        let left ← guess [true, false]
        if left then negative φ else negative ψ
    | .disj φ ψ => do
        let c ← negative φ
        let d ← negative ψ
        pure (c ++ d)
    | .neg φ => positive φ

def conjLetters [DecidableEq V.Letter] (c : Conj Γ V) : List Γ :=
  conjConsts c ++
    freshList (conjConsts c).toFinset ((conjLetterVars c).length + 2 * c.length)

/-- How a disequation `u ≠ v` holds: `(0, a, b)` for `u = w a s` and `v = w b t` with `a ≠ b`,
`(1, a, _)` for `u = v a s`, and `(2, a, _)` for `v = u a s`. -/
def disequationCases (A : List Γ) : List (Nat × Γ × Γ) :=
  ((List.range 3).flatMap fun k ↦ A.flatMap fun a ↦ A.map fun b ↦ (k, a, b)).filter
    fun t ↦ t.1 ≠ 0 ∨ t.2.1 ≠ t.2.2

def conjFreshVars [Fresh V.Word] (c : Conj Γ V) : List V.Word :=
  freshList (conjVars c).toFinset (3 * c.length)

/-- The `i`-th literal has the variables `3 * i`, `3 * i + 1` and `3 * i + 2` of `fv`. -/
def literalEquations [Fresh V.Word] (f : V.Letter → Γ) (fv : List V.Word)
    (dg : Nat → Nat × Γ × Γ) (li : Literal Γ V × Nat) : System Γ V :=
  let p := (li.1.2.1.substLetterVars f).flatten
  let q := (li.1.2.2.substLetterVars f).flatten
  let w := (fv[3 * li.2]?).getD (Fresh.fresh ∅)
  let s := (fv[3 * li.2 + 1]?).getD (Fresh.fresh ∅)
  let t := (fv[3 * li.2 + 2]?).getD (Fresh.fresh ∅)
  if li.1.1 then [(p, q)] else
    match dg li.2 with
    | (0, a, b) => [(p, [.inr w, .inl a, .inr s]), (q, [.inr w, .inl b, .inr t])]
    | (1, a, _) => [(p, q ++ [.inl a, .inr s])]
    | (_, a, _) => [(q, p ++ [.inl a, .inr s])]

def conjEquation [Fresh V.Word] (c : Conj Γ V) (f : V.Letter → Γ) (dg : Nat → Nat × Γ × Γ) :
    System Γ V :=
  c.zipIdx.flatMap (literalEquations f (conjFreshVars c) dg)

def conjEquations [DecidableEq V.Letter] [Fresh V.Word] (c : Conj Γ V) : Guess (System Γ V) := do
  let f ← assignments (fun _ ↦ conjLetters c) (fun _ ↦ Fresh.fresh ∅) (conjLetterVars c)
  let dg ← assignments (fun _ ↦ disequationCases (conjLetters c))
    (fun _ ↦ (0, Fresh.fresh ∅, Fresh.fresh ∅)) (List.range c.length)
  pure (conjEquation c f dg)

/-- The equations `uᵢ = vᵢ` as the one equation
`u₁ a ⋯ uₖ a u₁ b ⋯ uₖ b = v₁ a ⋯ vₖ a v₁ b ⋯ vₖ b`, for two fresh letters `a` and `b`. -/
def joinEquations (E : System Γ V) : Eqn Γ V :=
  let A := (E.flatMap Eqn.letters).toFinset
  let a := Fresh.fresh A
  let b := Fresh.fresh (insert a A)
  (E.flatMap (·.1 ++ [.inl a]) ++ E.flatMap (·.1 ++ [.inl b]),
    E.flatMap (·.2 ++ [.inl a]) ++ E.flatMap (·.2 ++ [.inl b]))

def wordEquations [DecidableEq V.Letter] [Fresh V.Word] (φ : Formula Γ V) : Guess (Eqn Γ V) := do
  let c ← guessConj φ
  let E ← conjEquations c
  pure (joinEquations E)

end Accordion.WE.Decidability

end
