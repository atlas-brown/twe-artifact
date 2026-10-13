module

public import Accordion.TWE.Linear.ToWE.Defs

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

namespace ToWE

open scoped Accordion.Formula WE Accordion.Guess BigConnectives

variable {Γ : Type} {V : TWE.Vars}

/-- `P ⋠ Q`: `P` is not a prefix of `Q`. -/
def notPrefixFormula [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (P Q : Word Γ V) :
    FreshM V (WordFormula Γ V) := do
  let A ← freshName
  let B ← freshName
  let K ← freshPath
  let J ← freshPath
  let K' ← freshPath
  return P ≐ Q ++ A ++ K ⋎ P ≐ J ++ A ++ K ⋏ Q ≐ J ++ B ++ K' ⋏ A ≠̇ B

@[inherit_doc] scoped infix:60 " ⋠ " => notPrefixFormula

/-- `P ⊀ Q`: `P` is not a strict prefix of `Q`. -/
def notStrictPrefixFormula [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (P Q : Word Γ V) :
    FreshM V (WordFormula Γ V) := do
  return P ≐ Q ⋎ (← P ⋠ Q)

@[inherit_doc] scoped infix:60 " ⊀ " => notStrictPrefixFormula

/-- `P ∥ Q`: neither word is a prefix of the other. -/
def pathIncomparableFormula [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (P Q : Word Γ V) :
    FreshM V (WordFormula Γ V) := do
  return (← P ⋠ Q) ⋏ (← Q ⋠ P)

@[inherit_doc] scoped infix:60 " ∥ " => pathIncomparableFormula

/-- A formula with a non-linear constant has no linear model, so nothing is guessed for it. -/
def rewriteWalks (φ : TWE.Formula Γ V) : Guess (Conj Γ V) :=
  if φ.hasLinearConstants then positive φ else ⊥
where
  /-- Unlike the paper, a walk also requires `T[ε]` to be a file or a directory. -/
  positive : TWE.Formula Γ V → Guess (Conj Γ V)
    | .top => ⊤
    | .bot => ⊥
    | .conj φ ψ => positive φ ∧ positive ψ
    | .disj φ ψ => positive φ ∨ positive ψ
    | .neg φ => negative φ
    | .atom (.pathEq P Q) => P ≐ Q
    | .atom (.pathIsLin _) => ⊤
    | .atom (.treeWalk P T ℓ) =>
        ⋁ h₀ ∈ [TWE.Shape.file, .dirc], ⋁ h ∈ [TWE.Shape.absent, .file, .dirc],
          P ≐ ℓ ∧ T[ε] ∶ h₀ ∧ T[ℓ] ∶ h
    | .atom (.treeShape T h) => T[ε] ∶ h
    | .atom (.setEq S S') => Atom.tweSet (.eq true S S')
    | .atom (.setMem A S) => Atom.tweSet (.mem true A S)
  /-- The negated walk and shape atoms are not in the paper. -/
  negative : TWE.Formula Γ V → Guess (Conj Γ V)
    | .top => ⊥
    | .bot => ⊤
    | .conj φ ψ => negative φ ∨ negative ψ
    | .disj φ ψ => negative φ ∧ negative ψ
    | .neg φ => positive φ
    | .atom (.pathEq P Q) => P ≠̇ Q
    | .atom (.pathIsLin _) => ⊥
    | .atom (.treeWalk P T ℓ) => P ≠̇ ℓ ∨ T[ε]↑ ∨ T[ε] ∶ .absent ∨ T[ℓ]↑
    | .atom (.treeShape T h) =>
        T[ε]↑ ∨ ⋁ h' ∈ [TWE.Shape.absent, .file, .dirc].filter (· ≠ h), T[ε] ∶ h'
    | .atom (.setEq S S') => Atom.tweSet (.eq false S S')
    | .atom (.setMem A S) => Atom.tweSet (.mem false A S)

/-- A negated atom also holds when some `T` is undefined. -/
def nameEntries [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] :
    Atom Γ V → FreshM V (Guess (Conj Γ V))
  | .tweSet α => do
      let (flat, terms) ← flattenSetAtom α
      let defined : Guess (Conj Γ V) := (⋀ e ∈ terms, e.set ≐ entries(e.tree[ε])) ∧ Atom.set flat
      return if α.positive then defined else defined ∨ ⋁ e ∈ terms, e.tree[ε]↑
  | α => return α

/-- `T[ℓ₁ ↦ T']↓`: the update `T[ℓ₁ ↦ T']` is defined. -/
def updateDefined (T : TWE.Tree V) (ℓ₁ : Word Γ V) (T' : TWE.Tree V) : Guess (Conj Γ V) :=
  ℓ₁ ≐ ε ∧ (⋁ h ∈ [TWE.Shape.file, .dirc], T[ε] ∶ h) ∧
      (⋁ h ∈ [TWE.Shape.file, .dirc], T'[ε] ∶ h) ∨
    ℓ₁ ≠̇ ε ∧ (⋁ h ∈ [TWE.Shape.absent, .file, .dirc], T[ℓ₁] ∶ h) ∧
      (⋁ h ∈ [TWE.Shape.absent, .file, .dirc], T'[ε] ∶ h)

/-- `T[ℓ₁ ↦ T']↑`: the update `T[ℓ₁ ↦ T']` is undefined. -/
def updateUndefined (T : TWE.Tree V) (ℓ₁ : Word Γ V) (T' : TWE.Tree V) : Guess (Conj Γ V) :=
  ℓ₁ ≐ ε ∧ (T[ε]↑ ∨ T[ε] ∶ .absent ∨ T'[ε]↑ ∨ T'[ε] ∶ .absent) ∨
    ℓ₁ ≠̇ ε ∧ (T[ℓ₁]↑ ∨ T'[ε]↑)

@[inherit_doc updateDefined]
scoped syntax:max term:max noWs "[" term " ↦ " term "]" "↓" : term
@[inherit_doc updateUndefined]
scoped syntax:max term:max noWs "[" term " ↦ " term "]" "↑" : term

macro_rules
  | `($T[$ℓ₁ ↦ $T']↓) => `(updateDefined $T $ℓ₁ $T')
macro_rules
  | `($T[$ℓ₁ ↦ $T']↑) => `(updateUndefined $T $ℓ₁ $T')

def updateCase [TWE.Vars.Comparable V] (defined : List (TWE.Tree V)) (u : TWE.Tree V) :
    Guess (Conj Γ V) :=
  match u with
  | .update T ℓ₁ T' => if u ∈ defined then T[ℓ₁ ↦ T']↓ else T[ℓ₁ ↦ T']↑
  | _ => ⊤

def assumeDefined [TWE.Vars.Comparable V] (defined : List (TWE.Tree V)) (α : Atom Γ V) :
    Guess (Conj Γ V) :=
  if α.updates.all (· ∈ defined) then α else if α matches .undefined _ _ then ⊤ else ⊥

/-- Not in the paper, whose rules over updates assume that the update is defined. -/
def caseUpdates [TWE.Vars.Comparable V] (β : Conj Γ V) : FreshM V (Guess (Conj Γ V)) := do
  let updates := (β.flatMap Atom.updates).dedup
  return (Guess.sublist updates).flatMap fun defined =>
    let asserted : Guess (Conj Γ V) := (⋀ α ∈ β, α) ∧ ⋀ u ∈ updates, updateCase defined u
    asserted.flatMap fun γ => ⋀ α ∈ γ, assumeDefined defined α

/-- The cases of the tree constants are not in the paper. -/
def rewriteEntriesAtom [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] :
    Atom Γ V → FreshM V (Guess (Conj Γ V))
  | .entries R T ℓ =>
      match T with
      | .var t => return R ≐ entries(t[ℓ])
      | .file | .abst => return ℓ ≐ ε ∧ R ≐ .empty
      | .emptyDirc => do
          let A ← freshName
          return (ℓ ≐ ε ∨ ℓ ≐ A) ∧ R ≐ .empty
      | .select T ℓ₁ => return R ≐ entries(T[↑ℓ₁ ++ ℓ])
      | .update T ℓ₁ T' => do
          let ℓ₂ ← freshPath
          let inside : Guess (Conj Γ V) := ℓ ≐ ↑ℓ₁ ++ ℓ₂ ∧ R ≐ entries(T'[ℓ₂])
          let A ← freshName
          let A' ← freshName
          let ℓ₃ ← freshPath
          let outside : Guess (Conj Γ V) :=
            ((ℓ₁ : Word Γ V) ≐ ℓ ++ A ++ A' ++ ℓ₃ ∨ ⌜← ℓ ∥ ↑ℓ₁⌝) ∧ R ≐ entries(T[ℓ])
          let B ← freshName
          let R' ← freshSet
          let child : Guess (Conj Γ V) :=
            (ℓ₁ : Word Γ V) ≐ ℓ ++ B ∧ R' ≐ entries(T[ℓ]) ∧
              ((T'[ε] ∶ .file ∨ T'[ε] ∶ .dirc) ∧ R ≐ R' ∪ {B} ∨
                T'[ε] ∶ .absent ∧ B ∉̇ R ∧ R ∪ {B} ≐ R' ∪ {B})
          return inside ∨ outside ∨ child
  | α => return α

/-- The cases of the tree constants and of `T[ℓ]↑` are not in the paper. -/
def rewriteShapeAtom [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] :
    Atom Γ V → FreshM V (Guess (Conj Γ V))
  | .shape T ℓ h =>
      match T with
      | .var t => return t[ℓ] ∶ h
      | .file => return if h = .file then ℓ ≐ ε else ⊥
      | .abst => return if h = .absent then ℓ ≐ ε else ⊥
      | .emptyDirc =>
          match h with
          | .dirc => return ℓ ≐ ε
          | .absent => do
              let A ← freshName
              return ℓ ≐ A
          | .file => return ⊥
      | .select T ℓ₁ => return T[↑ℓ₁ ++ ℓ] ∶ h
      | .update T ℓ₁ T' => do
          let ℓ₂ ← freshPath
          return ℓ ≐ ↑ℓ₁ ++ ℓ₂ ∧ T'[ℓ₂] ∶ h ∨
            ⌜← ↑ℓ₁ ⋠ ℓ⌝ ∧ T[ℓ] ∶ h
  | .undefined T ℓ =>
      match T with
      | .var t => do
          let A ← freshName
          let J ← freshPath
          let K ← freshPath
          return ℓ ≐ J ++ A ++ K ∧ (t[J] ∶ .file ∨ t[J] ∶ .absent)
      | .file | .abst => return ℓ ≠̇ ε
      | .emptyDirc => do
          let A ← freshName
          let B ← freshName
          let K ← freshPath
          return ℓ ≐ A ++ B ++ K
      | .select T ℓ₁ => return T[↑ℓ₁ ++ ℓ]↑
      | .update T ℓ₁ T' => do
          let ℓ₂ ← freshPath
          return ℓ ≐ ↑ℓ₁ ++ ℓ₂ ∧ T'[ℓ₂]↑ ∨
            ⌜← ↑ℓ₁ ⋠ ℓ⌝ ∧ T[ℓ]↑
  | α => return α

def endpointRewrite (e : BaseEntryObservation Γ V) (h : TWE.Shape) : Guess (Conj Γ V) :=
  e.tree[e.query] ∶ h ∧ if h = .dirc then ⊤ else e.set ≐ .empty

def entriesFunctional [TWE.Vars.Comparable V] (entries : List (BaseEntryObservation Γ V)) :
    Guess (Conj Γ V) :=
  ⋀ p ∈ entries ×ˢ entries,
    if p.1.tree = p.2.tree then p.1.query ≠̇ p.2.query ∨ p.1.set ≐ p.2.set else ⊤

def entriesLocationRewrite [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (e : BaseEntryObservation Γ V) (s : BaseShapeAssertion Γ V) :
    FreshM V (Guess (Conj Γ V)) := do
  let ℓ := e.query
  let ℓ' := s.query
  let R := e.set
  let A ← freshName
  let B ← freshName
  let B' ← freshName
  let ℓ'' ← freshPath
  return ℓ' ≐ ℓ ∨ ⌜← ℓ ⋠ ℓ'⌝ ∨
    ℓ' ≐ ℓ ++ A ∧ (if s.shape = .absent then A ∉̇ R else A ∈̇ R) ∨
    ℓ' ≐ ℓ ++ B ++ B' ++ ℓ'' ∧ B ∈̇ R

def entriesLocation [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (p : BaseEntryObservation Γ V × BaseShapeAssertion Γ V) : FreshM V (Guess (Conj Γ V)) :=
  if p.1.tree = p.2.tree then entriesLocationRewrite p.1 p.2 else return ⊤

def entriesCase [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (source : Conj Γ V)
    (hs : List TWE.Shape) : FreshM V (Guess (Conj Γ V)) := do
  let locations ← (caseDirectories source hs ×ˢ caseShapes source hs).mapM entriesLocation
  return (⋀ p ∈ source.baseEntries.zip hs, endpointRewrite p.1 p.2) ∧
    entriesFunctional source.baseEntries ∧ ⋀ D ∈ locations, D

/-- The child case reads the shape of `t[ℓ']` off its assertion, and every case takes its fresh
variables from the same variables in use. -/
def eliminateEntries [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (source : Conj Γ V) :
    FreshM V (Guess (Conj Γ V)) := fun used =>
  ((⋀ α ∈ source.filter (·.baseEntries?.isNone), α) ∧
    (endpointShapes source.baseEntries).flatMap fun hs => ((entriesCase source hs).run used).1,
    used)

def rewriteSetDisequality [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] :
    Atom Γ V → FreshM V (Guess (Conj Γ V))
  | .set (.eq false S₁ S₂) => do
      let A ← freshName
      return A ∈̇ S₁ ∧ A ∉̇ S₂ ∨ A ∉̇ S₁ ∧ A ∈̇ S₂
  | α => return α

def setMembershipFormula (sentinel a : Word Γ V) (S : List (Word Γ V)) : WordFormula Γ V :=
  ⋁ Aᵢ ∈ S, Aᵢ ≠̇ sentinel ⋏ a ≐ Aᵢ

def setSubsetFormula (sentinel : Word Γ V) (S S' : List (Word Γ V)) : WordFormula Γ V :=
  ⋀ Aᵢ ∈ S, Aᵢ ≐ sentinel ⋎ setMembershipFormula sentinel Aᵢ S'

def setAtomEncodingFormula (sentinel : Word Γ V) (A : V.Set → Nat → Word Γ V)
    (width : Nat) : SetAtom Γ V → WordFormula Γ V
  | .eq positive S S' =>
      if positive then
        setSubsetFormula sentinel (S.encodingWords A width) (S'.encodingWords A width) ⋏
          setSubsetFormula sentinel (S'.encodingWords A width) (S.encodingWords A width)
      else
        ∼(setSubsetFormula sentinel (S.encodingWords A width) (S'.encodingWords A width) ⋏
          setSubsetFormula sentinel (S'.encodingWords A width) (S.encodingWords A width))
  | .mem positive a S =>
      if positive then setMembershipFormula sentinel a.toWord (S.encodingWords A width)
      else ⋀ Aᵢ ∈ S.encodingWords A width, Aᵢ ≐ sentinel ⋎ a.toWord ≠̇ Aᵢ

def setEncodingFormula (sentinel : Word Γ V) (A : V.Set → Nat → Word Γ V)
    (atoms : List (SetAtom Γ V)) : WordFormula Γ V :=
  (⋀ a ∈ atoms.flatMap SetAtom.names, sentinel ≠̇ a.toWord) ⋏
    ((⋀ x ∈ atoms.flatMap SetAtom.variables, ⋀ j ∈ List.range (setWordBound atoms),
        ⋀ i ∈ List.range j, A x i ≐ sentinel ⋎ (A x j ≐ sentinel ⋎ A x i ≠̇ A x j)) ⋏
      ⋀ α ∈ atoms, setAtomEncodingFormula sentinel A (setWordBound atoms) α)

/-- `setWordBound` counts the name occurrences in the set atoms, which bounds the number of
names. -/
def encodeSets [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (β : Conj Γ V) :
    FreshM V (Guess (Conj Γ V)) := do
  let sentinel : Word Γ V := (← freshName)
  let names ← freshSequences (β.sets.flatMap SetAtom.variables) (setWordBound β.sets)
  return (⋀ α ∈ β.filter (·.set?.isNone), α) ∧
    ⌜setEncodingFormula sentinel (fun x i => (names x i : Word Γ V)) β.sets⌝

def leafPairFormula [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (p : BaseShapeAssertion Γ V × BaseShapeAssertion Γ V) : FreshM V (WordFormula Γ V) :=
  if p.1.tree = p.2.tree ∧ p.1.shape ≠ .dirc then p.1.query ⊀ p.2.query else return ⊤

/-- Replaces the base shape assertions of each tree variable by word formulas: equal locations have
equal shapes, and a file or absent location is not a strict prefix of another. -/
def reifyShapes [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (source : Conj Γ V) :
    FreshM V (WordFormula Γ V) := do
  let pairs := source.baseShapes ×ˢ source.baseShapes
  let leaves ← pairs.mapM leafPairFormula
  return (⋀ F ∈ source.words, F) ⋏
    ((⋀ p ∈ pairs,
        if p.1.tree = p.2.tree ∧ p.1.shape ≠ p.2.shape then p.1.query ≠̇ p.2.query else ⊤) ⋏
      ⋀ F ∈ leaves, F)

end ToWE

end Linear

end TWE

end Accordion

end
