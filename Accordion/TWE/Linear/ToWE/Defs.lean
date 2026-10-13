module

public import Accordion.TWE.Linear.ToWE.Intermediate
public import Accordion.TWE.Fresh

@[expose] public section

namespace Accordion

namespace TWE

open Linear.ToWE (Word)

variable {Γ : Type} {V : TWE.Vars}

def Path.hasLinearConstants : TWE.Path Γ V → Bool
  | .init .empty | .init .self | .init .parent => false
  | .join p q => p.hasLinearConstants && q.hasLinearConstants
  | .norm p => p.hasLinearConstants
  | .nil | .init (.name _) | .init (.var _) | .loc _ | .var _ => true

def Formula.hasLinearConstants (φ : TWE.Formula Γ V) : Bool :=
  φ.paths.all Path.hasLinearConstants

def Tree.size {V : TWE.TreeVars} : TWE.Tree V → Nat
  | .var _ => 0
  | .file | .emptyDirc | .abst => 1
  | .select T _ => T.size + 1
  | .update T _ T' => T.size + T'.size + 1

def Name.toWord : TWE.Name Γ V → Word Γ V
  | .name a => .letter a
  | .var x => .letterVar (.inl x)

/-- A non-linear component occurs in no formula with a linear model; its word is empty. -/
def Component.toWord : TWE.Component Γ V → Word Γ V
  | .name a => a.toWord
  | .var x => .letterVar (.inr x)
  | .empty | .self | .parent => .empty

def Path.toWord : TWE.Path Γ V → Word Γ V
  | .nil => .empty
  | .init b => b.toWord
  | .join p q => p.toWord ++ q.toWord
  | .loc l => .var (.inr l)
  | .var x => .var (.inl x)
  | .norm p => p.toWord

namespace Linear

namespace ToWE

variable {ρ : Type}

scoped instance : Coe (TWE.Path Γ V) (Word Γ V) := ⟨TWE.Path.toWord⟩
scoped instance : Coe V.Loc (Word Γ V) := ⟨fun l => TWE.Path.toWord (.loc l)⟩
scoped instance : Coe V.Path (Word Γ V) := ⟨fun x => TWE.Path.toWord (.var x)⟩
scoped instance : Coe (TWE.Name Γ V) (Word Γ V) := ⟨TWE.Name.toWord⟩
scoped instance : Coe V.Name (Word Γ V) := ⟨fun x => TWE.Name.toWord (.var x)⟩

scoped notation:60 u:61 " ≠̇ " v:61 =>
  Accordion.Formula.neg (Accordion.Formula.atom (WE.Atom.wordEq u v))

/-- Conjunctions and disjunctions of lists, shared by word formulas and guesses of conjunctions. -/
class BigConnectives (ρ : Type) where
  bigConj : List ρ → ρ
  bigDisj : List ρ → ρ

instance {A : Type} : BigConnectives (Accordion.Formula A) :=
  ⟨Accordion.Formula.bigConj, Accordion.Formula.bigDisj⟩

instance : BigConnectives (Guess (Conj Γ V)) := ⟨Guess.bigConj, Guess.bigDisj⟩

namespace BigConnectives

def all {ρ ι : Type} [BigConnectives ρ] (xs : List ι) (F : ι → ρ) : ρ :=
  bigConj (xs.map F)

def any {ρ ι : Type} [BigConnectives ρ] (xs : List ι) (F : ι → ρ) : ρ :=
  bigDisj (xs.map F)

scoped syntax "⋀ " ident " ∈ " term ", " term : term
scoped syntax "⋁ " ident " ∈ " term ", " term : term
macro_rules
  | `(⋀ $x ∈ $xs, $F) => `(BigConnectives.all $xs fun $x => $F)
macro_rules
  | `(⋁ $x ∈ $xs, $F) => `(BigConnectives.any $xs fun $x => $F)

end BigConnectives

structure BaseShapeAssertion (Γ : Type) (V : TWE.Vars) where
  tree : V.Tree
  query : Word Γ V
  shape : TWE.Shape

structure BaseEntryObservation (Γ : Type) (V : TWE.Vars) where
  tree : V.Tree
  query : Word Γ V
  set : V.Set

def BaseShapeAssertion.atom (s : BaseShapeAssertion Γ V) : Atom Γ V :=
  .shape (.var s.tree) s.query s.shape

def BaseEntryObservation.atom (e : BaseEntryObservation Γ V) : Atom Γ V :=
  .entries e.set (.var e.tree) e.query

def Atom.word? : Atom Γ V → Option (WordFormula Γ V)
  | .word F => some F
  | _ => none

def Atom.baseShape? : Atom Γ V → Option (BaseShapeAssertion Γ V)
  | .shape (.var t) ℓ h => some ⟨t, ℓ, h⟩
  | _ => none

def Atom.baseEntries? : Atom Γ V → Option (BaseEntryObservation Γ V)
  | .entries R (.var t) ℓ => some ⟨t, ℓ, R⟩
  | _ => none

def Atom.set? : Atom Γ V → Option (SetAtom Γ V)
  | .set α => some α
  | _ => none

def Conj.words (β : Conj Γ V) : List (WordFormula Γ V) := β.filterMap Atom.word?

def Conj.baseShapes (β : Conj Γ V) : List (BaseShapeAssertion Γ V) := β.filterMap Atom.baseShape?

def Conj.baseEntries (β : Conj Γ V) : List (BaseEntryObservation Γ V) :=
  β.filterMap Atom.baseEntries?

def Conj.sets (β : Conj Γ V) : List (SetAtom Γ V) := β.filterMap Atom.set?

def SetAtom.isDisequality : SetAtom Γ V → Bool
  | .eq false _ _ => true
  | _ => false

def SetTerm.names : SetTerm Γ V → List (TWE.Name Γ V)
  | .var _ | .empty => []
  | .insert A S => A :: S.names

def SetTerm.variables : SetTerm Γ V → List V.Set
  | .var x => [x]
  | .empty => []
  | .insert _ S => S.variables

def SetAtom.names : SetAtom Γ V → List (TWE.Name Γ V)
  | .eq _ S S' => S.names ++ S'.names
  | .mem _ A S => A :: S.names

def SetAtom.variables : SetAtom Γ V → List V.Set
  | .eq _ S S' => S.variables ++ S'.variables
  | .mem _ _ S => S.variables

structure EntriesTerm (V : TWE.Vars) where
  set : V.Set
  tree : TWE.Tree V

def endpointShapes : List (BaseEntryObservation Γ V) → Guess (List TWE.Shape)
  | [] => pure []
  | _ :: es => do
      let h ← guess [TWE.Shape.file, .absent, .dirc]
      let hs ← endpointShapes es
      pure (h :: hs)

def caseShapes (source : Conj Γ V) (hs : List TWE.Shape) : List (BaseShapeAssertion Γ V) :=
  source.baseShapes ++ (source.baseEntries.zip hs).map fun (e, h) => ⟨e.tree, e.query, h⟩

def caseDirectories (source : Conj Γ V) (hs : List TWE.Shape) : List (BaseEntryObservation Γ V) :=
  ((source.baseEntries.zip hs).filter (·.2 = .dirc)).map (·.1)

def setWordBound (atoms : List (SetAtom Γ V)) : Nat :=
  (atoms.flatMap SetAtom.names).length + (atoms.filter SetAtom.isDisequality).length

def SetTerm.encodingWords (A : V.Set → Nat → Word Γ V) (width : Nat) (S : SetTerm Γ V) :
    List (Word Γ V) :=
  S.names.map TWE.Name.toWord ++ S.variables.flatMap fun x => (List.range width).map (A x)

def Atom.treeSize : Atom Γ V → Nat
  | .shape T _ _ | .undefined T _ | .entries _ T _ => T.size
  | _ => 0

/-- This many passes of `rewriteAtoms` suffice for every atom rule, since a rule over updates
rewrites an atom about a tree into atoms about its subtrees. -/
def Conj.passes (β : Conj Γ V) : Nat :=
  (β.map fun α => 2 * α.treeSize + 1).sum

variable [TWE.Vars.Comparable V]

def Word.free : Word Γ V → TWE.Free V
  | .empty | .letter _ => ∅
  | .letterVar (.inl x) => { (∅ : TWE.Free V) with name := {x} }
  | .letterVar (.inr x) => { (∅ : TWE.Free V) with comp := {x} }
  | .var (.inl x) => { (∅ : TWE.Free V) with path := {x} }
  | .var (.inr l) => { (∅ : TWE.Free V) with loc := {l} }
  | .concat u v => Word.free u ∪ Word.free v

def WordFormula.free : WordFormula Γ V → TWE.Free V
  | .top | .bot => ∅
  | .atom (.wordEq u v) => Word.free u ∪ Word.free v
  | .conj F G | .disj F G => WordFormula.free F ∪ WordFormula.free G
  | .neg F => WordFormula.free F

def SetTerm.free : SetTerm Γ V → TWE.Free V
  | .var x => { (∅ : TWE.Free V) with set := {x} }
  | .empty => ∅
  | .insert A S => A.free ∪ S.free

def SetAtom.free : SetAtom Γ V → TWE.Free V
  | .eq _ S S' => S.free ∪ S'.free
  | .mem _ A S => A.free ∪ S.free

def TWESetAtom.free : TWESetAtom Γ V → TWE.Free V
  | .eq _ S S' => S.free ∪ S'.free
  | .mem _ A S => A.free ∪ S.free

def Atom.free : Atom Γ V → TWE.Free V
  | .word F => WordFormula.free F
  | .shape T ℓ _ | .undefined T ℓ => T.free ∪ Word.free ℓ
  | .entries R T ℓ => { (∅ : TWE.Free V) with set := {R} } ∪ T.free ∪ Word.free ℓ
  | .set α => α.free
  | .tweSet α => α.free

def Conj.free (β : Conj Γ V) : TWE.Free V :=
  β.foldr (init := ∅) fun α U => α.free ∪ U

/-- Runs `rewrite` with the variables of `β` in use, so that its fresh variables are not in `β`. -/
def chooseFreshVariables (β : Conj Γ V) (rewrite : FreshM V ρ) : ρ :=
  (rewrite.run β.free).1

/-- Each rewrite takes its fresh variables outside `done`, the conjunction produced so far, and the
atoms still to be rewritten. -/
def rewritePass (rule : Atom Γ V → FreshM V (Guess (Conj Γ V))) (done : Conj Γ V) :
    Conj Γ V → Guess (Conj Γ V)
  | [] => pure done
  | α :: rest =>
      (chooseFreshVariables (done ++ α :: rest) (rule α)).flatMap fun γ =>
        rewritePass rule (done ++ γ) rest

def rewriteAtoms (rule : Atom Γ V → FreshM V (Guess (Conj Γ V))) (β : Conj Γ V) :
    Guess (Conj Γ V) :=
  (·.flatMap (rewritePass rule []))^[β.passes] (pure β)

def rewriteConj (rule : Conj Γ V → FreshM V ρ) (β : Conj Γ V) : ρ :=
  chooseFreshVariables β (rule β)

variable [TWE.Vars.Fresh V]

def freshNames : Nat → FreshM V (List V.Name)
  | 0 => return []
  | n + 1 => do
      let A ← freshName
      return A :: (← freshNames n)

/-- A sequence of `n` fresh names `A x 0, …, A x (n - 1)` for every `x ∈ xs`. -/
def freshSequences {ι : Type} [DecidableEq ι] (xs : List ι) (n : Nat) :
    FreshM V (ι → Nat → V.Name) := do
  let unused ← freshName
  let names ← freshNames (xs.length * n)
  return fun x i => names.getD (xs.idxOf x * n + i) unused

def flattenSet : TWE.Set Γ V → FreshM V (SetTerm Γ V × List (EntriesTerm V))
  | .var x => return (.var x, [])
  | .empty => return (.empty, [])
  | .insert a S => do
      let (flat, terms) ← flattenSet S
      return (.insert a flat, terms)
  | .entries T => do
      let R ← freshSet
      return (.var R, [⟨R, T⟩])

def flattenSetAtom : TWESetAtom Γ V → FreshM V (SetAtom Γ V × List (EntriesTerm V))
  | .eq positive S S' => do
      let (flat, terms) ← flattenSet S
      let (flat', terms') ← flattenSet S'
      return (.eq positive flat flat', terms ++ terms')
  | .mem positive a S => do
      let (flat, terms) ← flattenSet S
      return (.mem positive a flat, terms)

end ToWE

end Linear

end TWE

end Accordion

end
