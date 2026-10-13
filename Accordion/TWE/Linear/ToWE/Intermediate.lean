module

public import Accordion.TWE.Linear
public import Accordion.WE
public import Accordion.Guess

@[expose] public section

namespace Accordion

namespace FileTree

namespace Focus

variable {Γ : Type} [Ord Γ]

/-- Below a missing entry the focus is absent; below a file or an absent focus the lookup is
undefined. -/
def follow : FileTree.Focus Γ → List Γ → Option (FileTree.Focus Γ)
  | f, [] => some f
  | .abst, _ :: _ => none
  | .tree .file, _ :: _ => none
  | .tree (.dirc δ), a :: w =>
      match δ[a]? with
      | none => follow .abst w
      | some τ => follow (.tree τ) w

def shapeFollow (f : FileTree.Focus Γ) (w : List Γ) : Option TWE.Shape :=
  (f.follow w).map FileTree.Focus.shape

def entryNames [DecidableEq Γ] : FileTree.Focus Γ → Finset Γ
  | .abst | .tree .file => ∅
  | .tree (.dirc δ) => δ.dom

def entriesFollow [DecidableEq Γ] (f : FileTree.Focus Γ) (w : List Γ) : Option (Finset Γ) :=
  (f.follow w).map entryNames

end Focus

end FileTree

namespace TWE

def Tree.updates {V : TWE.TreeVars} : TWE.Tree V → List (TWE.Tree V)
  | .select T _ => T.updates
  | .update T l T' => .update T l T' :: (T.updates ++ T'.updates)
  | .var _ | .file | .emptyDirc | .abst => []

namespace Linear

namespace ToWE

open FileTree.Focus (shapeFollow entriesFollow)

variable {Γ : Type} {V : TWE.Vars}

abbrev Vars (V : TWE.Vars) : WE.Vars where
  Letter := V.Name ⊕ V.Comp
  Word := V.Path ⊕ V.Loc

abbrev Word (Γ : Type) (V : TWE.Vars) := WE.Word Γ (Vars V)

abbrev WordFormula (Γ : Type) (V : TWE.Vars) := WE.Formula Γ (Vars V)

/-- The set terms of this atom may contain `entries(T)`. -/
inductive TWESetAtom (Γ : Type) (V : TWE.Vars) where
  | eq (positive : Bool) (s t : TWE.Set Γ V)
  | mem (positive : Bool) (a : TWE.Name Γ V) (s : TWE.Set Γ V)

def TWESetAtom.positive : TWESetAtom Γ V → Bool
  | .eq positive _ _ | .mem positive _ _ => positive

/-- A set term without `entries(T)`. -/
inductive SetTerm (Γ : Type) (V : TWE.Vars) where
  | var (x : V.Set)
  | empty
  | insert (name : TWE.Name Γ V) (set : SetTerm Γ V)

inductive SetAtom (Γ : Type) (V : TWE.Vars) where
  | eq (positive : Bool) (left right : SetTerm Γ V)
  | mem (positive : Bool) (name : TWE.Name Γ V) (set : SetTerm Γ V)

/-- An atom of the formulas between the rewrites (Fig. 8). -/
inductive Atom (Γ : Type) (V : TWE.Vars) where
  | word (F : WordFormula Γ V)
  | shape (T : TWE.Tree V) (ℓ : Word Γ V) (h : TWE.Shape)
  /-- `T[ℓ]↑`: `T[ℓ]` is undefined. -/
  | undefined (T : TWE.Tree V) (ℓ : Word Γ V)
  | entries (R : V.Set) (T : TWE.Tree V) (ℓ : Word Γ V)
  | set (α : SetAtom Γ V)
  | tweSet (α : TWESetAtom Γ V)

abbrev Conj (Γ : Type) (V : TWE.Vars) := List (Atom Γ V)

/-- Lets atom notation denote an atom or the guess of the conjunction that consists of it. -/
class InjectAtom (Γ : outParam Type) (V : outParam TWE.Vars) (ρ : Type) where
  inject : Atom Γ V → ρ

instance : InjectAtom Γ V (Atom Γ V) := ⟨id⟩
instance : InjectAtom Γ V (Guess (Conj Γ V)) := ⟨fun α => pure [α]⟩

scoped instance : Coe V.Set (SetTerm Γ V) := ⟨SetTerm.var⟩
scoped notation:65 S:65 " ∪ " "{" A "}" => SetTerm.insert A S

scoped notation:max "⌜" F "⌝" => InjectAtom.inject (Atom.word F)

scoped notation:60 u:61 " ≐ " v:61 =>
  InjectAtom.inject (Atom.word (Accordion.Formula.atom (WE.Atom.wordEq u v)))
scoped notation:60 u:61 " ≠̇ " v:61 =>
  InjectAtom.inject
    (Atom.word (Accordion.Formula.neg (Accordion.Formula.atom (WE.Atom.wordEq u v))))
scoped notation:60 S:61 " ≐ " S':61 => InjectAtom.inject (Atom.set (SetAtom.eq true S S'))
scoped notation:60 S:61 " ≠̇ " S':61 => InjectAtom.inject (Atom.set (SetAtom.eq false S S'))
scoped notation:60 A:61 " ∈̇ " S:61 => InjectAtom.inject (Atom.set (SetAtom.mem true A S))
scoped notation:60 A:61 " ∉̇ " S:61 => InjectAtom.inject (Atom.set (SetAtom.mem false A S))

/-- `T[ℓ] ∶ h`, the paper's `T[ℓ] ∈ h`. -/
scoped syntax:60 term:max noWs "[" term "]" " ∶ " term:61 : term
scoped syntax:max term:max noWs "[" term "]" "↑" : term
/-- `R ≐ entries(T[ℓ])`, for a tree `T` given by an identifier. -/
scoped syntax:60 term:61 " ≐ " "entries(" ident noWs "[" term "]" ")" : term

macro_rules
  | `($T[$ℓ] ∶ $h) => `(InjectAtom.inject (Atom.shape $T $ℓ $h))
macro_rules
  | `($T[$ℓ]↑) => `(InjectAtom.inject (Atom.undefined $T $ℓ))
macro_rules
  | `($R ≐ entries($T:ident[$ℓ])) => `(InjectAtom.inject (Atom.entries $R $T $ℓ))

scoped instance : Coe (Atom Γ V) (Guess (Conj Γ V)) := ⟨InjectAtom.inject⟩

/-- A model with linear values: component variables denote names, and path variables and
locations denote words. -/
structure WordModel (Γ : Type) [Ord Γ] (V : TWE.Vars) where
  σName : V.Name → Γ
  σComp : V.Comp → Γ
  σPath : V.Path → WE.GroundWord Γ
  σLoc  : V.Loc → WE.GroundWord Γ
  σSet  : V.Set → Finset Γ
  θ     : V.Tree → { f : FileTree.Focus Γ // f.Canonical }

namespace WordModel

variable [Ord Γ]

def toTWE (m : WordModel Γ V) : TWE.Model Γ V where
  σName := m.σName
  σComp x := .name (m.σComp x)
  σPath x := (m.σPath x : Accordion.Path Γ)
  σLoc x := (m.σLoc x : Accordion.Path Γ)
  σSet := m.σSet
  θ x := (m.θ x).1

def toWE (m : WordModel Γ V) : WE.Model Γ (Vars V) where
  σLetter := Sum.elim m.σName m.σComp
  σWord := Sum.elim m.σPath m.σLoc

end WordModel

def ObservesShape [Ord Γ] (m : WordModel Γ V) (T : TWE.Tree V) (w : List Γ) (h : TWE.Shape) :
    Prop :=
  ∃ f, m.toTWE.evalTree T = some f ∧ shapeFollow f w = some h

def ObservesEntries [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V) (w : List Γ)
    (N : Finset Γ) : Prop :=
  ∃ f, m.toTWE.evalTree T = some f ∧ entriesFollow f w = some N

def TWESetAtom.sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) : TWESetAtom Γ V → Prop
  | .eq positive s t => if positive then m.toTWE ⊨ s ≐ t else ¬m.toTWE ⊨ s ≐ t
  | .mem positive a s => if positive then m.toTWE ⊨ a ∈̇ s else ¬m.toTWE ⊨ a ∈̇ s

def SetTerm.eval [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) : SetTerm Γ V → Finset Γ
  | .var x => m.σSet x
  | .empty => ∅
  | .insert name set => Insert.insert (m.toTWE.evalName name) (set.eval m)

def SetAtom.sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) : SetAtom Γ V → Prop
  | .eq positive left right =>
      if positive then left.eval m = right.eval m else left.eval m ≠ right.eval m
  | .mem positive name set =>
      if positive then m.toTWE.evalName name ∈ set.eval m
      else m.toTWE.evalName name ∉ set.eval m

def Atom.sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) : Atom Γ V → Prop
  | .word F => m.toWE ⊨ F
  | .shape T ℓ h => ObservesShape m T (m.toWE.evalWord ℓ) h
  | .undefined T ℓ => ¬∃ h, ObservesShape m T (m.toWE.evalWord ℓ) h
  | .entries R T ℓ => ObservesEntries m T (m.toWE.evalWord ℓ) (m.σSet R)
  | .set α => α.sat m
  | .tweSet α => α.sat m

def Conj.sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (β : Conj Γ V) : Prop :=
  ∀ α ∈ β, α.sat m

def Conj.SAT [Ord Γ] [DecidableEq Γ] (β : Conj Γ V) : Prop :=
  ∃ m : WordModel Γ V, Conj.sat m β

/-- A fragment of the formulas between the rewrites, given by the atoms it allows (Fig. 8). -/
abbrev Fragment (Γ : Type) (V : TWE.Vars) := Atom Γ V → Prop

def Atom.WalksRewritten : Atom Γ V → Prop
  | .word _ | .shape _ _ _ | .undefined _ _ | .tweSet _ => True
  | .entries _ _ _ | .set _ => False

def Atom.EntriesNamed : Atom Γ V → Prop
  | .tweSet _ => False
  | _ => True

def Atom.EntriesRewritten : Atom Γ V → Prop
  | .entries _ (.var _) _ => True
  | .entries _ _ _ | .tweSet _ => False
  | _ => True

def Atom.UpdatesEliminated : Atom Γ V → Prop
  | .word _ | .shape (.var _) _ _ | .entries _ (.var _) _ | .set _ => True
  | _ => False

def Atom.EntriesEliminated : Atom Γ V → Prop
  | .word _ | .shape (.var _) _ _ | .set _ => True
  | _ => False

def Atom.SetsEncoded : Atom Γ V → Prop
  | .word _ | .shape (.var _) _ _ => True
  | _ => False

def Atom.updates : Atom Γ V → List (TWE.Tree V)
  | .shape T _ _ | .undefined T _ | .entries _ T _ => T.updates
  | _ => []

def Atom.DefinedIn [Ord Γ] (α : Atom Γ V) (m : WordModel Γ V) : Prop :=
  ∀ u ∈ α.updates, (m.toTWE.evalTree u).isSome

/-- `β` forces its updates to be defined, as it does when it contains `u↓` for each update `u`. -/
def Conj.UpdatesDefined [Ord Γ] [DecidableEq Γ] (β : Conj Γ V) : Prop :=
  ∀ m : WordModel Γ V, (∀ α ∈ β, α.sat m ∨ ¬α.DefinedIn m) → ∀ α ∈ β, α.DefinedIn m

end ToWE

end Linear

end TWE

namespace Guess

open TWE.Linear.ToWE

variable {Γ : Type} {V : TWE.Vars}

/-- `D ∧ E`: a conjunction guessed from `D` conjoined with one guessed from `E`. -/
def and (D E : Guess (Conj Γ V)) : Guess (Conj Γ V) :=
  D.flatMap fun β => E.map (β ++ ·)

/-- `D ∨ E`: a guess from `D` or from `E`. -/
def or (D E : Guess (Conj Γ V)) : Guess (Conj Γ V) :=
  D ++ E

def bigConj (Ds : List (Guess (Conj Γ V))) : Guess (Conj Γ V) :=
  Ds.foldr and (pure [])

def bigDisj (Ds : List (Guess (Conj Γ V))) : Guess (Conj Γ V) :=
  Ds.foldr or failure

@[inherit_doc] scoped infixr:35 " ∧ " => Guess.and
@[inherit_doc] scoped infixr:30 " ∨ " => Guess.or
/-- The empty conjunction. -/
scoped notation "⊤" => (pure [] : Guess (List _))
/-- The empty disjunction. -/
scoped notation "⊥" => (failure : Guess _)

def sat [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (D : Guess (Conj Γ V)) : Prop :=
  ∃ β ∈ D, Conj.sat m β

def SAT [Ord Γ] [DecidableEq Γ] (D : Guess (Conj Γ V)) : Prop :=
  ∃ m : WordModel Γ V, sat m D

def AllAtoms (P : Atom Γ V → Prop) (D : Guess (Conj Γ V)) : Prop :=
  ∀ β ∈ D, ∀ α ∈ β, P α

def UpdatesDefined [Ord Γ] [DecidableEq Γ] (D : Guess (Conj Γ V)) : Prop :=
  ∀ β ∈ D, β.UpdatesDefined

instance : Membership (Guess (Conj Γ V)) (Fragment Γ V) := ⟨fun P D => AllAtoms P D⟩

end Guess

end Accordion

end
