module

public import Accordion.TWE.Linear.ToWE.Rewrites
public import Accordion.FileTree.Entries.Properties
public import Accordion.Guess.Properties

@[expose] public section

namespace Accordion

namespace FileTree

variable {Γ : Type}

def Ctx.Missing [Ord Γ] : Ctx Γ → Prop
  | .hole => True
  | .node δ a C => δ.lookup a = none ∧ C.Missing

def Ctx.word : Ctx Γ → List Γ
  | .hole => []
  | .node _ a C => a :: C.word

def Ctx.plug [Ord Γ] (C : Ctx Γ) (f : Focus Γ) : Focus Γ :=
  match C.fill f with
  | some τ => .tree τ
  | none => .abst

def Entries.plug [Ord Γ] (δ : Entries Γ (FileTree Γ)) (a : Γ) :
    Focus Γ → Entries Γ (FileTree Γ)
  | .tree τ => δ.insert a τ
  | .abst => δ

def Focus.tree? : Focus Γ → Option (FileTree Γ)
  | .tree T => some T
  | .abst => none

end FileTree

namespace TWE

open Linear.ToWE (WordModel)

variable {Γ : Type} {V : TWE.Vars}

/-- A component variable whose value is not a name gets the name `a`. -/
def Model.toWordModel [Ord Γ] (m : TWE.Model Γ V) (hwf : m.WF) (a : Γ) : WordModel Γ V where
  σName := m.σName
  σComp x := match m.σComp x with
    | .name b => b
    | _ => a
  σPath x := (m.σPath x).names
  σLoc x := (m.σLoc x).names
  σSet := m.σSet
  θ x := ⟨m.θ x, hwf.2 x⟩

namespace Linear

namespace ToWE

open FileTree.Focus (follow shapeFollow entriesFollow)
open scoped Accordion.Formula WE Accordion.Guess BigConnectives

namespace WordModel

variable [Ord Γ]

def setName [DecidableEq V.Name] (m : WordModel Γ V) (x : V.Name) (a : Γ) : WordModel Γ V :=
  { m with σName := fun y ↦ if y = x then a else m.σName y }

def setComp [DecidableEq V.Comp] (m : WordModel Γ V) (x : V.Comp) (a : Γ) : WordModel Γ V :=
  { m with σComp := fun y ↦ if y = x then a else m.σComp y }

def setPath [DecidableEq V.Path] (m : WordModel Γ V) (x : V.Path) (w : WE.GroundWord Γ) :
    WordModel Γ V :=
  { m with σPath := fun y ↦ if y = x then w else m.σPath y }

def setLoc [DecidableEq V.Loc] (m : WordModel Γ V) (l : V.Loc) (w : WE.GroundWord Γ) :
    WordModel Γ V :=
  { m with σLoc := fun y ↦ if y = l then w else m.σLoc y }

def setSet [DecidableEq V.Set] (m : WordModel Γ V) (x : V.Set) (s : Finset Γ) : WordModel Γ V :=
  { m with σSet := fun y ↦ if y = x then s else m.σSet y }

def EqOn (m m' : WordModel Γ V) (U : TWE.Free V) : Prop :=
  Set.EqOn m.σName m'.σName ↑U.name ∧
    Set.EqOn m.σComp m'.σComp ↑U.comp ∧
    Set.EqOn m.σPath m'.σPath ↑U.path ∧
    Set.EqOn m.σLoc m'.σLoc ↑U.loc ∧
    Set.EqOn m.σSet m'.σSet ↑U.set ∧
    Set.EqOn m.θ m'.θ ↑U.tree

scoped notation:50 m:51 " ≡[" U "] " m':51 => WordModel.EqOn m m' U

def evalPath (m : WordModel Γ V) : TWE.Path Γ V → WE.GroundWord Γ
  | .nil => []
  | .init (.name (.name a)) => [a]
  | .init (.name (.var x)) => [m.σName x]
  | .init (.var x) => [m.σComp x]
  | .init .empty | .init .self | .init .parent => []
  | .join p q => evalPath m p ++ evalPath m q
  | .loc l => m.σLoc l
  | .var x => m.σPath x
  | .norm p => evalPath m p

def withTrees (m : WordModel Γ V) (θ : V.Tree → { f : FileTree.Focus Γ // f.Canonical }) :
    WordModel Γ V :=
  { m with θ := θ }

def withSets (m : WordModel Γ V) (σSet : V.Set → Finset Γ) : WordModel Γ V :=
  { m with σSet := σSet }

def entriesValue [DecidableEq Γ] (m : WordModel Γ V) (T : TWE.Tree V) : Option (Finset Γ) :=
  m.toTWE.evalNameSet (.entries T)

end WordModel

end ToWE

end Linear

end TWE

namespace Guess

open TWE.Linear.ToWE
open scoped WordModel

variable {Γ : Type} {V : TWE.Vars} [Ord Γ] [DecidableEq Γ]

/-- `D` holds after giving new values to the variables outside `U`. -/
def satFresh (m : WordModel Γ V) (U : TWE.Free V) (D : Guess (Conj Γ V)) : Prop :=
  ∃ m', m ≡[U] m' ∧ sat m' D

end Guess

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

namespace Linear

namespace ToWE

open FileTree.Focus (follow shapeFollow entriesFollow)
open scoped Accordion.Formula WE Accordion.Guess BigConnectives

def sourceSkeleton [Ord Γ] (target : WE.Model Γ (Vars V)) : WordModel Γ V where
  σName x := target.σLetter (.inl x)
  σComp x := target.σLetter (.inr x)
  σPath x := target.σWord (.inl x)
  σLoc x := target.σWord (.inr x)
  σSet _ := ∅
  θ _ := ⟨.abst, by trivial⟩

def Leaf (f : FileTree.Focus Γ) : Prop :=
  f.shape = .file ∨ f.shape = .absent

section SatFresh

open scoped WordModel

variable [Ord Γ] [DecidableEq Γ]

def SatPreserving (U : TWE.Free V) (β : Conj Γ V) (D : Guess (Conj Γ V)) : Prop :=
  ∀ m : WordModel Γ V, Guess.satFresh m U D ↔ Conj.sat m β

def SatPreservingIn (M : WordModel Γ V → Prop) (U : TWE.Free V) (β : Conj Γ V)
    (D : Guess (Conj Γ V)) : Prop :=
  ∀ m, M m → (Guess.satFresh m U D ↔ Conj.sat m β)

def Conj.Ensures (cond : Atom Γ V → WordModel Γ V → Prop) (β : Conj Γ V) : Prop :=
  ∀ m, (∀ α ∈ β, α.sat m ∨ ¬cond α m) → ∀ α ∈ β, cond α m

end SatFresh

def Atom.shapeRank : Atom Γ V → Nat
  | .shape T _ _ => 2 * T.size
  | .undefined T _ => 2 * T.size + 1
  | _ => 0

def Atom.entriesRank : Atom Γ V → Nat
  | .entries _ T _ => T.size
  | _ => 0

def Atom.tweSetRank : Atom Γ V → Nat
  | .tweSet _ => 1
  | _ => 0

def EntriesTerm.Holds [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (e : EntriesTerm V) : Prop :=
  m.entriesValue e.tree = some (m.σSet e.set)

structure GroundTreeShapeAssertion (Γ X : Type) where
  tree : X
  path : List Γ
  shape : TWE.Shape

def evalBaseShapeAssertions [Ord Γ] (m : WordModel Γ V) (atoms : List (BaseShapeAssertion Γ V)) :
    List (GroundTreeShapeAssertion Γ V.Tree) :=
  atoms.map fun atom ↦ ⟨atom.tree, m.toWE.evalWord atom.query, atom.shape⟩

def BaseShapeAssertionsSat [Ord Γ] (m : WordModel Γ V) (atoms : List (BaseShapeAssertion Γ V)) :
    Prop :=
  ∀ atom ∈ atoms, ObservesShape m (.var atom.tree) (m.toWE.evalWord atom.query) atom.shape

/-- For a directory `R = entries(t[ℓ])` and an observed location `t[ℓ'] ∶ h`: a name `A` with
`ℓ' = ℓ A K` is an entry of the directory exactly when `t[ℓ A]` is present. -/
def DirectoryRelation (ℓ ℓ' : List Γ) (R : Finset Γ) (h : TWE.Shape) : Prop :=
  ∀ A K, ℓ' = ℓ ++ A :: K → (A ∈ R ↔ K ≠ [] ∨ h ≠ .absent)

def EntriesCaseHolds [Ord Γ] (m : WordModel Γ V) (source : Conj Γ V) (hs : List TWE.Shape) :
    Prop :=
  (∀ p ∈ source.baseEntries.zip hs,
    ObservesShape m (.var p.1.tree) (m.toWE.evalWord p.1.query) p.2 ∧
      (p.2 ≠ .dirc → m.σSet p.1.set = ∅)) ∧
  (∀ p ∈ source.baseEntries ×ˢ source.baseEntries, p.1.tree = p.2.tree →
    m.toWE.evalWord p.1.query = m.toWE.evalWord p.2.query → m.σSet p.1.set = m.σSet p.2.set) ∧
  ∀ p ∈ caseDirectories source hs ×ˢ caseShapes source hs, p.1.tree = p.2.tree →
    DirectoryRelation (m.toWE.evalWord p.1.query) (m.toWE.evalWord p.2.query) (m.σSet p.1.set)
      p.2.shape

/-- The set that a sequence of names encodes: its values other than `c`, the value of `#`. -/
def encodedSet [Ord Γ] [DecidableEq Γ] (m : WordModel Γ V) (c : Γ)
    (names : List (TWE.Name Γ V)) : Finset Γ :=
  (names.map m.toTWE.evalName).toFinset.erase c

def SetTerm.encodingNames (N : V.Set → Nat → V.Name) (width : Nat) (S : SetTerm Γ V) :
    List (TWE.Name Γ V) :=
  S.names ++ S.variables.flatMap fun x ↦ (List.range width).map fun i ↦ .var (N x i)

abbrev GroundShapeObservation (Γ : Type) := List Γ × TWE.Shape

def rootShape (observations : List (GroundShapeObservation Γ)) : Option TWE.Shape :=
  (observations.find? (·.1.isEmpty)).map (·.2)

def childObservations [DecidableEq Γ] (a : Γ) (observations : List (GroundShapeObservation Γ)) :
    List (GroundShapeObservation Γ) :=
  observations.filterMap fun
    | (b :: w, h) => if b = a then some (w, h) else none
    | ([], _) => none

def observationHeads (observations : List (GroundShapeObservation Γ)) : List Γ :=
  observations.filterMap (·.1.head?)

/-- A node is absent unless it is observed as a file or a directory, or an observation goes through
it. -/
def buildShapeFocus [Ord Γ] [DecidableEq Γ] :
    Nat → List (GroundShapeObservation Γ) → FileTree.Focus Γ
  | 0, _ => .abst
  | fuel + 1, observations =>
      match rootShape observations with
      | some .absent => .abst
      | some .file => .tree .file
      | root =>
          if root = some .dirc ∨ observationHeads observations ≠ [] then
            .tree (.dirc (.ofSigmas ((observationHeads observations).filterMap fun a ↦
              (buildShapeFocus fuel (childObservations a observations)).tree?.map (⟨a, ·⟩))))
          else .abst

def ShapeFunctional (observations : List (GroundShapeObservation Γ)) : Prop :=
  ∀ path h k, (path, h) ∈ observations → (path, k) ∈ observations → h = k

def ShapeLeafCompatible (observations : List (GroundShapeObservation Γ)) : Prop :=
  ∀ path h, (path, h) ∈ observations → h ≠ .dirc →
    ∀ query k, (query, k) ∈ observations →
      ¬(path <+: query ∧ path ≠ query)

def Forced (observations : List (GroundShapeObservation Γ)) (w : List Γ) : Prop :=
  ∃ s h, (w ++ s, h) ∈ observations ∧ (s ≠ [] ∨ h ≠ .absent)

abbrev GroundDirectoryObservation (Γ : Type) := List Γ × Finset Γ

def observationFuel (observations : List (GroundShapeObservation Γ)) : Nat :=
  (observations.map (·.1.length)).sum + 1

structure GroundTreeDirectoryObservation (Γ X : Type) where
  tree : X
  path : List Γ
  entries : Finset Γ

section Ground

variable {X : Type}

def shapeObservationsFor [DecidableEq X] (x : X)
    (atoms : List (GroundTreeShapeAssertion Γ X)) : List (GroundShapeObservation Γ) :=
  atoms.filterMap fun atom ↦ if atom.tree = x then some (atom.path, atom.shape) else none

def directoryObservationsFor [DecidableEq X] (x : X)
    (atoms : List (GroundTreeDirectoryObservation Γ X)) : List (GroundDirectoryObservation Γ) :=
  atoms.filterMap fun atom ↦ if atom.tree = x then some (atom.path, atom.entries) else none

def FunctionalConsistency
    (atoms : List (GroundTreeShapeAssertion Γ X)) : Prop :=
  ∀ left ∈ atoms, ∀ right ∈ atoms,
    left.tree = right.tree → left.path = right.path → left.shape = right.shape

def LeafCondition
    (atoms : List (GroundTreeShapeAssertion Γ X)) : Prop :=
  ∀ leaf ∈ atoms, leaf.shape ≠ .dirc →
    ∀ atom ∈ atoms, leaf.tree = atom.tree →
      ¬(leaf.path <+: atom.path ∧ leaf.path ≠ atom.path)

def GroundShapesRealised [Ord Γ]
    (θ : X → { f : FileTree.Focus Γ // f.Canonical })
    (atoms : List (GroundTreeShapeAssertion Γ X)) : Prop :=
  ∀ atom ∈ atoms,
    shapeFollow (θ atom.tree).1 atom.path = some atom.shape

def GroundDirectoriesFunctional
    (directories : List (GroundTreeDirectoryObservation Γ X)) : Prop :=
  ∀ left ∈ directories, ∀ right ∈ directories,
    left.tree = right.tree → left.path = right.path →
      left.entries = right.entries

def GroundDirectoryEndpointsObserved
    (shapes : List (GroundTreeShapeAssertion Γ X))
    (directories : List (GroundTreeDirectoryObservation Γ X)) : Prop :=
  ∀ directory ∈ directories,
    (⟨directory.tree, directory.path, .dirc⟩ :
      GroundTreeShapeAssertion Γ X) ∈ shapes

def GroundDirectoryShapesCompatible
    (shapes : List (GroundTreeShapeAssertion Γ X))
    (directories : List (GroundTreeDirectoryObservation Γ X)) : Prop :=
  ∀ directory ∈ directories, ∀ shape ∈ shapes,
    directory.tree = shape.tree → ∀ name suffix,
      shape.path = directory.path ++ (name :: suffix) →
      (name ∈ directory.entries ↔ suffix ≠ [] ∨ shape.shape ≠ .absent)

structure GroundDirectoryShapeCompatibility
    (shapes : List (GroundTreeShapeAssertion Γ X))
    (directories : List (GroundTreeDirectoryObservation Γ X)) : Prop where
  shapesFunctional : FunctionalConsistency shapes
  shapesLeafCompatible : LeafCondition shapes
  directoriesFunctional : GroundDirectoriesFunctional directories
  endpointsObserved : GroundDirectoryEndpointsObserved shapes directories
  shapesCompatible : GroundDirectoryShapesCompatible shapes directories

def GroundDirectoriesRealised [Ord Γ] [DecidableEq Γ]
    (θ : X → { focus : FileTree.Focus Γ // focus.Canonical })
    (directories : List (GroundTreeDirectoryObservation Γ X)) : Prop :=
  ∀ directory ∈ directories,
    entriesFollow (θ directory.tree).1 directory.path = some directory.entries

end Ground

end ToWE

end Linear

end TWE

end Accordion

end
