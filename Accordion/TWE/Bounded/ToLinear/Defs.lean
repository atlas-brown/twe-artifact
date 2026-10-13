module

public import Accordion.TWE.Bounded.ToLinear.Intermediate
public import Accordion.TWE.Linear.ToWE.Defs

@[expose] public section

namespace Accordion

namespace TWE

variable {Γ : Type} {V : TWE.Vars}

def Path.compVars : TWE.Path Γ V → List V.Comp
  | .nil | .loc _ | .var _ => []
  | .init (.var x) => [x]
  | .init _ => []
  | .join p q => p.compVars ++ q.compVars
  | .norm p => p.compVars

def Path.pathVars : TWE.Path Γ V → List V.Path
  | .nil | .init _ | .loc _ => []
  | .var x => [x]
  | .join p q => p.pathVars ++ q.pathVars
  | .norm p => p.pathVars

def Formula.compVars : TWE.Formula Γ V → List V.Comp
  | .top | .bot | .atom (.treeShape _ _) | .atom (.setEq _ _) | .atom (.setMem _ _) => []
  | .conj φ ψ | .disj φ ψ => compVars φ ++ compVars ψ
  | .neg φ => compVars φ
  | .atom (.pathEq p q) => p.compVars ++ q.compVars
  | .atom (.pathIsLin p) | .atom (.treeWalk p _ _) => p.compVars

def Formula.pathVars : TWE.Formula Γ V → List V.Path
  | .top | .bot | .atom (.treeShape _ _) | .atom (.setEq _ _) | .atom (.setMem _ _) => []
  | .conj φ ψ | .disj φ ψ => pathVars φ ++ pathVars ψ
  | .neg φ => pathVars φ
  | .atom (.pathEq p q) => p.pathVars ++ q.pathVars
  | .atom (.pathIsLin p) | .atom (.treeWalk p _ _) => p.pathVars

namespace Bounded

namespace ToLinear

variable {α β : Type}

structure FreshState (Γ : Type) (V : TWE.Vars) where
  used : TWE.Free V
  definitions : List (TWE.Formula Γ V)

/-- A computation that takes fresh variables and records their defining equations. -/
def FreshDefM (Γ : Type) (V : TWE.Vars) (α : Type) : Type := StateM (FreshState Γ V) α

instance : Monad (FreshDefM Γ V) := inferInstanceAs (Monad (StateM (FreshState Γ V)))

instance : LawfulMonad (FreshDefM Γ V) :=
  inferInstanceAs (LawfulMonad (StateM (FreshState Γ V)))

def FreshDefM.run (x : FreshDefM Γ V α) (s : FreshState Γ V) : α × FreshState Γ V := x s

def FreshDefM.start (x : FreshDefM Γ V α) (U : TWE.Free V) : α × List (TWE.Formula Γ V) :=
  ((x.run ⟨U, []⟩).1, (x.run ⟨U, []⟩).2.definitions)

def FreshDefM.lift (x : FreshM V α) : FreshDefM Γ V α := fun s =>
  ((x.run s.used).1, { s with used := (x.run s.used).2 })

def define (F : TWE.Formula Γ V) : FreshDefM Γ V Unit := fun s =>
  ((), { s with definitions := s.definitions ++ [F] })

/-- A component variable that `δ` does not mention is a name. -/
def VariableDecomposition.component [DecidableEq V.Comp] (δ : VariableDecomposition V)
    (x : V.Comp) : ComponentKind :=
  (δ.components.lookup x).getD .name

/-- A path variable that `δ` does not mention is its own single block. -/
def VariableDecomposition.path [DecidableEq V.Path] (δ : VariableDecomposition V) (x : V.Path) :
    V.Path × List (Step × V.Path) :=
  (δ.paths.lookup x).getD (x, [])

def VariableDecomposition.blocks (δ : VariableDecomposition V) : List V.Path :=
  δ.paths.flatMap fun p => p.2.1 :: p.2.2.map Prod.snd

def VariableDecomposition.free [DecidableEq V.Path] (δ : VariableDecomposition V) : TWE.Free V :=
  { (∅ : TWE.Free V) with path := δ.blocks.toFinset }

namespace Decomposition

def nil : Decomposition Γ V := ⟨.nil, []⟩

def linear (path : TWE.Path Γ V) : Decomposition Γ V := ⟨path, []⟩

def step (value : Step) : Decomposition Γ V := ⟨.nil, [(value, .nil)]⟩

def var (blocks : V.Path × List (Step × V.Path)) : Decomposition Γ V :=
  ⟨blocks.1, blocks.2.map fun p => (p.1, (p.2 : TWE.Path Γ V))⟩

def blocks (decomposition : Decomposition Γ V) : List (TWE.Path Γ V) :=
  decomposition.first :: decomposition.rest.map Prod.snd

def steps (decomposition : Decomposition Γ V) : List Step :=
  decomposition.rest.map Prod.fst

def appendToLast : List (Step × TWE.Path Γ V) → TWE.Path Γ V → List (Step × TWE.Path Γ V)
  | [], _ => []
  | [(step, block)], suffix => [(step, block ++ suffix)]
  | pair :: next :: rest, suffix => pair :: appendToLast (next :: rest) suffix

def append (left right : Decomposition Γ V) : Decomposition Γ V :=
  match left.rest with
  | [] => ⟨left.first ++ right.first, right.rest⟩
  | rest => ⟨left.first, appendToLast rest right.first ++ right.rest⟩

end Decomposition

def ComponentKind.all : List ComponentKind :=
  [.name, .empty, .self, .parent]

def stepPatterns : Nat → Guess (List Step)
  | 0 => pure []
  | k + 1 => pure [] ++ do
      let step ← guess [Step.empty, Step.self, Step.parent]
      let steps ← stepPatterns k
      pure (step :: steps)

def assignments : List α → Guess β → Guess (List (α × β))
  | [], _ => pure []
  | x :: xs, values => do
      let value ← values
      let rest ← assignments xs values
      pure ((x, value) :: rest)

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

def freshLoc : FreshDefM Γ V V.Loc := .lift TWE.freshLoc

def freshPath : FreshDefM Γ V V.Path := .lift TWE.freshPath

def freshName : FreshDefM Γ V V.Name := .lift TWE.freshName

def freshBlocks : List Step → FreshM V (List (Step × V.Path))
  | [] => return []
  | C :: steps => do
      let X ← TWE.freshPath
      return (C, X) :: (← freshBlocks steps)

/-- For each `X` with non-linear components `C₁ ⋯ Cₘ`, the decomposition `X = X₀ C₁ X₁ ⋯ Cₘ Xₘ`
with fresh path variables `Xᵢ`. -/
def freshDecompositions :
    List (V.Path × List Step) → FreshM V (List (V.Path × V.Path × List (Step × V.Path)))
  | [] => return []
  | p :: paths => do
      let X₀ ← TWE.freshPath
      let blocks ← freshBlocks p.2
      return (p.1, X₀, blocks) :: (← freshDecompositions paths)

end ToLinear

end Bounded

end TWE

end Accordion

end
