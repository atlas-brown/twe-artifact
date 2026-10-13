module

public import Accordion.TWE
public import Accordion.Fresh
public import Mathlib.Data.Set.Function

@[expose] public section

namespace Accordion

namespace TWE

class Vars.Comparable (V : Vars) where
  [name : DecidableEq V.Name]
  [comp : DecidableEq V.Comp]
  [path : DecidableEq V.Path]
  [loc  : DecidableEq V.Loc]
  [set  : DecidableEq V.Set]
  [tree : DecidableEq V.Tree]

class Vars.Unbounded (V : Vars) where
  [name : Infinite V.Name]
  [comp : Infinite V.Comp]
  [path : Infinite V.Path]
  [loc  : Infinite V.Loc]
  [set  : Infinite V.Set]

class Vars.Fresh (V : Vars) where
  [name : Accordion.Fresh V.Name]
  [comp : Accordion.Fresh V.Comp]
  [path : Accordion.Fresh V.Path]
  [loc  : Accordion.Fresh V.Loc]
  [set  : Accordion.Fresh V.Set]

-- Lean 4.32 rejects the `Comparable` projections as instances unless they are `reducible`.
attribute [reducible, instance]
  Vars.Comparable.name Vars.Comparable.comp Vars.Comparable.path
  Vars.Comparable.loc Vars.Comparable.set Vars.Comparable.tree
attribute [instance]
  Vars.Unbounded.name Vars.Unbounded.comp Vars.Unbounded.path
  Vars.Unbounded.loc Vars.Unbounded.set
attribute [reducible, instance]
  Vars.Fresh.name Vars.Fresh.comp Vars.Fresh.path
  Vars.Fresh.loc Vars.Fresh.set

instance (V : Vars) [Vars.Fresh V] : Vars.Unbounded V where

structure Free (V : Vars) where
  name : Finset V.Name
  comp : Finset V.Comp
  path : Finset V.Path
  loc  : Finset V.Loc
  set  : Finset V.Set
  tree : Finset V.Tree

variable {Γ : Type} {V : Vars}

instance : EmptyCollection (Free V) where
  emptyCollection := ⟨∅, ∅, ∅, ∅, ∅, ∅⟩

instance [Vars.Comparable V] : Union (Free V) where
  union U U' :=
    ⟨U.name ∪ U'.name, U.comp ∪ U'.comp, U.path ∪ U'.path,
      U.loc ∪ U'.loc, U.set ∪ U'.set, U.tree ∪ U'.tree⟩

instance : HasSubset (Free V) where
  Subset U U' :=
    U.name ⊆ U'.name ∧ U.comp ⊆ U'.comp ∧ U.path ⊆ U'.path ∧
      U.loc ⊆ U'.loc ∧ U.set ⊆ U'.set ∧ U.tree ⊆ U'.tree

namespace Name

def free [Vars.Comparable V] : Name Γ V → Free V
  | .name _ => ∅
  | .var x => { (∅ : Free V) with name := {x} }

end Name

namespace Component

def free [Vars.Comparable V] : Component Γ V → Free V
  | .empty => ∅
  | .self => ∅
  | .parent => ∅
  | .name a => a.free
  | .var x => { (∅ : Free V) with comp := {x} }

end Component

namespace Path

def free [Vars.Comparable V] : Path Γ V → Free V
  | .nil => ∅
  | .init b => b.free
  | .join p q => p.free ∪ q.free
  | .loc l => { (∅ : Free V) with loc := {l} }
  | .var x => { (∅ : Free V) with path := {x} }
  | .norm p => p.free

end Path

namespace Tree

def free [Vars.Comparable V] : Tree V → Free V
  | .var x => { (∅ : Free V) with tree := {x} }
  | .file => ∅
  | .emptyDirc => ∅
  | .abst => ∅
  | .select t l => t.free ∪ { (∅ : Free V) with loc := {l} }
  | .update t l t' => t.free ∪ { (∅ : Free V) with loc := {l} } ∪ t'.free

end Tree

namespace Set

def free [Vars.Comparable V] : Set Γ V → Free V
  | .var x => { (∅ : Free V) with set := {x} }
  | .empty => ∅
  | .insert a s => a.free ∪ s.free
  | .entries t => t.free

end Set

namespace Atom

def free [Vars.Comparable V] : Atom Γ V → Free V
  | .pathEq p q => p.free ∪ q.free
  | .pathIsLin p => p.free
  | .treeWalk p t l => t.free ∪ p.free ∪ { (∅ : Free V) with loc := {l} }
  | .treeShape t _ => t.free
  | .setEq s s' => s.free ∪ s'.free
  | .setMem a s => a.free ∪ s.free

end Atom

namespace Formula

open scoped Accordion.Formula in
def free [Vars.Comparable V] : Formula Γ V → Free V
  | ⊤ => ∅
  | ⊥ => ∅
  | .atom a => a.free
  | φ ⋏ ψ => free φ ∪ free ψ
  | φ ⋎ ψ => free φ ∪ free ψ
  | ∼φ => free φ

end Formula

namespace Model

def EqOn (m m' : Model Γ V) (U : Free V) : Prop :=
  Set.EqOn m.σName m'.σName ↑U.name ∧
    Set.EqOn m.σComp m'.σComp ↑U.comp ∧
    Set.EqOn m.σPath m'.σPath ↑U.path ∧
    Set.EqOn m.σLoc m'.σLoc ↑U.loc ∧
    Set.EqOn m.σSet m'.σSet ↑U.set ∧
    Set.EqOn m.θ m'.θ ↑U.tree

scoped notation:50 m:51 " ≡[" U "] " m':51 => Model.EqOn m m' U

end Model

def FreshM (V : Vars) (ρ : Type) : Type := StateM (Free V) ρ

instance : Monad (FreshM V) := inferInstanceAs (Monad (StateM (Free V)))

instance : LawfulMonad (FreshM V) := inferInstanceAs (LawfulMonad (StateM (Free V)))

def FreshM.run {ρ : Type} (x : FreshM V ρ) (U : Free V) : ρ × Free V := x U

variable [Vars.Comparable V] [Vars.Fresh V]

def freshName : FreshM V V.Name := fun U =>
  (Fresh.fresh U.name, { U with name := insert (Fresh.fresh U.name) U.name })

def freshPath : FreshM V V.Path := fun U =>
  (Fresh.fresh U.path, { U with path := insert (Fresh.fresh U.path) U.path })

def freshLoc : FreshM V V.Loc := fun U =>
  (Fresh.fresh U.loc, { U with loc := insert (Fresh.fresh U.loc) U.loc })

def freshSet : FreshM V V.Set := fun U =>
  (Fresh.fresh U.set, { U with set := insert (Fresh.fresh U.set) U.set })

end TWE

end Accordion

end
