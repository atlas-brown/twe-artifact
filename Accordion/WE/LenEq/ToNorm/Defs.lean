module

public import Mathlib.Basic.IsEmpty.Defs
public import Accordion.WE.LenEq
public import Accordion.WE.Norm

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula Norm

variable {Γ X : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace ToNorm

inductive Var (X : Type) where
  | source (x : X)
  | inverse (x : X)
  | up

def liftWord : WE.Word Γ V → Norm.Path Γ (Var V.Word)
  | .empty => ε
  | .letter a => .letter a
  | .letterVar x => isEmptyElim x
  | .var x => .var (.source x)
  | .concat u v => liftWord u ++ liftWord v

def invertWord : WE.Word Γ V → Norm.Path Γ (Var V.Word)
  | .empty => ε
  | .letter _ => .var .up
  | .letterVar x => isEmptyElim x
  | .var x => .var (.inverse x)
  | .concat u v => invertWord u ++ invertWord v

def inverseGuards [Inhabited Γ] (xs : List X) :
    Norm.Formula Γ (Var X) :=
  Norm.Formula.pathBalanced (.letter default ++ .var .up) ⋏
    Accordion.Formula.bigConj (xs.map fun x =>
      Norm.Formula.pathBalanced (.var (.source x) ++ .var (.inverse x)))

def parents : Nat → Accordion.Path Γ
  | 0 => ε
  | n + 1 => .app (parents n) ‥

def sourceModel (m : Norm.Model Γ (Var V.Word)) : Model Γ V where
  σLetter x := isEmptyElim x
  σWord x := (m.σPath (.source x)).norm.names

end ToNorm

open ToNorm

def Model.toNorm (m : Model Γ V) : Norm.Model Γ (Var V.Word) where
  σPath
    | .source x => (m.σWord x : Accordion.Path Γ)
    | .inverse x => parents (GroundWord.length (m.σWord x))
    | .up => parents 1

namespace Atom

def toNorm [Inhabited Γ] : Atom Γ V → Norm.Formula Γ (Var V.Word)
  | .wordEq u v => .norm (liftWord u) ≐ .norm (liftWord v)
  | .lenEq u v => Norm.Formula.pathBalanced (liftWord u ++ invertWord v)

end Atom

end LenEq

end WE

end Accordion

end
