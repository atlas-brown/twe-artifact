module

public import Accordion.WE.LenEq.ToWalk.Defs
public import Accordion.WE.ShapeReg

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula ShapeReg

variable {Γ : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace ToShapeReg

inductive PathVar (X : Type) where
  | source (x : X)
  | inverse (x : X)
  | up

abbrev Vars (X : Type) : ShapeReg.Vars where
  Path := PathVar X
  Tree := Unit

/-- The target alphabet: `Γ` plus a separator that is not a letter of `Γ`, so that no source word
contains it. -/
inductive Alphabet (Γ : Type) where
  | letter (a : Γ)
  | sep

namespace Alphabet

def letter? : Alphabet Γ → Option Γ
  | letter a => some a
  | sep => none

instance [Ord Γ] : Ord (Alphabet Γ) :=
  ⟨fun a b => compare a.letter? b.letter?⟩

instance [Ord Γ] [Std.TransOrd Γ] : Std.TransOrd (Alphabet Γ) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := compare (α := Option Γ))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := compare (α := Option Γ))

instance [Ord Γ] [Std.LawfulEqOrd Γ] : Std.LawfulEqOrd (Alphabet Γ) where
  compare_self := Std.ReflCmp.compare_self (cmp := compare (α := Option Γ))
  eq_of_compare {a b} h := by
    have h : a.letter? = b.letter? :=
      Std.LawfulEqCmp.eq_of_compare (cmp := compare) (h : compare a.letter? b.letter? = .eq)
    cases a <;> cases b <;> simp_all [letter?]

end Alphabet

def encWord : GroundWord Γ → GroundWord (Alphabet Γ)
  | [] => []
  | a :: w => .letter a :: .sep :: encWord w

def liftWord : WE.Word Γ V → ShapeReg.Path (Alphabet Γ) (Vars V.Word)
  | .empty => ε
  | .letter a => .letter (.letter a) ++ .letter .sep
  | .letterVar x => isEmptyElim x
  | .var x => .var (.source x)
  | .concat u v => liftWord u ++ liftWord v

def invertWord : WE.Word Γ V → ShapeReg.Path (Alphabet Γ) (Vars V.Word)
  | .empty => ε
  | .letter _ => .var .up ++ .var .up
  | .letterVar x => isEmptyElim x
  | .var x => .var (.inverse x)
  | .concat u v => invertWord u ++ invertWord v

def sourceLang : ShapeReg.Regex (Alphabet Γ) :=
  .star (.concat (.nameNotIn {.sep}) (.name .sep))

def inverseLang : ShapeReg.Regex (Alphabet Γ) :=
  .star (.concat .parent .parent)

def site (u v : WE.Word Γ V) : ShapeReg.Path (Alphabet Γ) (Vars V.Word) :=
  liftWord u ++ invertWord v

def prefixed [Inhabited Γ] (p : ShapeReg.Path (Alphabet Γ) (Vars V.Word)) :
    ShapeReg.Path (Alphabet Γ) (Vars V.Word) :=
  .letter (.letter default) ++ (.letter .sep ++ p)

def probe (p : ShapeReg.Path (Alphabet Γ) (Vars V.Word)) :
    ShapeReg.Path (Alphabet Γ) (Vars V.Word) :=
  p ++ (.var .up ++ .letter .sep)

def walks [Inhabited Γ] (u v : WE.Word Γ V) : ShapeReg.Formula (Alphabet Γ) (Vars V.Word) :=
  (() ⊢ site u v ⇝ .dirc) ⋏ (() ⊢ prefixed (site u v) ⇝ .dirc)

def balanced [Inhabited Γ] (u v : WE.Word Γ V) : ShapeReg.Formula (Alphabet Γ) (Vars V.Word) :=
  (() ⊢ probe (site u v) ⇝ .file) ⋏ (() ⊢ probe (prefixed (site u v)) ⇝ .dirc)

def guards [Inhabited Γ] (φ : Formula Γ V) : ShapeReg.Formula (Alphabet Γ) (Vars V.Word) :=
  Accordion.Formula.bigConj
    ([() ⊢ .letter .sep ⇝ .file, .var PathVar.up ∈̇ .parent] ++
      (Formula.vars φ).map (fun x =>
        (.var (PathVar.source x) ∈̇ sourceLang) ⋏ (.var (PathVar.inverse x) ∈̇ inverseLang) ⋏
          walks (.var x) (.var x) ⋏ balanced (.var x) (.var x)) ++
      φ.atoms.filterMap fun
        | .lenEq u v => some (walks u v)
        | .wordEq _ _ => none)

def sourceModel (m : ShapeReg.Model (Alphabet Γ) (Vars V.Word)) : Model Γ V where
  σLetter x := isEmptyElim x
  σWord x := (m.σPath (.source x)).names.filterMap Alphabet.letter?

def touch [Ord Γ] (δ : FileTree.Entries (Alphabet Γ) (FileTree (Alphabet Γ))) :
    FileTree.Entries (Alphabet Γ) (FileTree (Alphabet Γ)) :=
  δ.insert .sep .file

def walkedWords (φ : Formula Γ V) (m : Model Γ V) : List (GroundWord Γ) :=
  (Formula.vars φ).map m.σWord ++
    φ.atoms.filterMap fun
      | .lenEq u _ => some (m.evalWord u)
      | .wordEq _ _ => none

def dirWords [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) : List (GroundWord (Alphabet Γ)) :=
  (walkedWords φ m).map encWord ++ (walkedWords φ m).map (fun w => encWord (default :: w))

end ToShapeReg

open ToShapeReg

def Model.toShapeReg [Ord Γ] [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    ShapeReg.Model (Alphabet Γ) (ToShapeReg.Vars V.Word) where
  σPath
    | .source x => (encWord (m.σWord x) : Accordion.Path (Alphabet Γ))
    | .inverse x => ToNorm.parents (2 * GroundWord.length (m.σWord x))
    | .up => ToNorm.parents 1
  θ _ := .tree (.dirc (touch (ToWalk.mkdirs (dirWords φ m))))

namespace Atom

def toShapeReg [Inhabited Γ] : Atom Γ V → ShapeReg.Formula (Alphabet Γ) (ToShapeReg.Vars V.Word)
  | .wordEq u v => liftWord u ≐ liftWord v
  | .lenEq u v => balanced u v

end Atom

end LenEq

end WE

end Accordion

end
