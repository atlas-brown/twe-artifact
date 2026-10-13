module

public import Accordion.WE.LenEq.ToNorm.Defs
public import Accordion.WE.Walk

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula Walk

variable {Γ : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace ToWalk

inductive PathVar (X : Type) where
  | inverse (x : X)
  | up

inductive Loc (Γ : Type) (V : WE.Vars) where
  | source (x : V.Word)
  | endpoint (u v : WE.Word Γ V)
  | prefixed (u v : WE.Word Γ V)

abbrev Vars (Γ : Type) (V : WE.Vars) : Walk.Vars where
  Path := PathVar V.Word
  Loc := Loc Γ V
  Tree := Unit

def liftWord : WE.Word Γ V → Walk.Path Γ (Vars Γ V)
  | .empty => ε
  | .letter a => .letter a
  | .letterVar x => isEmptyElim x
  | .var x => .loc (Loc.source x)
  | .concat u v => liftWord u ++ liftWord v

def invertWord : WE.Word Γ V → Walk.Path Γ (Vars Γ V)
  | .empty => ε
  | .letter _ => .var PathVar.up
  | .letterVar x => isEmptyElim x
  | .var x => .var (PathVar.inverse x)
  | .concat u v => invertWord u ++ invertWord v

def walks [Inhabited Γ] (u v : WE.Word Γ V) : Walk.Formula Γ (Vars Γ V) :=
  (() ⊢ liftWord u ++ invertWord v ⇝ Loc.endpoint u v) ⋏
    (() ⊢ .letter default ++ (liftWord u ++ invertWord v) ⇝ Loc.prefixed u v)

def atRoot (u v : WE.Word Γ V) : Walk.Formula Γ (Vars Γ V) :=
  (.loc (Loc.endpoint u v) ≐ ε) ⋏ ∼(.loc (Loc.prefixed u v) ≐ ε)

def guards [Inhabited Γ] (φ : Formula Γ V) : Walk.Formula Γ (Vars Γ V) :=
  Accordion.Formula.bigConj
    (((.letter default : WE.Word Γ V) :: (Formula.vars φ).map .var).map
        (fun w => walks w w ⋏ atRoot w w) ++
      φ.atoms.filterMap fun
        | .lenEq u v => some (walks u v)
        | .wordEq _ _ => none)

def normModel (m : Walk.Model Γ (Vars Γ V)) : Norm.Model Γ (ToNorm.Var V.Word) where
  σPath
    | .source x => m.σLoc (Loc.source x)
    | .inverse x => m.σPath (PathVar.inverse x)
    | .up => m.σPath PathVar.up

section

variable [Ord Γ]

def mkdir : GroundWord Γ → FileTree.Entries Γ (FileTree Γ) → FileTree.Entries Γ (FileTree Γ)
  | [], δ => δ
  | a :: w, δ =>
      δ.insert a (.dirc (mkdir w (match δ[a]? with
        | some (.dirc δ') => δ'
        | _ => ∅)))

def mkdirs (ws : List (GroundWord Γ)) : FileTree.Entries Γ (FileTree Γ) :=
  ws.foldr mkdir ∅

def HasDir : GroundWord Γ → FileTree.Entries Γ (FileTree Γ) → Prop
  | [], _ => True
  | a :: w, δ => ∃ δ', δ[a]? = some (.dirc δ') ∧ HasDir w δ'

end

def walkedWords [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) : List (GroundWord Γ) :=
  ([default] :: (Formula.vars φ).map m.σWord) ++
    φ.atoms.filterMap fun
      | .lenEq u _ => some (m.evalWord u)
      | .wordEq _ _ => none

def dirWords [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) : List (GroundWord Γ) :=
  walkedWords φ m ++ (walkedWords φ m).map (default :: ·)

end ToWalk

open ToWalk

def Model.toWalk [Ord Γ] [Inhabited Γ] (φ : Formula Γ V) (m : Model Γ V) :
    Walk.Model Γ (ToWalk.Vars Γ V) where
  σPath
    | .inverse x => ToNorm.parents (GroundWord.length (m.σWord x))
    | .up => ToNorm.parents 1
  σLoc
    | .source x => (m.σWord x : Accordion.Path Γ)
    | .endpoint u v =>
        (Path.descend (m.evalWord u) ++
          ToNorm.parents (GroundWord.length (m.evalWord v))).norm
    | .prefixed u v =>
        (Path.descend (default :: m.evalWord u) ++
          ToNorm.parents (GroundWord.length (m.evalWord v))).norm
  θ _ := .tree (.dirc (mkdirs (dirWords φ m)))

namespace Atom

def toWalk : Atom Γ V → Walk.Formula Γ (ToWalk.Vars Γ V)
  | .wordEq u v => liftWord u ≐ liftWord v
  | .lenEq u v => atRoot u v

end Atom

end LenEq

end WE

end Accordion

end
