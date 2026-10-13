module

public import Accordion.Formula

@[expose] public section

namespace Accordion

namespace WE

def Subst (X V : Type) := X → V

abbrev GroundWord (Γ : Type) := List Γ

namespace GroundWord

def length (w : GroundWord Γ) : Nat :=
  List.length w

end GroundWord

scoped macro:max atomic("|" noWs) w:term noWs "|" : term => `(GroundWord.length $w)

structure Vars where
  Letter : Type
  Word : Type

inductive Word (Γ : Type) (V : Vars) where
  | empty
  | letter (a : Γ)
  | letterVar (x : V.Letter)
  | var (x : V.Word)
  | concat (u v : Word Γ V)

instance {Γ : Type} {V : Vars} : Append (Word Γ V) := ⟨Word.concat⟩

attribute [coe] Word.letter Word.letterVar Word.var

instance {Γ : Type} {V : Vars} : Coe Γ (Word Γ V) := ⟨Word.letter⟩
instance {Γ : Type} {V : Vars} : Coe V.Letter (Word Γ V) := ⟨Word.letterVar⟩
instance {Γ : Type} {V : Vars} : Coe V.Word (Word Γ V) := ⟨Word.var⟩

scoped notation "ε" => Word.empty

inductive Atom (Γ : Type) (V : Vars) where
  | wordEq (u v : Word Γ V)

/-- A formula of word equations (§5). -/
abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

scoped notation:60 u:61 " ≐ " v:61 => Accordion.Formula.atom (Atom.wordEq u v)

structure Model (Γ : Type) (V : Vars) where
  σLetter : V.Letter → Γ
  σWord : V.Word → GroundWord Γ

variable {Γ : Type} {V : Vars}

namespace Word

def vars : Word Γ V → List V.Word
  | .empty => []
  | .letter _ => []
  | .letterVar _ => []
  | .var x => [x]
  | .concat u v => u.vars ++ v.vars

def letterVars : Word Γ V → List V.Letter
  | .empty => []
  | .letter _ => []
  | .letterVar x => [x]
  | .var _ => []
  | .concat u v => u.letterVars ++ v.letterVars

end Word

namespace Model

def evalWord (m : Model Γ V) : Word Γ V → GroundWord Γ
  | .empty => []
  | .letter a => [a]
  | .letterVar x => [m.σLetter x]
  | .var x => m.σWord x
  | .concat u v => m.evalWord u ++ m.evalWord v

def satAtom (m : Model Γ V) : Atom Γ V → Prop
  | .wordEq u v => m.evalWord u = m.evalWord v

instance : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

end Model

namespace Formula

def SAT (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m ⊨ φ

end Formula

end WE

end Accordion

end
