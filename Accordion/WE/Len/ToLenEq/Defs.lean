module

public import Accordion.WE.Len
public import Accordion.WE.LenEq

@[expose] public section

namespace Accordion

namespace WE

namespace Len

variable {Γ : Type} {V : WE.Vars}

namespace ToLenEq

abbrev Vars (V : WE.Vars) : WE.Vars where
  Letter := PEmpty
  Word := V.Letter ⊕ V.Word

def liftWord : WE.Word Γ V → WE.Word Γ (Vars V)
  | .empty => ε
  | .letter a => .letter a
  | .letterVar x => .var (.inl x)
  | .var x => .var (.inr x)
  | .concat u v => liftWord u ++ liftWord v

def sidePart (pos : Bool) (k : Int) (w : WE.Word Γ V) : WE.Word Γ V :=
  (List.replicate (bif pos then k else -k).toNat w).foldr (· ++ ·) ε

def sideWord [Inhabited Γ] (pos : Bool) (c₀ : Int) : List (LenTerm V.Word) → WE.Word Γ (Vars V)
  | [] => sidePart pos c₀ (.letter default)
  | t :: ts => sidePart (V := Vars V) pos t.c (.var (.inr t.x)) ++ sideWord pos c₀ ts

def guards [Inhabited Γ] (xs : List V.Letter) : LenEq.Formula Γ (Vars V) :=
  Accordion.Formula.bigConj (xs.map fun x => .atom (.lenEq (.var (.inl x)) (.letter default)))

def sourceModel [Inhabited Γ] (m : LenEq.Model Γ (Vars V)) : Model Γ V where
  σLetter x := (m.σWord (.inl x)).headD default
  σWord x := m.σWord (.inr x)

end ToLenEq

open ToLenEq

def Model.toLenEq (m : Model Γ V) : LenEq.Model Γ (ToLenEq.Vars V) where
  σLetter := PEmpty.elim
  σWord := Sum.elim (fun x => [m.σLetter x]) m.σWord

namespace Atom

def toLenEq [Inhabited Γ] : Atom Γ V → LenEq.Formula Γ (ToLenEq.Vars V)
  | .wordEq u v => .atom (.wordEq (liftWord u) (liftWord v))
  | .wordLength c =>
      .atom (.lenEq (sideWord true c.c₀ c.terms) (sideWord false c.c₀ c.terms))

end Atom

end Len

end WE

end Accordion

end
