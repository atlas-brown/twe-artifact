module

public import Accordion.WE.LenEq.ToWalk.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula
open ToWalk

variable {Γ : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace Formula

def toWalk [Inhabited Γ] (φ : Formula Γ V) : Walk.Formula Γ (ToWalk.Vars Γ V) :=
  guards φ ⋏ φ.bind Atom.toWalk

@[grind =]
theorem toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [Inhabited Γ]
    (φ : Formula Γ V) : Walk.Formula.SAT (toWalk φ) ↔ SAT φ :=
  guards_bind_equisat φ

end Formula

end LenEq

end WE

end Accordion

end
