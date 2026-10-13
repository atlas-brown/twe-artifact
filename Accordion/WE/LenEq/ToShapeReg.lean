module

public import Accordion.WE.LenEq.ToShapeReg.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula
open ToShapeReg

variable {Γ : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace Formula

def toShapeReg [Inhabited Γ] (φ : Formula Γ V) :
    ShapeReg.Formula (Alphabet Γ) (ToShapeReg.Vars V.Word) :=
  guards φ ⋏ φ.bind Atom.toShapeReg

@[grind =]
theorem toShapeReg_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [Inhabited Γ] (φ : Formula Γ V) :
    ShapeReg.Formula.SAT (toShapeReg φ) ↔ SAT φ :=
  guards_bind_toShapeReg_equisat φ

end Formula

end LenEq

end WE

end Accordion

end
